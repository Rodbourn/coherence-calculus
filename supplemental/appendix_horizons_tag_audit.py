#!/usr/bin/env python3
r"""
Audit formal manuscript items in the horizon/spectral appendices for local `\lean{...}` tags.
"""

from __future__ import annotations

import json
import re
from collections import Counter
from dataclasses import dataclass
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
MONOGRAPH_DIR = PROJECT_ROOT / "manuscripts" / "monograph"
HBC_TEX = MONOGRAPH_DIR / "hbc.tex"
ARTIFACTS = PROJECT_ROOT / "artifacts"
REPORT_JSON = ARTIFACTS / "appendix_horizons_tag_audit.json"

SECTION_NAMES = {
    "appendix_oblique_horizons",
    "appendix_continuous_spectral_horizons",
    "appendix_trace_level_coherence_laws",
}

INPUT_RE = re.compile(r"""\\input\{sections/([^}]+)\}""")
LABEL_RE = re.compile(r"""\\label\{([^}]*)\}""")
LEAN_RE = re.compile(r"""\\lean\{([^}]*)\}""")
NEWTHEOREM_RE = re.compile(r"""\\newtheorem\{([^}]+)\}""")


@dataclass(frozen=True)
class SectionInfo:
    section_name: str
    tex_path: Path


@dataclass(frozen=True)
class ItemInfo:
    env_type: str
    line_number: int
    label: str
    tagged: bool
    lean_tag: str


def formal_env_re() -> re.Pattern[str]:
    env_names = NEWTHEOREM_RE.findall(HBC_TEX.read_text(encoding="utf-8"))
    if not env_names:
        raise RuntimeError(f"no formal environments found in {HBC_TEX}")
    env_pattern = "|".join(re.escape(name) for name in env_names)
    return re.compile(r"""\\begin\{(""" + env_pattern + r""")\}""")


def parse_sections() -> list[SectionInfo]:
    sections: list[SectionInfo] = []
    for line in HBC_TEX.read_text(encoding="utf-8").splitlines():
        input_match = INPUT_RE.search(line)
        if not input_match:
            continue
        section_name = input_match.group(1)
        if section_name not in SECTION_NAMES:
            continue
        sections.append(
            SectionInfo(
                section_name=section_name,
                tex_path=MONOGRAPH_DIR / "sections" / f"{section_name}.tex",
            )
        )
    return sections


def extract_items(section: SectionInfo) -> list[ItemInfo]:
    lines = section.tex_path.read_text(encoding="utf-8").splitlines()
    items: list[ItemInfo] = []
    env_re = formal_env_re()

    for i, line in enumerate(lines):
        env_match = env_re.search(line)
        if not env_match:
            continue

        window = "\n".join(lines[i : i + 6])
        lean_match = LEAN_RE.search(window)
        label_match = LABEL_RE.search(window)

        items.append(
            ItemInfo(
                env_type=env_match.group(1),
                line_number=i + 1,
                label=label_match.group(1) if label_match else "",
                tagged=lean_match is not None,
                lean_tag=lean_match.group(1).strip() if lean_match else "",
            )
        )

    return items


def build_report() -> dict[str, object]:
    sections = parse_sections()
    section_rows: list[dict[str, object]] = []
    total_counter: Counter[str] = Counter()

    for section in sections:
        items = extract_items(section)
        counts = Counter()
        counts["items"] = len(items)
        for item in items:
            counts["tagged" if item.tagged else "missing"] += 1

        total_counter.update(counts)
        section_rows.append(
            {
                "section": section.section_name,
                "tex_path": str(section.tex_path.relative_to(PROJECT_ROOT)),
                "counts": dict(counts),
                "items": [
                    {
                        "env_type": item.env_type,
                        "line_number": item.line_number,
                        "label": item.label,
                        "tagged": item.tagged,
                        "lean_tag": item.lean_tag,
                    }
                    for item in items
                ],
            }
        )

    return {
        "manuscript_root": str(HBC_TEX.relative_to(PROJECT_ROOT)),
        "lane": "appendix_horizons",
        "summary": {
            "sections": len(section_rows),
            "items": total_counter["items"],
            "tagged": total_counter["tagged"],
            "missing": total_counter["missing"],
        },
        "sections_detail": section_rows,
    }


def main() -> None:
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    report = build_report()
    REPORT_JSON.write_text(json.dumps(report, indent=2), encoding="utf-8")
    summary = report["summary"]
    print(f"wrote {REPORT_JSON.relative_to(PROJECT_ROOT)}")
    print(
        "summary:",
        f"{summary['items']} formal items,",
        f"{summary['tagged']} tagged,",
        f"{summary['missing']} missing",
    )


if __name__ == "__main__":
    main()
