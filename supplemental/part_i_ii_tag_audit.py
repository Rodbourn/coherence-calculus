#!/usr/bin/env python3
r"""
Audit theorem-like manuscript items in Part I / Part II for local `\lean{...}`
tags.

This is intentionally a manuscript-hygiene audit, not a proof-surface audit.
It answers a different question from `active_part_coverage.py`:

- `active_part_coverage.py`: are existing `\lean{...}` references covered by the
  active Lean certification boundary?
- `part_i_ii_tag_audit.py`: which theorem-like manuscript items in Parts I / II
  still lack any nearby `\lean{...}` tag?

The script emits Markdown and JSON reports under `artifacts/`.
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
REPORT_MD = ARTIFACTS / "part_i_ii_tag_audit.md"
REPORT_JSON = ARTIFACTS / "part_i_ii_tag_audit.json"

PART_RE = re.compile(r"""(?:\\part\*\{|\\manuscriptpart\{)(Part [IVX]+):""")
CHAPTER_RE = re.compile(r"""\\manuscriptchapter\{([^}]*)\}\{([^}]*)\}""")
INPUT_RE = re.compile(r"""\\input\{sections/([^}]+)\}""")
LABEL_RE = re.compile(r"""\\label\{([^}]*)\}""")
LEAN_RE = re.compile(r"""\\lean\{([^}]*)\}""")
NEWTHEOREM_RE = re.compile(r"""\\newtheorem\{([^}]+)\}""")


@dataclass(frozen=True)
class SectionInfo:
    part: str
    chapter_number: str
    chapter_title: str
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


def parse_part_sections() -> list[SectionInfo]:
    current_part = ""
    current_chapter_number = ""
    current_chapter_title = ""
    sections: list[SectionInfo] = []

    for line in HBC_TEX.read_text(encoding="utf-8").splitlines():
        part_match = PART_RE.search(line)
        if part_match:
            part_name = part_match.group(1)
            current_part = part_name if part_name in {"Part I", "Part II"} else ""
            continue

        chapter_match = CHAPTER_RE.search(line)
        if chapter_match and current_part:
            current_chapter_number = chapter_match.group(1)
            current_chapter_title = chapter_match.group(2)
            continue

        if not current_part:
            continue

        input_match = INPUT_RE.search(line)
        if input_match:
            section_name = input_match.group(1)
            sections.append(
                SectionInfo(
                    part=current_part,
                    chapter_number=current_chapter_number,
                    chapter_title=current_chapter_title,
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
    sections = parse_part_sections()
    section_rows: list[dict[str, object]] = []
    total_counter: Counter[str] = Counter()

    for section in sections:
        items = extract_items(section)
        counts = Counter()
        counts["items"] = len(items)
        for item in items:
            counts["tagged" if item.tagged else "missing"] += 1
            counts[f"env_{item.env_type}"] += 1

        total_counter.update(counts)
        section_rows.append(
            {
                "part": section.part,
                "chapter_number": section.chapter_number,
                "chapter_title": section.chapter_title,
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
        "summary": {
            "sections": len(section_rows),
            "items": total_counter["items"],
            "tagged": total_counter["tagged"],
            "missing": total_counter["missing"],
        },
        "sections_detail": section_rows,
    }


def write_markdown(report: dict[str, object]) -> None:
    summary = report["summary"]
    lines: list[str] = []
    lines.append("# Part I / Part II Tag Audit")
    lines.append("")
    lines.append("This report checks formal manuscript items in Part I / Part II")
    lines.append("for nearby `\\lean{...}` tags.")
    lines.append("")
    lines.append(f"- Manuscript root: `{report['manuscript_root']}`")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    lines.append(f"- Section files scanned: {summary['sections']}")
    lines.append(f"- Formal items scanned: {summary['items']}")
    lines.append(f"- Tagged: {summary['tagged']}")
    lines.append(f"- Missing tag: {summary['missing']}")
    lines.append("")
    lines.append("## Section Summary")
    lines.append("")
    lines.append("| Part | Chapter | Section | Items | Tagged | Missing |")
    lines.append("| --- | --- | --- | ---: | ---: | ---: |")

    for section in report["sections_detail"]:
        counts = Counter(section["counts"])
        lines.append(
            f"| {section['part']} | {section['chapter_number']} {section['chapter_title']} | "
            f"`{section['section']}` | {counts['items']} | {counts['tagged']} | {counts['missing']} |"
        )

    lines.append("")
    lines.append("## Missing Tags")
    lines.append("")

    for section in report["sections_detail"]:
        missing = [item for item in section["items"] if not item["tagged"]]
        if not missing:
            continue
        lines.append(f"### `{section['section']}`")
        lines.append("")
        lines.append(
            f"`{section['part']}`, Chapter {section['chapter_number']} ({section['chapter_title']}); "
            f"source `{section['tex_path']}`"
        )
        lines.append("")
        for item in missing:
            label_suffix = f" `{item['label']}`" if item["label"] else ""
            lines.append(
                f"- line {item['line_number']}: `{item['env_type']}`{label_suffix}"
            )
        lines.append("")

    REPORT_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")


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
