#!/usr/bin/env python3
"""
Audit the operator-side appendices against the detached AppendixOperators Lean root.
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
LEAN_ROOT = PROJECT_ROOT / "CoherenceCalculus" / "CoherenceCalculus" / "AppendixOperators.lean"
STRICT_AUDIT = PROJECT_ROOT / "CoherenceCalculus" / "appendix_operators_axiom_check.lean"
LEAN_SRC = PROJECT_ROOT / "CoherenceCalculus" / "CoherenceCalculus"
ARTIFACTS = PROJECT_ROOT / "artifacts"
REPORT_JSON = ARTIFACTS / "appendix_operators_coverage.json"

SECTION_NAMES = {
    "advanced_operators",
    "advanced_operators_ii",
    "advanced_operators_iii",
    "advanced_operators_iv",
    "boundary",
}

INPUT_RE = re.compile(r"""\\input\{sections/([^}]+)\}""")
LEAN_TAG_RE = re.compile(r"""\\lean\{([^}]*)\}""")
AUDIT_RE = re.compile(r"""#print axioms ([A-Za-z0-9_'.]+)""")
NAMESPACE_RE = re.compile(r"""^\s*namespace\s+([A-Za-z0-9_'.]+)\s*$""")
END_RE = re.compile(r"""^\s*end\s+([A-Za-z0-9_'.]+)\s*$""")
DECL_RE = re.compile(
    r"""^\s*(?:protected\s+)?(?:noncomputable\s+)?"""
    r"""(?:abbrev|axiom|class|def|inductive|instance|lemma|structure|theorem)\s+"""
    r"""([A-Za-z0-9_'.]+)"""
)


@dataclass(frozen=True)
class SectionInfo:
    tex_path: Path


@dataclass(frozen=True)
class RefOccurrence:
    display_name: str
    line_number: int


def strip_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    block_depth = 0
    while i < len(text):
        if block_depth == 0 and text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                i += 1
            continue
        if text.startswith("/-", i):
            block_depth += 1
            i += 2
            continue
        if block_depth > 0 and text.startswith("-/", i):
            block_depth -= 1
            i += 2
            continue
        if block_depth == 0:
            out.append(text[i])
        elif text[i] == "\n":
            out.append("\n")
        i += 1
    return "".join(out)


def normalize_name(name: str) -> str:
    name = name.strip()
    if not name:
        return name
    if name.startswith("CoherenceCalculus."):
        return name
    return f"CoherenceCalculus.{name}"


def candidate_names(name: str) -> list[str]:
    name = name.strip()
    if not name:
        return []
    if name.startswith("CoherenceCalculus."):
        return [name]
    if "." in name:
        return [name, normalize_name(name)]
    return [normalize_name(name), name]


def qualify_name(namespace_stack: list[str], raw_name: str) -> str:
    if raw_name.startswith("CoherenceCalculus."):
        return raw_name
    if namespace_stack:
        return ".".join(namespace_stack + [raw_name])
    return raw_name


def parse_sections() -> dict[str, SectionInfo]:
    sections: dict[str, SectionInfo] = {}
    for line in HBC_TEX.read_text(encoding="utf-8").splitlines():
        input_match = INPUT_RE.search(line)
        if not input_match:
            continue
        section_name = input_match.group(1)
        if section_name not in SECTION_NAMES:
            continue
        sections[section_name] = SectionInfo(
            tex_path=MONOGRAPH_DIR / "sections" / f"{section_name}.tex",
        )
    return sections


def extract_section_refs(section: SectionInfo) -> list[RefOccurrence]:
    refs: list[RefOccurrence] = []
    for line_number, line in enumerate(section.tex_path.read_text(encoding="utf-8").splitlines(), start=1):
        for match in LEAN_TAG_RE.finditer(line):
            raw = match.group(1)
            for piece in raw.split(","):
                display = piece.strip()
                if display:
                    refs.append(RefOccurrence(display_name=display, line_number=line_number))
    return refs


def parse_audited_names(path: Path) -> set[str]:
    return {match.group(1).strip() for match in AUDIT_RE.finditer(path.read_text(encoding="utf-8"))}


def parse_declarations(paths: list[Path]) -> dict[str, dict[str, str]]:
    owner: dict[str, dict[str, str]] = {}
    for path in paths:
        namespace_stack: list[str] = []
        content = strip_comments(path.read_text(encoding="utf-8"))
        for line in content.splitlines():
            namespace_match = NAMESPACE_RE.match(line)
            if namespace_match:
                namespace_stack.append(namespace_match.group(1))
                continue

            end_match = END_RE.match(line)
            if end_match:
                if namespace_stack and namespace_stack[-1] == end_match.group(1):
                    namespace_stack.pop()
                continue

            decl_match = DECL_RE.match(line)
            if not decl_match:
                continue

            full_name = qualify_name(namespace_stack, decl_match.group(1))
            owner.setdefault(
                full_name,
                {
                    "owner": str(path.relative_to(PROJECT_ROOT)),
                    "decl_type": line.strip().split()[0],
                },
            )
    return owner


def classify_name(
    display_name: str,
    strict_audited: set[str],
    appendix_defs: dict[str, dict[str, str]],
    all_defs: dict[str, dict[str, str]],
) -> tuple[str, str, str]:
    for full_name in candidate_names(display_name):
        if full_name in strict_audited:
            info = appendix_defs.get(full_name, all_defs.get(full_name, {}))
            return "audited_strict", full_name, info.get("owner", "")
    for full_name in candidate_names(display_name):
        if full_name in appendix_defs:
            return "appendix_root_unaudited", full_name, appendix_defs[full_name]["owner"]
    for full_name in candidate_names(display_name):
        if full_name in all_defs:
            return "outside_appendix_root", full_name, all_defs[full_name]["owner"]
    candidates = candidate_names(display_name)
    return "missing", (candidates[0] if candidates else display_name), ""


def build_report() -> dict[str, object]:
    sections = parse_sections()
    strict_audited = parse_audited_names(STRICT_AUDIT)
    appendix_defs = parse_declarations([LEAN_ROOT])
    all_defs = parse_declarations(sorted(LEAN_SRC.rglob("*.lean")))

    overall_names: dict[str, dict[str, object]] = {}
    section_rows: list[dict[str, object]] = []

    for section_name, info in sections.items():
        refs = extract_section_refs(info)
        per_name: dict[str, dict[str, object]] = {}

        for ref in refs:
            status, full_name, owner = classify_name(
                ref.display_name, strict_audited, appendix_defs, all_defs
            )
            current = per_name.get(full_name)
            if current is None:
                per_name[full_name] = {
                    "display_name": ref.display_name,
                    "full_name": full_name,
                    "status": status,
                    "owner": owner,
                    "first_line": ref.line_number,
                }
            else:
                current["first_line"] = min(current["first_line"], ref.line_number)

            overall_names.setdefault(
                full_name,
                {
                    "display_name": ref.display_name,
                    "full_name": full_name,
                    "status": status,
                    "owner": owner,
                },
            )

        counts = Counter(item["status"] for item in per_name.values())
        section_rows.append(
            {
                "section": section_name,
                "tex_path": str(info.tex_path.relative_to(PROJECT_ROOT)),
                "counts": dict(counts),
                "refs": sorted(per_name.values(), key=lambda item: item["display_name"]),
            }
        )

    overall_counts = Counter(item["status"] for item in overall_names.values())
    return {
        "manuscript_surface": {
            "main_tex": str(HBC_TEX.relative_to(PROJECT_ROOT)),
            "lean_root": str(LEAN_ROOT.relative_to(PROJECT_ROOT)),
            "strict_audit": str(STRICT_AUDIT.relative_to(PROJECT_ROOT)),
        },
        "lane": "appendix_operators",
        "summary": {
            "sections": len(section_rows),
            "references": len(overall_names),
            "audited_strict": overall_counts["audited_strict"],
            "appendix_root_unaudited": overall_counts["appendix_root_unaudited"],
            "outside_appendix_root": overall_counts["outside_appendix_root"],
            "missing": overall_counts["missing"],
        },
        "sections": section_rows,
    }


def main() -> None:
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    report = build_report()
    REPORT_JSON.write_text(json.dumps(report, indent=2), encoding="utf-8")
    summary = report["summary"]
    print(f"wrote {REPORT_JSON.relative_to(PROJECT_ROOT)}")
    print(
        "summary:",
        f"{summary['references']} refs,",
        f"{summary['audited_strict']} strict,",
        f"{summary['appendix_root_unaudited']} appendix-root unaudited,",
        f"{summary['outside_appendix_root']} outside-root,",
        f"{summary['missing']} missing",
    )


if __name__ == "__main__":
    main()
