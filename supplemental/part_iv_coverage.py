#!/usr/bin/env python3
"""
Audit the Part IV manuscript surface against the separate Part IV Lean root.
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
LEAN_ROOT = PROJECT_ROOT / "CoherenceCalculus" / "CoherenceCalculus" / "PartIV.lean"
STRICT_AUDIT = PROJECT_ROOT / "CoherenceCalculus" / "part4_axiom_check.lean"
OTHER_STRICT_AUDITS = [
    PROJECT_ROOT / "CoherenceCalculus" / "active_axiom_check.lean",
    PROJECT_ROOT / "CoherenceCalculus" / "active_bedrock_axiom_check.lean",
    PROJECT_ROOT / "CoherenceCalculus" / "part3_axiom_check.lean",
    PROJECT_ROOT / "CoherenceCalculus" / "part3_derived_axiom_check.lean",
    PROJECT_ROOT / "CoherenceCalculus" / "appendix_operators_axiom_check.lean",
    PROJECT_ROOT / "CoherenceCalculus" / "appendix_horizons_axiom_check.lean",
]
LEAN_SRC = PROJECT_ROOT / "CoherenceCalculus" / "CoherenceCalculus"
PART4_SRC = LEAN_SRC / "PartIV"
ARTIFACTS = PROJECT_ROOT / "artifacts"
REPORT_MD = ARTIFACTS / "part_iv_coverage.md"
REPORT_JSON = ARTIFACTS / "part_iv_coverage.json"

PART_RE = re.compile(r"""(?:\\part\*\{|\\manuscriptpart\{)(Part [IVX]+):""")
CHAPTER_RE = re.compile(r"""\\manuscriptchapter\{([^}]*)\}\{([^}]*)\}""")
INPUT_RE = re.compile(r"""\\input\{sections/([^}]+)\}""")
LEAN_TAG_RE = re.compile(r"""\\lean\{([^}]*)\}""")
AUDIT_RE = re.compile(r"""#print axioms ([A-Za-z0-9_'.]+)""")
NAMESPACE_RE = re.compile(r"""^\s*namespace\s+([A-Za-z0-9_'.]+)\s*$""")
END_RE = re.compile(r"""^\s*end\s+([A-Za-z0-9_'.]+)\s*$""")
APPENDIX_PART_RE = re.compile(r"""\\manuscriptpart\{Appendices\}""")
DECL_RE = re.compile(
    r"""^\s*(?:protected\s+)?(?:noncomputable\s+)?"""
    r"""(?:abbrev|axiom|class|def|inductive|instance|lemma|structure|theorem)\s+"""
    r"""([A-Za-z0-9_'.]+)"""
)


@dataclass(frozen=True)
class SectionInfo:
    part: str
    chapter_number: str
    chapter_title: str
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


def parse_part_sections() -> dict[str, SectionInfo]:
    current_part = ""
    current_chapter_number = ""
    current_chapter_title = ""
    sections: dict[str, SectionInfo] = {}

    for line in HBC_TEX.read_text(encoding="utf-8").splitlines():
        if APPENDIX_PART_RE.search(line) or line.strip() == r"\appendix":
            current_part = ""
            continue

        part_match = PART_RE.search(line)
        if part_match:
            current_part = part_match.group(1) if part_match.group(1) == "Part IV" else ""
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
            sections[section_name] = SectionInfo(
                part=current_part,
                chapter_number=current_chapter_number,
                chapter_title=current_chapter_title,
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
    other_strict_audited: set[str],
    part4_defs: dict[str, dict[str, str]],
    all_defs: dict[str, dict[str, str]],
) -> tuple[str, str, str]:
    for full_name in candidate_names(display_name):
        if full_name in strict_audited:
            info = part4_defs.get(full_name, all_defs.get(full_name, {}))
            return "audited_strict", full_name, info.get("owner", "")
    for full_name in candidate_names(display_name):
        if full_name in part4_defs:
            return "part4_root_unaudited", full_name, part4_defs[full_name]["owner"]
    for full_name in candidate_names(display_name):
        if full_name in other_strict_audited:
            info = all_defs.get(full_name, {})
            return "audited_other_lane", full_name, info.get("owner", "")
    for full_name in candidate_names(display_name):
        if full_name in all_defs:
            return "outside_part4_root", full_name, all_defs[full_name]["owner"]
    candidates = candidate_names(display_name)
    return "missing", (candidates[0] if candidates else display_name), ""


def build_report() -> dict[str, object]:
    sections = parse_part_sections()
    strict_audited = parse_audited_names(STRICT_AUDIT)
    other_strict_audited: set[str] = set()
    for path in OTHER_STRICT_AUDITS:
        other_strict_audited |= parse_audited_names(path)
    part4_files = [LEAN_ROOT] + sorted(PART4_SRC.rglob("*.lean"))
    part4_defs = parse_declarations(part4_files)
    all_defs = parse_declarations(sorted(LEAN_SRC.rglob("*.lean")))

    overall_names: dict[str, dict[str, object]] = {}
    section_rows: list[dict[str, object]] = []

    for section_name, info in sections.items():
        refs = extract_section_refs(info)
        per_name: dict[str, dict[str, object]] = {}

        for ref in refs:
            status, full_name, owner = classify_name(
                ref.display_name, strict_audited, other_strict_audited, part4_defs, all_defs
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
                "part": info.part,
                "chapter_number": info.chapter_number,
                "chapter_title": info.chapter_title,
                "tex_path": str(info.tex_path.relative_to(PROJECT_ROOT)),
                "counts": dict(counts),
                "items": sorted(per_name.values(), key=lambda item: item["first_line"]),
            }
        )

    overall_counts = Counter(item["status"] for item in overall_names.values())
    return {
        "manuscript_root": str(HBC_TEX.relative_to(PROJECT_ROOT)),
        "lean_root": str(LEAN_ROOT.relative_to(PROJECT_ROOT)),
        "strict_audit_surface": str(STRICT_AUDIT.relative_to(PROJECT_ROOT)),
        "other_strict_audit_surfaces": [
            str(path.relative_to(PROJECT_ROOT))
            for path in OTHER_STRICT_AUDITS
        ],
        "summary": {
            "sections": len(section_rows),
            "references": len(overall_names),
            "audited_strict": overall_counts["audited_strict"],
            "audited_other_lane": overall_counts["audited_other_lane"],
            "part4_root_unaudited": overall_counts["part4_root_unaudited"],
            "outside_part4_root": overall_counts["outside_part4_root"],
            "missing": overall_counts["missing"],
        },
        "sections_detail": section_rows,
    }


def write_markdown(report: dict[str, object]) -> None:
    summary = report["summary"]
    lines: list[str] = []
    lines.append("# Part IV Coverage Audit")
    lines.append("")
    lines.append("This report compares the current Part IV manuscript surface to the")
    lines.append("separate Part IV Lean certification boundary and records when the")
    lines.append("current manuscript instead lands on another strict audited lane.")
    lines.append("")
    lines.append("Certification boundary used:")
    lines.append(f"- Manuscript root: `{report['manuscript_root']}`")
    lines.append(f"- Part IV Lean root: `{report['lean_root']}`")
    lines.append(f"- Strict no-axioms audit surface: `{report['strict_audit_surface']}`")
    lines.append("- Other strict audit surfaces checked for cross-lane certification:")
    for path in report["other_strict_audit_surfaces"]:
        lines.append(f"  - `{path}`")
    lines.append("")
    lines.append("Status meanings:")
    lines.append("- `audited_strict`: referenced from the manuscript and present on the strict Part IV `#print axioms` audit surface")
    lines.append("- `audited_other_lane`: referenced from the Part IV manuscript surface, but certified on another strict audited lane rather than in `PartIV.lean`")
    lines.append("- `part4_root_unaudited`: defined in the Part IV root but not yet on the Part IV audit surface")
    lines.append("- `outside_part4_root`: defined somewhere in the repository, but not in the Part IV root")
    lines.append("- `missing`: no matching declaration found in `CoherenceCalculus/CoherenceCalculus/*.lean`")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    lines.append(f"- Part IV section files scanned: {summary['sections']}")
    lines.append(f"- Unique Lean references in Part IV: {summary['references']}")
    lines.append(f"- `audited_strict`: {summary['audited_strict']}")
    lines.append(f"- `audited_other_lane`: {summary['audited_other_lane']}")
    lines.append(f"- `part4_root_unaudited`: {summary['part4_root_unaudited']}")
    lines.append(f"- `outside_part4_root`: {summary['outside_part4_root']}")
    lines.append(f"- `missing`: {summary['missing']}")
    lines.append("")
    lines.append("## Section Summary")
    lines.append("")
    lines.append("| Part | Chapter | Section | Refs | Strict | Other Lane | Root Unaudited | Outside Root | Missing |")
    lines.append("| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |")
    for section in report["sections_detail"]:
        counts = Counter(section["counts"])
        lines.append(
            f"| {section['part']} | {section['chapter_number']} {section['chapter_title']} | "
            f"`{section['section']}` | {sum(counts.values())} | {counts['audited_strict']} | "
            f"{counts['audited_other_lane']} | {counts['part4_root_unaudited']} | "
            f"{counts['outside_part4_root']} | {counts['missing']} |"
        )

    lines.append("")
    lines.append("## Boundary And Gap Details")
    lines.append("")
    for section in report["sections_detail"]:
        gaps = [item for item in section["items"] if item["status"] != "audited_strict"]
        if not gaps:
            continue
        lines.append(f"### `{section['section']}`")
        lines.append("")
        lines.append(
            f"`{section['part']}`, Chapter {section['chapter_number']} ({section['chapter_title']}); "
            f"source `{section['tex_path']}`"
        )
        lines.append("")
        for status in ("audited_other_lane", "part4_root_unaudited", "outside_part4_root", "missing"):
            items = [item for item in gaps if item["status"] == status]
            if not items:
                continue
            lines.append(f"{status}:")
            for item in items:
                owner = f" -> `{item['owner']}`" if item["owner"] else ""
                lines.append(
                    f"- line {item['first_line']}: `{item['display_name']}` -> "
                    f"`{item['full_name']}`{owner}"
                )
            lines.append("")

    REPORT_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    report = build_report()
    REPORT_JSON.write_text(json.dumps(report, indent=2), encoding="utf-8")
    write_markdown(report)
    summary = report["summary"]
    print(f"wrote {REPORT_JSON.relative_to(PROJECT_ROOT)}")
    print(
        "summary:",
        f"{summary['references']} refs,",
        f"{summary['audited_strict']} strict,",
        f"{summary['audited_other_lane']} other-lane,",
        f"{summary['part4_root_unaudited']} root-unaudited,",
        f"{summary['outside_part4_root']} outside-root,",
        f"{summary['missing']} missing",
    )


if __name__ == "__main__":
    main()
