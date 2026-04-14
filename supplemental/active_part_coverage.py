#!/usr/bin/env python3
"""
Audit the current Part I / Part II manuscript surface against the active Lean
certification boundary.

The script treats:
- manuscript surface: Part I / Part II section inputs from
  `manuscripts/monograph/hbc.tex`
- active Lean root: `CoherenceCalculus/CoherenceCalculus.lean` ->
  `CoherenceCalculus/CoherenceCalculus/Foundation.lean`
- strict no-axioms audit surface: `CoherenceCalculus/active_axiom_check.lean`
- bedrock-only audit surface: `CoherenceCalculus/active_bedrock_axiom_check.lean`

It emits a Markdown report and a JSON summary under `artifacts/`.
"""

from __future__ import annotations

import json
import re
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
MONOGRAPH_DIR = PROJECT_ROOT / "manuscripts" / "monograph"
HBC_TEX = MONOGRAPH_DIR / "hbc.tex"
LEAN_ROOT = PROJECT_ROOT / "CoherenceCalculus" / "CoherenceCalculus.lean"
FOUNDATION_ROOT = PROJECT_ROOT / "CoherenceCalculus" / "CoherenceCalculus" / "Foundation.lean"
STRICT_AUDIT = PROJECT_ROOT / "CoherenceCalculus" / "active_axiom_check.lean"
BEDROCK_AUDIT = PROJECT_ROOT / "CoherenceCalculus" / "active_bedrock_axiom_check.lean"
LEAN_SRC = PROJECT_ROOT / "CoherenceCalculus" / "CoherenceCalculus"
ARTIFACTS = PROJECT_ROOT / "artifacts"
REPORT_MD = ARTIFACTS / "active_part_i_ii_coverage.md"
REPORT_JSON = ARTIFACTS / "active_part_i_ii_coverage.json"

PART_RE = re.compile(r"""(?:\\part\*\{|\\manuscriptpart\{)(Part [IVX]+):""")
CHAPTER_RE = re.compile(r"""\\manuscriptchapter\{([^}]*)\}\{([^}]*)\}""")
INPUT_RE = re.compile(r"""\\input\{sections/([^}]+)\}""")
LEAN_TAG_RE = re.compile(r"""\\lean\{([^}]*)\}""")
AUDIT_RE = re.compile(r"""#print axioms ([A-Za-z0-9_'.]+)""")
IMPORT_RE = re.compile(r"""^\s*import CoherenceCalculus\.Foundation(?:\.([A-Za-z0-9_'.]+))?\s*$""")
NAMESPACE_RE = re.compile(r"""^\s*namespace\s+([A-Za-z0-9_'.]+)\s*$""")
END_RE = re.compile(r"""^\s*end\s+([A-Za-z0-9_'.]+)\s*$""")
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
    """Remove Lean line and block comments while keeping line structure."""
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
                if not display:
                    continue
                refs.append(
                    RefOccurrence(
                        display_name=display,
                        line_number=line_number,
                    )
                )
    return refs


def parse_audited_names(path: Path) -> set[str]:
    return {
        match.group(1).strip()
        for match in AUDIT_RE.finditer(path.read_text(encoding="utf-8"))
    }


def imported_foundation_paths(path: Path) -> list[Path]:
    imports: list[Path] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = IMPORT_RE.match(line)
        if not match:
            continue
        module_name = match.group(1)
        if not module_name:
            imports.append(FOUNDATION_ROOT)
            continue
        imports.append(LEAN_SRC / "Foundation" / f"{module_name}.lean")
    return imports


def active_foundation_files() -> list[Path]:
    seen: set[Path] = set()
    ordered: list[Path] = []
    pending = [FOUNDATION_ROOT]

    while pending:
        path = pending.pop()
        if path in seen or not path.exists():
            continue
        seen.add(path)
        ordered.append(path)
        pending.extend(imported_foundation_paths(path))

    return sorted(ordered)


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
                end_name = end_match.group(1)
                if namespace_stack and namespace_stack[-1] == end_name:
                    namespace_stack.pop()
                continue

            decl_match = DECL_RE.match(line)
            if not decl_match:
                continue

            raw_name = decl_match.group(1)
            full_name = qualify_name(namespace_stack, raw_name)
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
    bedrock_audited: set[str],
    active_defs: dict[str, dict[str, str]],
    all_defs: dict[str, dict[str, str]],
) -> tuple[str, str, str]:
    for full_name in candidate_names(display_name):
        if full_name in strict_audited:
            info = active_defs.get(full_name, all_defs.get(full_name, {}))
            return "audited_strict", full_name, info.get("owner", "")
    for full_name in candidate_names(display_name):
        if full_name in bedrock_audited:
            info = active_defs.get(full_name, all_defs.get(full_name, {}))
            return "audited_bedrock", full_name, info.get("owner", "")
    for full_name in candidate_names(display_name):
        if full_name in active_defs:
            info = active_defs[full_name]
            if info["owner"].endswith("AxiomCore.lean"):
                return "active_bedrock_decl", full_name, info["owner"]
            return "active_root_unaudited", full_name, info["owner"]
    for full_name in candidate_names(display_name):
        if full_name in all_defs:
            return "outside_active_root", full_name, all_defs[full_name]["owner"]
    candidates = candidate_names(display_name)
    fallback = candidates[0] if candidates else display_name
    return "missing", fallback, ""


def build_report() -> dict[str, object]:
    sections = parse_part_sections()
    strict_audited = parse_audited_names(STRICT_AUDIT)
    bedrock_audited = parse_audited_names(BEDROCK_AUDIT)

    active_files = active_foundation_files()
    active_defs = parse_declarations(active_files)
    all_defs = parse_declarations(sorted(LEAN_SRC.rglob("*.lean")))

    overall_names: dict[str, dict[str, object]] = {}
    section_rows: list[dict[str, object]] = []

    for section_name, info in sections.items():
        refs = extract_section_refs(info)
        per_name: dict[str, dict[str, object]] = {}
        for ref in refs:
            status, full_name, owner = classify_name(
                ref.display_name,
                strict_audited,
                bedrock_audited,
                active_defs,
                all_defs,
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
                "refs": sorted(per_name.values(), key=lambda item: item["full_name"]),
            }
        )

    overall_counts = Counter(item["status"] for item in overall_names.values())
    return {
        "manuscript_surface": {
            "main_tex": str(HBC_TEX.relative_to(PROJECT_ROOT)),
            "lean_root": str(LEAN_ROOT.relative_to(PROJECT_ROOT)),
            "foundation_root": str(FOUNDATION_ROOT.relative_to(PROJECT_ROOT)),
            "strict_audit": str(STRICT_AUDIT.relative_to(PROJECT_ROOT)),
            "bedrock_audit": str(BEDROCK_AUDIT.relative_to(PROJECT_ROOT)),
        },
        "summary": {
            "part_i_ii_sections": len(section_rows),
            "unique_lean_refs": len(overall_names),
            "audited_strict": overall_counts["audited_strict"],
            "audited_bedrock": overall_counts["audited_bedrock"],
            "active_bedrock_decl": overall_counts["active_bedrock_decl"],
            "active_root_unaudited": overall_counts["active_root_unaudited"],
            "outside_active_root": overall_counts["outside_active_root"],
            "missing": overall_counts["missing"],
        },
        "sections": section_rows,
        "overall_refs": sorted(overall_names.values(), key=lambda item: item["full_name"]),
    }


def write_markdown(report: dict[str, object]) -> None:
    summary = report["summary"]
    lines: list[str] = []
    lines.append("# Active Part I / Part II Coverage Audit")
    lines.append("")
    lines.append("This report compares the current Part I / Part II manuscript surface to the")
    lines.append("active Lean certification boundary.")
    lines.append("")
    lines.append("Certification boundary used:")
    lines.append(f"- Manuscript root: `{report['manuscript_surface']['main_tex']}`")
    lines.append(f"- Active Lean root: `{report['manuscript_surface']['lean_root']}`")
    lines.append(f"- Active foundation chain: `{report['manuscript_surface']['foundation_root']}`")
    lines.append(f"- Strict no-axioms audit surface: `{report['manuscript_surface']['strict_audit']}`")
    lines.append(f"- Bedrock-only audit surface: `{report['manuscript_surface']['bedrock_audit']}`")
    lines.append("")
    lines.append("Status meanings:")
    lines.append("- `audited_strict`: referenced from the manuscript and present on the strict `#print axioms` audit surface")
    lines.append("- `audited_bedrock`: referenced from the manuscript and present on the bedrock-only audit surface")
    lines.append("- `active_bedrock_decl`: referenced directly from the active bedrock declarations in `Foundation/AxiomCore.lean`")
    lines.append("- `active_root_unaudited`: defined in the active foundation chain but not yet on the active audit surface")
    lines.append("- `outside_active_root`: defined somewhere in the repository, but not in the active foundation chain")
    lines.append("- `missing`: no matching declaration found in `CoherenceCalculus/CoherenceCalculus/*.lean`")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    lines.append(f"- Part I / Part II section files scanned: {summary['part_i_ii_sections']}")
    lines.append(f"- Unique Lean references in Part I / Part II: {summary['unique_lean_refs']}")
    lines.append(f"- `audited_strict`: {summary['audited_strict']}")
    lines.append(f"- `audited_bedrock`: {summary['audited_bedrock']}")
    lines.append(f"- `active_bedrock_decl`: {summary['active_bedrock_decl']}")
    lines.append(f"- `active_root_unaudited`: {summary['active_root_unaudited']}")
    lines.append(f"- `outside_active_root`: {summary['outside_active_root']}")
    lines.append(f"- `missing`: {summary['missing']}")
    lines.append("")
    lines.append("## Section Summary")
    lines.append("")
    lines.append("| Part | Chapter | Section | Refs | Strict | Bedrock | Bedrock Decl | Active Unaudited | Outside Root | Missing |")
    lines.append("| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |")

    for section in report["sections"]:
        counts = Counter(section["counts"])
        total = sum(counts.values())
        lines.append(
            f"| {section['part']} | {section['chapter_number']} {section['chapter_title']} | "
            f"`{section['section']}` | {total} | {counts['audited_strict']} | {counts['audited_bedrock']} | "
            f"{counts['active_bedrock_decl']} | {counts['active_root_unaudited']} | "
            f"{counts['outside_active_root']} | {counts['missing']} |"
        )

    lines.append("")
    lines.append("## Boundary And Gap Details")
    lines.append("")

    for section in report["sections"]:
        counts = Counter(section["counts"])
        if (
            counts["audited_bedrock"] == 0
            and counts["active_bedrock_decl"] == 0
            and counts["active_root_unaudited"] == 0
            and counts["outside_active_root"] == 0
            and counts["missing"] == 0
        ):
            continue

        lines.append(f"### `{section['section']}`")
        lines.append("")
        lines.append(
            f"`{section['part']}`, Chapter {section['chapter_number']} ({section['chapter_title']}); "
            f"source `{section['tex_path']}`"
        )
        lines.append("")

        grouped: dict[str, list[dict[str, object]]] = defaultdict(list)
        for ref in section["refs"]:
            if ref["status"] != "audited_strict":
                grouped[ref["status"]].append(ref)

        for status in (
            "audited_bedrock",
            "active_bedrock_decl",
            "active_root_unaudited",
            "outside_active_root",
            "missing",
        ):
            items = grouped.get(status, [])
            if not items:
                continue
            lines.append(f"{status}:")
            for item in items:
                owner_suffix = f" -> `{item['owner']}`" if item["owner"] else ""
                lines.append(
                    f"- `{item['full_name']}` (from `{item['display_name']}`, line {item['first_line']}){owner_suffix}"
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
        f"{summary['unique_lean_refs']} refs,",
        f"{summary['audited_strict']} strict,",
        f"{summary['audited_bedrock']} bedrock-audited,",
        f"{summary['active_bedrock_decl']} bedrock-decls,",
        f"{summary['active_root_unaudited']} active-unaudited,",
        f"{summary['outside_active_root']} outside-root,",
        f"{summary['missing']} missing",
    )


if __name__ == "__main__":
    main()
