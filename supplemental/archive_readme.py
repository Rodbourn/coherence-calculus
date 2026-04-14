#!/usr/bin/env python3
"""
Generate a concise upload-facing README for the artifacts directory.

Output:
  - artifacts/README.md

The goal is to make the generated archive surface self-describing without
requiring a reader to inspect the build scripts first.
"""

from __future__ import annotations

import json
from datetime import datetime
from pathlib import Path


PROJECT_ROOT = Path(__file__).parent.parent
OUTPUT_DIR = PROJECT_ROOT / "artifacts"

MANIFEST_PATH = OUTPUT_DIR / "lean_manifest.json"
PIPELINE_PATH = OUTPUT_DIR / "lean_pipeline_status.json"
README_PATH = OUTPUT_DIR / "README.md"


def load_json(path: Path) -> dict:
    if not path.exists():
        return {}
    return json.loads(path.read_text(encoding="utf-8"))


def existing(names: list[str]) -> list[str]:
    return [name for name in names if (OUTPUT_DIR / name).exists()]


def main() -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    manifest = load_json(MANIFEST_PATH)
    pipeline = load_json(PIPELINE_PATH)
    summary = manifest.get("summary", {})
    pipeline_summary = pipeline.get("summary", {})
    bridge_requested = bool(pipeline_summary.get("bridge_requested"))

    pdfs = sorted(path.name for path in OUTPUT_DIR.glob("hbc-*.pdf"))
    audit_logs = existing(
        [
            "lean_part_i_ii_audits.out.txt",
            "lean_part_iii_audits.out.txt",
            "lean_part_iv_audits.out.txt",
            "lean_appendix_operators_audits.out.txt",
            "lean_appendix_horizons_audits.out.txt",
            "lean_mathlib_bridge_build.out.txt",
        ]
    )
    flat_roots = existing(
        [
            "lean_foundation_flat.lean",
            "lean_part_iii_flat.lean",
            "lean_part_iv_flat.lean",
            "lean_appendix_operators_flat.lean",
            "lean_appendix_horizons_flat.lean",
            "lean_mathlib_bridge_flat.lean",
        ]
    )
    machine_reports = existing(
        [
            "dashboard.html",
            "lean_manifest.json",
            "lean_pipeline_status.json",
            "lean_coverage_reports.json",
        ]
    )

    completion_markers = [
        "dashboard.html",
        "lean_manifest.json",
        "lean_pipeline_status.json",
        "lean_coverage_reports.json",
        "lean_foundation_flat.lean",
        "lean_part_iii_flat.lean",
        "lean_part_iv_flat.lean",
    ]
    missing_markers = [name for name in completion_markers if not (OUTPUT_DIR / name).exists()]

    lines = [
        "# README",
        "",
        f"Generated: `{datetime.now().isoformat()}`",
        "",
        "This directory is the upload-facing artifact surface produced by the manuscript build pipeline.",
        "It is intended to be small enough to inspect directly while still exposing the Lean certification and manuscript-coverage status.",
        "",
        "## What Belongs Here",
        "",
        "- Manuscript outputs: the compiled PDF and the flattened TeX source.",
        "- Lean audit outputs: lane-specific `#print axioms` logs from the recorded passing run.",
        "- Flat Lean exports: self-contained manuscript proof surfaces and the optional bridge export.",
        "- Verification helpers: machine-readable status files describing the recorded passing run.",
        "",
        "## How To Read The Lean Artifacts",
        "",
        "- Each manuscript `lean_*_flat.lean` file contains the full local dependency closure needed to kernel-check that manuscript lane directly with `lean`.",
        "- The audit logs are the authoritative axiom reports for those roots.",
        "- `lean_mathlib_bridge_flat.lean` is the optional external mathlib-validation export. Checking it requires any mathlib-enabled Lean 4 workspace, not the upstream project tree.",
        "- The PDF filename is generated from the current git commit hash; a clean tree omits the `-dirty` suffix.",
        "",
        "## Present Files",
        "",
    ]

    if pdfs:
        lines.append("### Manuscript")
        lines.append("")
        for name in pdfs:
            lines.append(f"- `{name}`")
        if (OUTPUT_DIR / "hbc_flat.tex").exists():
            lines.append("- `hbc_flat.tex`")
        lines.append("")

    if audit_logs:
        lines.append("### Audit Logs")
        lines.append("")
        for name in audit_logs:
            lines.append(f"- `{name}`")
        lines.append("")

    if flat_roots:
        lines.append("### Flat Lean Roots")
        lines.append("")
        for name in flat_roots:
            lines.append(f"- `{name}`")
        lines.append("")

    if machine_reports:
        lines.append("### Verification Files")
        lines.append("")
        for name in machine_reports:
            lines.append(f"- `{name}`")
        lines.append("")

    lines.extend(
        [
            "## Current Verified Scope",
            "",
            f"- Manuscript-lane declarations counted on the dashboard: `{summary.get('active_total', '—')}`",
            f"- Bridge declarations counted on the dashboard: `{summary.get('bridge_total', '—')}`",
            f"- Certified manuscript lanes passing in the recorded pipeline run: `{pipeline_summary.get('certified_lanes_passing', '—')}`",
            f"- Appendix lanes passing in the recorded pipeline run: `{pipeline_summary.get('appendix_lanes_passing', '—')}`",
            f"- Full manuscript lanes passing in the recorded pipeline run: `{pipeline_summary.get('full_manuscript_lanes_passing', '—')}`",
            f"- External validation bridge requested in the recorded pipeline run: `{bridge_requested}`",
            "",
            "## Completeness Check",
            "",
        ]
    )

    if missing_markers:
        lines.append("The directory is incomplete if any of the following core files are missing:")
        lines.append("")
        for name in missing_markers:
            lines.append(f"- `{name}`")
        lines.append("")
        lines.append("If that happens, the build was interrupted and the archive should be regenerated before deposit.")
    else:
        lines.append("The core verification surface is present.")

    lines.extend(
        [
            "",
            "## Checking The Flat Exports",
            "",
            "- The manuscript flat exports are intended to kernel-check directly with `lean`.",
            "- The optional mathlib bridge export is reviewable as a flat source surface, but still needs a mathlib-enabled Lean 4 workspace for checking.",
        ]
    )

    README_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"Archive README: {README_PATH}")


if __name__ == "__main__":
    main()
