#!/usr/bin/env python3
"""
Combine manuscript Lean coverage/tag reports into one upload-facing JSON file.

This keeps the build artifact surface compact while preserving the native
per-lane report generators and their internal data structures.
"""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
ARTIFACTS = PROJECT_ROOT / "artifacts"
OUTPUT_JSON = ARTIFACTS / "lean_coverage_reports.json"

INPUT_REPORTS = {
    "part_i_ii_coverage": ARTIFACTS / "active_part_i_ii_coverage.json",
    "part_i_ii_tag": ARTIFACTS / "part_i_ii_tag_audit.json",
    "part_iii_coverage": ARTIFACTS / "part_iii_coverage.json",
    "part_iii_tag": ARTIFACTS / "part_iii_tag_audit.json",
    "part_iv_coverage": ARTIFACTS / "part_iv_coverage.json",
    "part_iv_tag": ARTIFACTS / "part_iv_tag_audit.json",
    "appendix_operators_coverage": ARTIFACTS / "appendix_operators_coverage.json",
    "appendix_operators_tag": ARTIFACTS / "appendix_operators_tag_audit.json",
    "appendix_horizons_coverage": ARTIFACTS / "appendix_horizons_coverage.json",
    "appendix_horizons_tag": ARTIFACTS / "appendix_horizons_tag_audit.json",
}


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def main() -> None:
    ARTIFACTS.mkdir(parents=True, exist_ok=True)

    missing = [str(path.relative_to(PROJECT_ROOT)) for path in INPUT_REPORTS.values() if not path.exists()]
    if missing:
        raise SystemExit(f"missing coverage inputs: {', '.join(missing)}")

    reports = {name: load_json(path) for name, path in INPUT_REPORTS.items()}
    combined = {
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "reports": reports,
        "summary": {
            name: report.get("summary", {})
            for name, report in reports.items()
        },
    }

    OUTPUT_JSON.write_text(json.dumps(combined, indent=2), encoding="utf-8")
    print(f"wrote {OUTPUT_JSON.relative_to(PROJECT_ROOT)}")
    for name, report in combined["summary"].items():
        print(f"summary: {name} -> {json.dumps(report, sort_keys=True)}")


if __name__ == "__main__":
    main()
