#!/usr/bin/env python3
"""
Generate flat Lean upload artifacts for the active proof roots.

Outputs:
  - artifacts/lean_foundation_flat.lean
  - artifacts/lean_part_iii_flat.lean
  - artifacts/lean_part_iv_flat.lean
  - artifacts/lean_appendix_operators_flat.lean
  - artifacts/lean_appendix_horizons_flat.lean
  - artifacts/lean_mathlib_bridge_flat.lean

Each file concatenates the transitive local dependency closure needed for the
target root, preserving file boundaries in comments and hoisting only external
imports to the top.
"""

from __future__ import annotations

import json
import re
from collections import OrderedDict
from datetime import datetime
from pathlib import Path


PROJECT_ROOT = Path(__file__).parent.parent
OUTPUT_DIR = PROJECT_ROOT / "artifacts"
MANIFEST_PATH = OUTPUT_DIR / "lean_manifest.json"

BRIDGE_PACKAGE_DIR = PROJECT_ROOT / "CoherenceCalculusMathlibBridge" / "CoherenceCalculusMathlibBridge"

IMPORT_RE = re.compile(r"^\s*import\s+(.+?)\s*$")


ROOT_SPECS = [
    {
        "label": "Certified Foundation root",
        "artifact": "lean_foundation_flat.lean",
        "source_root": "CoherenceCalculus/CoherenceCalculus/Foundation.lean",
        "local_module_prefixes": ["CoherenceCalculus"],
        "count_keys": ["Part I", "Part II", "Part III (Foundation)"],
    },
    {
        "label": "Certified Part III root",
        "artifact": "lean_part_iii_flat.lean",
        "source_root": "CoherenceCalculus/CoherenceCalculus/PartIII.lean",
        "local_module_prefixes": ["CoherenceCalculus"],
        "count_keys": ["Part III (PartIII/)"],
    },
    {
        "label": "Certified Part IV root",
        "artifact": "lean_part_iv_flat.lean",
        "source_root": "CoherenceCalculus/CoherenceCalculus/PartIV.lean",
        "local_module_prefixes": ["CoherenceCalculus"],
        "count_keys": ["Part IV (PartIV/)"],
    },
    {
        "label": "Appendix operator root",
        "artifact": "lean_appendix_operators_flat.lean",
        "source_root": "CoherenceCalculus/CoherenceCalculus/AppendixOperators.lean",
        "local_module_prefixes": ["CoherenceCalculus"],
        "count_keys": ["Appendix Operators"],
    },
    {
        "label": "Appendix horizon root",
        "artifact": "lean_appendix_horizons_flat.lean",
        "source_root": "CoherenceCalculus/CoherenceCalculus/AppendixHorizons.lean",
        "local_module_prefixes": ["CoherenceCalculus"],
        "count_keys": ["Appendix Horizons"],
    },
    {
        "label": "External mathlib validation bridge",
        "artifact": "lean_mathlib_bridge_flat.lean",
        "source_root": "CoherenceCalculusMathlibBridge/CoherenceCalculusMathlibBridge.lean",
        "local_module_prefixes": ["CoherenceCalculusMathlibBridge", "CoherenceCalculus"],
        "count_keys": [],
    },
]


MODULE_PREFIX_ROOTS: dict[str, Path] = {
    "CoherenceCalculus": PROJECT_ROOT / "CoherenceCalculus",
    "CoherenceCalculusMathlibBridge": PROJECT_ROOT / "CoherenceCalculusMathlibBridge",
}


def load_manifest() -> dict:
    if not MANIFEST_PATH.exists():
        raise FileNotFoundError(
            f"Missing {MANIFEST_PATH}. Run supplemental/lean_dashboard.py first."
        )
    return json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))


def parse_imports(path: Path) -> list[str]:
    imports: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = IMPORT_RE.match(line)
        if match:
            imports.extend(match.group(1).split())
    return imports


def strip_import_lines(text: str) -> str:
    body_lines = [line for line in text.splitlines() if not IMPORT_RE.match(line)]
    body = "\n".join(body_lines).lstrip("\n")
    return body.rstrip() + "\n"


def ordered_unique(items: list[str]) -> list[str]:
    seen = OrderedDict()
    for item in items:
        seen.setdefault(item, None)
    return list(seen.keys())


def declaration_count(manifest: dict, spec: dict) -> int:
    parts = manifest.get("parts", {})
    if spec["artifact"] == "lean_mathlib_bridge_flat.lean":
        bridge_package = manifest.get("bridge_package", {})
        return len(bridge_package.get("active", [])) + len(bridge_package.get("orphaned", []))
    return sum(len(parts.get(key, [])) for key in spec["count_keys"])


def resolve_local_module(module_name: str) -> Path | None:
    for prefix, workspace_root in MODULE_PREFIX_ROOTS.items():
        if module_name == prefix:
            return workspace_root / f"{prefix}.lean"
        local_prefix = f"{prefix}."
        if module_name.startswith(local_prefix):
            suffix = module_name[len(local_prefix) :].split(".")
            return workspace_root / prefix / Path(*suffix).with_suffix(".lean")
    return None


def collect_source_files(spec: dict) -> list[Path]:
    root_path = PROJECT_ROOT / spec["source_root"]
    local_module_prefixes = spec["local_module_prefixes"]
    local_prefixes = tuple(f"{prefix}." for prefix in local_module_prefixes)
    seen: OrderedDict[Path, None] = OrderedDict()

    def walk(path: Path) -> None:
        if path in seen:
            return
        for imp in parse_imports(path):
            if imp in local_module_prefixes or imp.startswith(local_prefixes):
                dep = resolve_local_module(imp)
                if dep is None or not dep.exists():
                    raise FileNotFoundError(f"unable to resolve local import {imp} from {path}")
                walk(dep)
        seen[path] = None

    walk(root_path)
    return list(seen.keys())


def external_imports(paths: list[Path], local_module_prefixes: list[str]) -> list[str]:
    imports: list[str] = []
    local_prefixes = tuple(f"{prefix}." for prefix in local_module_prefixes)
    for path in paths:
        for imp in parse_imports(path):
            if imp in local_module_prefixes or imp.startswith(local_prefixes):
                continue
            imports.append(imp)
    return ordered_unique(imports)


def render_flat_file(manifest: dict, spec: dict) -> str:
    source_files = collect_source_files(spec)
    imports = external_imports(source_files, spec["local_module_prefixes"])
    decl_count = declaration_count(manifest, spec)

    header = [
        "/-",
        "Auto-generated flat Lean export for upload.",
        f"Generated: {datetime.now().isoformat()}",
        f"Root: {spec['source_root']}",
        f"Included transitive local files: {len(source_files)}",
        f"Declarations represented: {decl_count}",
        "Every declaration counted for this root in artifacts/dashboard.html is present below.",
        "The local dependency closure needed to check this root is also included below.",
        "-/",
        "",
    ]
    if imports:
        header.extend(f"import {imp}" for imp in imports)
        header.append("")

    chunks = ["\n".join(header)]
    for path in source_files:
        rel = path.relative_to(PROJECT_ROOT).as_posix()
        chunks.append(f"/- FILE: {rel} -/\n")
        chunks.append(strip_import_lines(path.read_text(encoding="utf-8")))
        chunks.append("")
    return "\n".join(chunks).rstrip() + "\n"


def main() -> None:
    OUTPUT_DIR.mkdir(exist_ok=True)
    manifest = load_manifest()

    for spec in ROOT_SPECS:
        if spec["artifact"] == "lean_mathlib_bridge_flat.lean" and not BRIDGE_PACKAGE_DIR.exists():
            continue
        output_path = OUTPUT_DIR / spec["artifact"]
        output_path.write_text(render_flat_file(manifest, spec), encoding="utf-8")
        print(f"Wrote {output_path.name}")


if __name__ == "__main__":
    main()
