#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path


BEDROCK_AXIOMS = {
    "CoherenceCalculus.Primitive",
    "CoherenceCalculus.Primitive.decEq",
    "CoherenceCalculus.bulkCount",
    "CoherenceCalculus.boundaryCount",
    "CoherenceCalculus.closure",
}

PRINT_RE = re.compile(r"""^\s*#print axioms ([A-Za-z0-9_'.]+)\s*$""")
NONE_RE = re.compile(r"""^'([^']+)' does not depend on any axioms$""")
DEPENDS_RE = re.compile(r"""^'([^']+)' depends on axioms: \[(.*)$""")


def parse_surface_names(surface: Path) -> list[str]:
    names: list[str] = []
    for line in surface.read_text(encoding="utf-8").splitlines():
        match = PRINT_RE.match(line)
        if match:
            names.append(match.group(1))
    return names


def parse_lean_output(output: str) -> dict[str, list[str]]:
    results: dict[str, list[str]] = {}
    lines = output.splitlines()
    i = 0

    while i < len(lines):
        line = lines[i]

        none_match = NONE_RE.match(line)
        if none_match:
            results[none_match.group(1)] = []
            i += 1
            continue

        depends_match = DEPENDS_RE.match(line)
        if depends_match:
            theorem = depends_match.group(1)
            chunks = [depends_match.group(2)]
            while not chunks[-1].rstrip().endswith("]"):
                i += 1
                if i >= len(lines):
                    raise ValueError(f"unterminated axiom list for {theorem}")
                chunks.append(lines[i])
            body = "\n".join(chunks)
            body = body.rsplit("]", 1)[0]
            axioms = [piece.strip() for piece in body.split(",") if piece.strip()]
            results[theorem] = axioms
            i += 1
            continue

        i += 1

    return results


def run_surface(surface: Path) -> tuple[int, str]:
    proc = subprocess.run(
        ["lake", "env", "lean", surface.name],
        cwd=surface.parent,
        capture_output=True,
        text=True,
    )
    output = proc.stdout + proc.stderr
    return proc.returncode, output


def check_strict(surface: Path, results: dict[str, list[str]]) -> int:
    failed = False
    for theorem in parse_surface_names(surface):
        axioms = results.get(theorem)
        if axioms is None:
            print(f"Strict axiom audit failed: no `#print axioms` output found for {theorem}.", file=sys.stderr)
            failed = True
            continue
        if axioms:
            joined = ", ".join(axioms)
            print(
                f"Strict axiom audit failed: {theorem} depends on forbidden axioms: {joined}.",
                file=sys.stderr,
            )
            failed = True
    if failed:
        return 1

    print("Strict no-axioms audit passed.")
    return 0


def check_bedrock(surface: Path, results: dict[str, list[str]]) -> int:
    failed = False
    for theorem in parse_surface_names(surface):
        axioms = results.get(theorem)
        if axioms is None:
            print(f"Bedrock axiom audit failed: no `#print axioms` output found for {theorem}.", file=sys.stderr)
            failed = True
            continue
        disallowed = sorted(set(axioms) - BEDROCK_AXIOMS)
        if disallowed:
            joined = ", ".join(disallowed)
            print(
                f"Bedrock axiom audit failed: {theorem} depends on non-bedrock axioms: {joined}.",
                file=sys.stderr,
            )
            failed = True
    if failed:
        return 1

    print("Bedrock-surface axiom audit passed.")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description="Run and validate a Lean `#print axioms` audit surface.")
    parser.add_argument("surface", help="Path to the Lean audit surface file.")
    parser.add_argument("--mode", choices=("strict", "bedrock"), required=True)
    args = parser.parse_args()

    surface = Path(args.surface).resolve()
    returncode, output = run_surface(surface)
    if output:
        print(output, end="" if output.endswith("\n") else "\n")
    if returncode != 0:
        return returncode

    results = parse_lean_output(output)
    if args.mode == "strict":
        return check_strict(surface, results)
    return check_bedrock(surface, results)


if __name__ == "__main__":
    raise SystemExit(main())
