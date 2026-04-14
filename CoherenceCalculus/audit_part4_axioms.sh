#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

lake build CoherenceCalculus.PartIV
python3 audit_axiom_surface.py --mode strict part4_axiom_check.lean
