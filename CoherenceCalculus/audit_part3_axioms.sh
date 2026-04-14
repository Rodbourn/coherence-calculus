#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

lake build CoherenceCalculus.PartIII
python3 audit_axiom_surface.py --mode strict part3_axiom_check.lean
python3 audit_axiom_surface.py --mode strict part3_derived_axiom_check.lean
