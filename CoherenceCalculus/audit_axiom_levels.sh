#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

bash audit_active_axioms.sh
bash audit_bedrock_axioms.sh

echo "All axiom-surface audits passed."
