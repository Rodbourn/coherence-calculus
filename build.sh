#!/bin/bash

# Build script for the public monograph repository.
# Builds the monograph in build/ and outputs artifacts/.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
MONOGRAPH_DIR="$SCRIPT_DIR/manuscripts/monograph"
BUILD_DIR="$SCRIPT_DIR/build"
ARTIFACTS_DIR="$SCRIPT_DIR/artifacts"
MAIN_TEX="hbc.tex"
MAIN_NAME="hbc"
WITH_BRIDGE=0
ZENODO_MODE=0

while [ "$#" -gt 0 ]; do
    case "$1" in
        --with-bridge)
            WITH_BRIDGE=1
            ;;
        --zenodo)
            WITH_BRIDGE=1
            ZENODO_MODE=1
            ;;
        *)
            echo "Unknown option: $1" >&2
            echo "Usage: bash build.sh [--with-bridge] [--zenodo]" >&2
            exit 1
            ;;
    esac
    shift
done

# Clean and create directories
mkdir -p "$BUILD_DIR"
mkdir -p "$ARTIFACTS_DIR"
find "$ARTIFACTS_DIR" -mindepth 1 -maxdepth 1 -exec rm -rf {} + 2>/dev/null || true

echo "=== Building $MAIN_TEX ==="

# Get git hash
GIT_HASH=$(git -C "$SCRIPT_DIR" rev-parse --short HEAD 2>/dev/null || echo "unknown")
GIT_DIRTY=""
if git -C "$SCRIPT_DIR" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    if ! git -C "$SCRIPT_DIR" diff --ignore-cr-at-eol --quiet -- \
            . \
            ':(exclude)artifacts' \
            ':(exclude)build' \
            2>/dev/null \
        || ! git -C "$SCRIPT_DIR" diff --cached --ignore-cr-at-eol --quiet -- \
            . \
            ':(exclude)artifacts' \
            ':(exclude)build' \
            2>/dev/null; then
        GIT_DIRTY="-dirty"
    fi
fi
GIT_VERSION="${GIT_HASH}${GIT_DIRTY}"
echo "Git version: $GIT_VERSION"

LEAN_DIR="$SCRIPT_DIR/CoherenceCalculus"
BRIDGE_DIR="$SCRIPT_DIR/CoherenceCalculusMathlibBridge"

LEAN_BUILD_LOG="$BUILD_DIR/lean_main_build.out.txt"
LEAN_PART_I_II_AUDIT_LOG="$ARTIFACTS_DIR/lean_part_i_ii_audits.out.txt"
LEAN_PART_III_AUDIT_LOG="$ARTIFACTS_DIR/lean_part_iii_audits.out.txt"
LEAN_PART_IV_AUDIT_LOG="$ARTIFACTS_DIR/lean_part_iv_audits.out.txt"
LEAN_APPENDIX_OPERATORS_AUDIT_LOG="$ARTIFACTS_DIR/lean_appendix_operators_audits.out.txt"
LEAN_APPENDIX_HORIZONS_AUDIT_LOG="$ARTIFACTS_DIR/lean_appendix_horizons_audits.out.txt"
LEAN_BRIDGE_LOG="$ARTIFACTS_DIR/lean_mathlib_bridge_build.out.txt"
LEAN_PIPELINE_STATUS_JSON="$ARTIFACTS_DIR/lean_pipeline_status.json"
LEAN_BUILD_STATUS_FILE="$BUILD_DIR/.lean_build_status"
LEAN_PART_I_II_STATUS_FILE="$BUILD_DIR/.lean_part_i_ii_status"
LEAN_PART_III_STATUS_FILE="$BUILD_DIR/.lean_part_iii_status"
LEAN_PART_IV_STATUS_FILE="$BUILD_DIR/.lean_part_iv_status"
LEAN_APPENDIX_OPERATORS_STATUS_FILE="$BUILD_DIR/.lean_appendix_operators_status"
LEAN_APPENDIX_HORIZONS_STATUS_FILE="$BUILD_DIR/.lean_appendix_horizons_status"
LEAN_BRIDGE_STATUS_FILE="$BUILD_DIR/.lean_bridge_status"

LEAN_BUILD_STATUS="not-run"
LEAN_PART_I_II_AUDIT_STATUS="not-run"
LEAN_PART_III_AUDIT_STATUS="not-run"
LEAN_PART_IV_AUDIT_STATUS="not-run"
LEAN_APPENDIX_OPERATORS_AUDIT_STATUS="not-run"
LEAN_APPENDIX_HORIZONS_AUDIT_STATUS="not-run"
LEAN_BRIDGE_STATUS="skipped"

LEAN_BUILD_COMMAND="cd CoherenceCalculus && lake build"
LEAN_PART_I_II_AUDIT_COMMAND="cd CoherenceCalculus && bash audit_axiom_levels.sh"
LEAN_PART_III_AUDIT_COMMAND="cd CoherenceCalculus && bash audit_part3_axioms.sh"
LEAN_PART_IV_AUDIT_COMMAND="cd CoherenceCalculus && bash audit_part4_axioms.sh"
LEAN_APPENDIX_OPERATORS_AUDIT_COMMAND="cd CoherenceCalculus && lake build CoherenceCalculus.AppendixOperators && bash audit_appendix_operators_axioms.sh"
LEAN_APPENDIX_HORIZONS_AUDIT_COMMAND="cd CoherenceCalculus && lake build CoherenceCalculus.AppendixHorizons && bash audit_appendix_horizons_axioms.sh"
LEAN_BRIDGE_COMMAND="cd CoherenceCalculusMathlibBridge && lake build"
COVERAGE_JSON_FILES=(
    "$ARTIFACTS_DIR/active_part_i_ii_coverage.json"
    "$ARTIFACTS_DIR/part_i_ii_tag_audit.json"
    "$ARTIFACTS_DIR/part_iii_coverage.json"
    "$ARTIFACTS_DIR/part_iii_tag_audit.json"
    "$ARTIFACTS_DIR/part_iv_coverage.json"
    "$ARTIFACTS_DIR/part_iv_tag_audit.json"
    "$ARTIFACTS_DIR/appendix_operators_coverage.json"
    "$ARTIFACTS_DIR/appendix_operators_tag_audit.json"
    "$ARTIFACTS_DIR/appendix_horizons_coverage.json"
    "$ARTIFACTS_DIR/appendix_horizons_tag_audit.json"
)

run_with_live_log() {
    local log_path="$1"
    shift
    "$@" 2>&1 | tee "$log_path"
    local cmd_status=${PIPESTATUS[0]}
    return "$cmd_status"
}

write_status_markers() {
    printf '%s\n' "$LEAN_BUILD_STATUS" > "$LEAN_BUILD_STATUS_FILE"
    printf '%s\n' "$LEAN_PART_I_II_AUDIT_STATUS" > "$LEAN_PART_I_II_STATUS_FILE"
    printf '%s\n' "$LEAN_PART_III_AUDIT_STATUS" > "$LEAN_PART_III_STATUS_FILE"
    printf '%s\n' "$LEAN_PART_IV_AUDIT_STATUS" > "$LEAN_PART_IV_STATUS_FILE"
    printf '%s\n' "$LEAN_APPENDIX_OPERATORS_AUDIT_STATUS" > "$LEAN_APPENDIX_OPERATORS_STATUS_FILE"
    printf '%s\n' "$LEAN_APPENDIX_HORIZONS_AUDIT_STATUS" > "$LEAN_APPENDIX_HORIZONS_STATUS_FILE"
    printf '%s\n' "$LEAN_BRIDGE_STATUS" > "$LEAN_BRIDGE_STATUS_FILE"
}

write_lean_pipeline_status() {
    export PIPELINE_OUTPUT="$LEAN_PIPELINE_STATUS_JSON"
    export PIPELINE_GIT_VERSION="$GIT_VERSION"
    export PIPELINE_MODE_WITH_BRIDGE="$WITH_BRIDGE"
    export PIPELINE_MODE_ZENODO="$ZENODO_MODE"
    export PIPELINE_LEAN_BUILD_STATUS_FILE="$LEAN_BUILD_STATUS_FILE"
    export PIPELINE_LEAN_BUILD_COMMAND="$LEAN_BUILD_COMMAND"
    export PIPELINE_PART_I_II_STATUS_FILE="$LEAN_PART_I_II_STATUS_FILE"
    export PIPELINE_PART_I_II_LOG="$(basename "$LEAN_PART_I_II_AUDIT_LOG")"
    export PIPELINE_PART_I_II_COMMAND="$LEAN_PART_I_II_AUDIT_COMMAND"
    export PIPELINE_PART_III_STATUS_FILE="$LEAN_PART_III_STATUS_FILE"
    export PIPELINE_PART_III_LOG="$(basename "$LEAN_PART_III_AUDIT_LOG")"
    export PIPELINE_PART_III_COMMAND="$LEAN_PART_III_AUDIT_COMMAND"
    export PIPELINE_PART_IV_STATUS_FILE="$LEAN_PART_IV_STATUS_FILE"
    export PIPELINE_PART_IV_LOG="$(basename "$LEAN_PART_IV_AUDIT_LOG")"
    export PIPELINE_PART_IV_COMMAND="$LEAN_PART_IV_AUDIT_COMMAND"
    export PIPELINE_APPENDIX_OPERATORS_STATUS_FILE="$LEAN_APPENDIX_OPERATORS_STATUS_FILE"
    export PIPELINE_APPENDIX_OPERATORS_LOG="$(basename "$LEAN_APPENDIX_OPERATORS_AUDIT_LOG")"
    export PIPELINE_APPENDIX_OPERATORS_COMMAND="$LEAN_APPENDIX_OPERATORS_AUDIT_COMMAND"
    export PIPELINE_APPENDIX_HORIZONS_STATUS_FILE="$LEAN_APPENDIX_HORIZONS_STATUS_FILE"
    export PIPELINE_APPENDIX_HORIZONS_LOG="$(basename "$LEAN_APPENDIX_HORIZONS_AUDIT_LOG")"
    export PIPELINE_APPENDIX_HORIZONS_COMMAND="$LEAN_APPENDIX_HORIZONS_AUDIT_COMMAND"
    export PIPELINE_BRIDGE_STATUS_FILE="$LEAN_BRIDGE_STATUS_FILE"
    export PIPELINE_BRIDGE_LOG_FILE="$LEAN_BRIDGE_LOG"
    export PIPELINE_BRIDGE_LOG="$(basename "$LEAN_BRIDGE_LOG")"
    export PIPELINE_BRIDGE_COMMAND="$LEAN_BRIDGE_COMMAND"
    python3 - <<'PY'
import json
import os
from pathlib import Path
from datetime import datetime, timezone

def read_status(path_key, default):
    path = Path(os.environ[path_key])
    if not path.exists():
        return default
    return path.read_text(encoding="utf-8").strip() or default

def step(status, command_key, requested=True, log_key=None):
    data = {
        "status": status,
        "requested": requested,
        "command": os.environ[command_key],
    }
    if log_key:
        data["log"] = f"artifacts/{os.environ[log_key]}"
    return data

mode = {
    "with_bridge": (
        os.environ["PIPELINE_MODE_WITH_BRIDGE"] == "1"
        or read_status("PIPELINE_BRIDGE_STATUS_FILE", "skipped") != "skipped"
        or Path(os.environ["PIPELINE_BRIDGE_LOG_FILE"]).exists()
    ),
    "zenodo": os.environ["PIPELINE_MODE_ZENODO"] == "1",
}
main_step = step(
    read_status("PIPELINE_LEAN_BUILD_STATUS_FILE", "not-run"),
    "PIPELINE_LEAN_BUILD_COMMAND",
)
part_i_ii_step = step(
    read_status("PIPELINE_PART_I_II_STATUS_FILE", "not-run"),
    "PIPELINE_PART_I_II_COMMAND",
    log_key="PIPELINE_PART_I_II_LOG",
)
part_iii_step = step(
    read_status("PIPELINE_PART_III_STATUS_FILE", "not-run"),
    "PIPELINE_PART_III_COMMAND",
    log_key="PIPELINE_PART_III_LOG",
)
part_iv_step = step(
    read_status("PIPELINE_PART_IV_STATUS_FILE", "not-run"),
    "PIPELINE_PART_IV_COMMAND",
    log_key="PIPELINE_PART_IV_LOG",
)
appendix_operators_step = step(
    read_status("PIPELINE_APPENDIX_OPERATORS_STATUS_FILE", "not-run"),
    "PIPELINE_APPENDIX_OPERATORS_COMMAND",
    log_key="PIPELINE_APPENDIX_OPERATORS_LOG",
)
appendix_horizons_step = step(
    read_status("PIPELINE_APPENDIX_HORIZONS_STATUS_FILE", "not-run"),
    "PIPELINE_APPENDIX_HORIZONS_COMMAND",
    log_key="PIPELINE_APPENDIX_HORIZONS_LOG",
)
bridge_status = read_status("PIPELINE_BRIDGE_STATUS_FILE", "skipped")
bridge_log_path = Path(os.environ["PIPELINE_BRIDGE_LOG_FILE"])
bridge_requested = bool(mode.get("with_bridge") or bridge_status != "skipped" or bridge_log_path.exists())
if bridge_requested and bridge_status == "skipped" and bridge_log_path.exists():
    bridge_status = "passing"
bridge_step = step(
    bridge_status if bridge_requested else "skipped",
    "PIPELINE_BRIDGE_COMMAND",
    requested=bridge_requested,
    log_key="PIPELINE_BRIDGE_LOG",
)

certified_passing = all(
    item["status"] == "passing"
    for item in (main_step, part_i_ii_step, part_iii_step, part_iv_step)
)
appendix_passing = all(
    item["status"] == "passing"
    for item in (appendix_operators_step, appendix_horizons_step)
)
full_manuscript_passing = certified_passing and appendix_passing
requested_steps = [
    main_step,
    part_i_ii_step,
    part_iii_step,
    part_iv_step,
    appendix_operators_step,
    appendix_horizons_step,
]
if bridge_requested:
    requested_steps.append(bridge_step)
requested_passing = all(item["status"] == "passing" for item in requested_steps)

data = {
    "generated_utc": datetime.now(timezone.utc).isoformat(),
    "git_version": os.environ["PIPELINE_GIT_VERSION"],
    "mode": mode,
    "summary": {
        "certified_lanes_passing": certified_passing,
        "appendix_lanes_passing": appendix_passing,
        "full_manuscript_lanes_passing": full_manuscript_passing,
        "all_requested_lanes_passing": requested_passing,
        "bridge_requested": bridge_requested,
    },
    "steps": {
        "main_lean_build": main_step,
        "part_i_ii_audits": part_i_ii_step,
        "part_iii_audits": part_iii_step,
        "part_iv_audits": part_iv_step,
        "appendix_operators_audits": appendix_operators_step,
        "appendix_horizons_audits": appendix_horizons_step,
        "mathlib_bridge_build": bridge_step,
    },
}

with open(os.environ["PIPELINE_OUTPUT"], "w", encoding="utf-8") as fh:
    json.dump(data, fh, indent=2)
PY
}

write_status_markers

flatten_latex() {
    local file="$1"
    local dir="$(dirname "$file")"

    while IFS= read -r line; do
        if [[ "$line" =~ ^[[:space:]]*\\input\{([^}]+)\} ]]; then
            local input_file="${BASH_REMATCH[1]}"
            [[ "$input_file" != *.tex ]] && input_file="$input_file.tex"
            local full_path="$dir/$input_file"
            if [ -f "$full_path" ]; then
                echo "% === Begin: $input_file ==="
                flatten_latex "$full_path"
                echo "% === End: $input_file ==="
            else
                echo "$line"
            fi
        elif [[ "$line" =~ ^[[:space:]]*\\include\{([^}]+)\} ]]; then
            local include_file="${BASH_REMATCH[1]}"
            [[ "$include_file" != *.tex ]] && include_file="$include_file.tex"
            local full_path="$dir/$include_file"
            if [ -f "$full_path" ]; then
                echo "% === Begin: $include_file ==="
                flatten_latex "$full_path"
                echo "% === End: $include_file ==="
            else
                echo "$line"
            fi
        else
            echo "$line"
        fi
    done < "$file"
}

# Run pdflatex (first pass)
echo "--- First pdflatex pass ---"
cd "$MONOGRAPH_DIR"
pdflatex -interaction=nonstopmode -output-directory="$BUILD_DIR" "\def\githash{$GIT_VERSION}\input{$MAIN_TEX}"
cd "$SCRIPT_DIR"

# Run bibtex if .bib file exists (check both monograph dir and root)
if [ -f "$MONOGRAPH_DIR/references.bib" ]; then
    echo "--- Running bibtex ---"
    cp "$MONOGRAPH_DIR/references.bib" "$BUILD_DIR/"
    cd "$BUILD_DIR"
    bibtex "$MAIN_NAME"
    cd "$SCRIPT_DIR"
elif [ -f "$SCRIPT_DIR/references.bib" ]; then
    echo "--- Running bibtex ---"
    cp "$SCRIPT_DIR/references.bib" "$BUILD_DIR/"
    cd "$BUILD_DIR"
    bibtex "$MAIN_NAME"
    cd "$SCRIPT_DIR"
fi

# Run pdflatex (second pass for references)
echo "--- Second pdflatex pass ---"
cd "$MONOGRAPH_DIR"
pdflatex -interaction=nonstopmode -output-directory="$BUILD_DIR" "\def\githash{$GIT_VERSION}\input{$MAIN_TEX}"
cd "$SCRIPT_DIR"

# Run pdflatex (third pass for cross-references)
echo "--- Third pdflatex pass ---"
cd "$MONOGRAPH_DIR"
pdflatex -interaction=nonstopmode -output-directory="$BUILD_DIR" "\def\githash{$GIT_VERSION}\input{$MAIN_TEX}"
cd "$SCRIPT_DIR"

# Copy PDF to artifacts with git hash in filename
if [ -f "$BUILD_DIR/$MAIN_NAME.pdf" ]; then
    cp "$BUILD_DIR/$MAIN_NAME.pdf" "$ARTIFACTS_DIR/${MAIN_NAME}-${GIT_VERSION}.pdf"
    echo "=== PDF copied to $ARTIFACTS_DIR/${MAIN_NAME}-${GIT_VERSION}.pdf ==="
fi

# Create flattened monograph LaTeX file
echo "=== Creating flattened LaTeX file ==="
flatten_latex "$MONOGRAPH_DIR/$MAIN_TEX" > "$ARTIFACTS_DIR/${MAIN_NAME}_flat.tex"
echo "=== Flattened LaTeX saved to $ARTIFACTS_DIR/${MAIN_NAME}_flat.tex ==="

# Build Lean formalization
echo ""
echo "=========================================="
echo "=== Lean 4 Formalization ==="
echo "=========================================="
if [ -d "$LEAN_DIR" ]; then
    # Source elan if available
    if [ -f "$HOME/.elan/env" ]; then
        source "$HOME/.elan/env"
    fi

    if command -v lake >/dev/null 2>&1; then
        echo "--- Building Lean project ---"
        cd "$LEAN_DIR"
        if run_with_live_log "$LEAN_BUILD_LOG" lake build; then
            LEAN_BUILD_STATUS="passing"
            echo "Lean build: SUCCESS"
        else
            LEAN_BUILD_STATUS="failed"
            echo "Lean build: FAILED (see $LEAN_BUILD_LOG)"
        fi

        echo "--- Auditing Part I / II certified lanes ---"
        if run_with_live_log "$LEAN_PART_I_II_AUDIT_LOG" bash audit_axiom_levels.sh; then
            LEAN_PART_I_II_AUDIT_STATUS="passing"
            echo "Part I / II audits: SUCCESS"
        else
            LEAN_PART_I_II_AUDIT_STATUS="failed"
            echo "Part I / II audits: FAILED (see $LEAN_PART_I_II_AUDIT_LOG)"
        fi

        echo "--- Auditing Part III certified lane ---"
        if run_with_live_log "$LEAN_PART_III_AUDIT_LOG" bash audit_part3_axioms.sh; then
            LEAN_PART_III_AUDIT_STATUS="passing"
            echo "Part III audits: SUCCESS"
        else
            LEAN_PART_III_AUDIT_STATUS="failed"
            echo "Part III audits: FAILED (see $LEAN_PART_III_AUDIT_LOG)"
        fi

        echo "--- Auditing Part IV certified lane ---"
        if run_with_live_log "$LEAN_PART_IV_AUDIT_LOG" bash audit_part4_axioms.sh; then
            LEAN_PART_IV_AUDIT_STATUS="passing"
            echo "Part IV audits: SUCCESS"
        else
            LEAN_PART_IV_AUDIT_STATUS="failed"
            echo "Part IV audits: FAILED (see $LEAN_PART_IV_AUDIT_LOG)"
        fi

        echo "--- Auditing appendix operator lane ---"
        if run_with_live_log "$LEAN_APPENDIX_OPERATORS_AUDIT_LOG" bash -lc "lake build CoherenceCalculus.AppendixOperators && bash audit_appendix_operators_axioms.sh"; then
            LEAN_APPENDIX_OPERATORS_AUDIT_STATUS="passing"
            echo "Appendix operator audits: SUCCESS"
        else
            LEAN_APPENDIX_OPERATORS_AUDIT_STATUS="failed"
            echo "Appendix operator audits: FAILED (see $LEAN_APPENDIX_OPERATORS_AUDIT_LOG)"
        fi

        echo "--- Auditing appendix horizon lane ---"
        if run_with_live_log "$LEAN_APPENDIX_HORIZONS_AUDIT_LOG" bash -lc "lake build CoherenceCalculus.AppendixHorizons && bash audit_appendix_horizons_axioms.sh"; then
            LEAN_APPENDIX_HORIZONS_AUDIT_STATUS="passing"
            echo "Appendix horizon audits: SUCCESS"
        else
            LEAN_APPENDIX_HORIZONS_AUDIT_STATUS="failed"
            echo "Appendix horizon audits: FAILED (see $LEAN_APPENDIX_HORIZONS_AUDIT_LOG)"
        fi
        cd "$SCRIPT_DIR"
    else
        LEAN_BUILD_STATUS="skipped"
        LEAN_PART_I_II_AUDIT_STATUS="skipped"
        LEAN_PART_III_AUDIT_STATUS="skipped"
        LEAN_PART_IV_AUDIT_STATUS="skipped"
        LEAN_APPENDIX_OPERATORS_AUDIT_STATUS="skipped"
        LEAN_APPENDIX_HORIZONS_AUDIT_STATUS="skipped"
        echo "Lean/Lake not installed. Skipping formalization build."
        echo "Install with: curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh"
    fi
else
    LEAN_BUILD_STATUS="skipped"
    LEAN_PART_I_II_AUDIT_STATUS="skipped"
    LEAN_PART_III_AUDIT_STATUS="skipped"
    LEAN_PART_IV_AUDIT_STATUS="skipped"
    LEAN_APPENDIX_OPERATORS_AUDIT_STATUS="skipped"
    LEAN_APPENDIX_HORIZONS_AUDIT_STATUS="skipped"
    echo "No CoherenceCalculus/ directory found. Skipping Lean build."
fi

if [ "$WITH_BRIDGE" -eq 1 ]; then
    echo ""
    echo "=========================================="
    echo "=== External Mathlib Validation Bridge ==="
    echo "=========================================="
    if [ -d "$BRIDGE_DIR" ]; then
        if [ -f "$HOME/.elan/env" ]; then
            source "$HOME/.elan/env"
        fi

        if command -v lake >/dev/null 2>&1; then
            echo "--- Building separate validation bridge package ---"
            cd "$BRIDGE_DIR"
            BRIDGE_TMP_LOG="$BRIDGE_DIR/.bridge_build.out.txt"
            rm -f "$BRIDGE_TMP_LOG"
            if run_with_live_log "$BRIDGE_TMP_LOG" lake build; then
                cp "$BRIDGE_TMP_LOG" "$LEAN_BRIDGE_LOG"
                LEAN_BRIDGE_STATUS="passing"
                printf '%s\n' "$LEAN_BRIDGE_STATUS" > "$LEAN_BRIDGE_STATUS_FILE"
                echo "External validation bridge build: SUCCESS"
            else
                if [ -f "$BRIDGE_TMP_LOG" ]; then
                    cp "$BRIDGE_TMP_LOG" "$LEAN_BRIDGE_LOG"
                fi
                LEAN_BRIDGE_STATUS="failed"
                printf '%s\n' "$LEAN_BRIDGE_STATUS" > "$LEAN_BRIDGE_STATUS_FILE"
                echo "External validation bridge build: FAILED (see $LEAN_BRIDGE_LOG)"
            fi
            rm -f "$BRIDGE_TMP_LOG"
            cd "$SCRIPT_DIR"
        else
            LEAN_BRIDGE_STATUS="skipped"
            printf '%s\n' "$LEAN_BRIDGE_STATUS" > "$LEAN_BRIDGE_STATUS_FILE"
            echo "Lean/Lake not installed. Skipping external validation bridge build."
        fi
    else
        LEAN_BRIDGE_STATUS="skipped"
        printf '%s\n' "$LEAN_BRIDGE_STATUS" > "$LEAN_BRIDGE_STATUS_FILE"
        echo "No CoherenceCalculusMathlibBridge/ directory found. Skipping external validation bridge build."
    fi
fi

write_status_markers
write_lean_pipeline_status

# Run supplemental scripts and capture output
echo ""
echo "=== Running supplemental scripts ==="
SUPPLEMENTAL_DIR="$SCRIPT_DIR/supplemental"

if [ -d "$SUPPLEMENTAL_DIR" ]; then
    run_python_script() {
        local script="$1"
        local keep_log="${2:-no}"
        local script_name
        local output_name
        local temp_log

        script_name=$(basename "$script")
        output_name="${script_name%.py}.out.txt"
        temp_log="$BUILD_DIR/${script_name%.py}.tmp.out.txt"

        echo "--- Running $script_name ---"
        if PYTHONPATH="$SUPPLEMENTAL_DIR" PYTHONIOENCODING=utf-8 python3 "$script" > "$temp_log" 2>&1; then
            if [ "$keep_log" = "yes" ]; then
                cp "$temp_log" "$ARTIFACTS_DIR/$output_name"
                echo "    Output saved to $ARTIFACTS_DIR/$output_name"
            else
                echo "    Completed"
            fi
        else
            cp "$temp_log" "$ARTIFACTS_DIR/$output_name"
            echo "    Script failed (output saved to $ARTIFACTS_DIR/$output_name)"
        fi
        rm -f "$temp_log"
    }

    coverage_scripts=(
        "active_part_coverage.py"
        "part_i_ii_tag_audit.py"
        "part_iii_coverage.py"
        "part_iii_tag_audit.py"
        "part_iv_coverage.py"
        "part_iv_tag_audit.py"
        "appendix_operators_coverage.py"
        "appendix_operators_tag_audit.py"
        "appendix_horizons_coverage.py"
        "appendix_horizons_tag_audit.py"
    )

    deferred_dashboard=""
    deferred_flatten=""
    deferred_archive_readme=""
    deferred_combine=""
    for script_name in "${coverage_scripts[@]}"; do
        script="$SUPPLEMENTAL_DIR/$script_name"
        if [ -f "$script" ]; then
            run_python_script "$script"
        fi
    done

    if [ -f "$SUPPLEMENTAL_DIR/combine_coverage_reports.py" ]; then
        deferred_combine="$SUPPLEMENTAL_DIR/combine_coverage_reports.py"
    fi
    if [ -f "$SUPPLEMENTAL_DIR/lean_dashboard.py" ]; then
        deferred_dashboard="$SUPPLEMENTAL_DIR/lean_dashboard.py"
    fi
    if [ -f "$SUPPLEMENTAL_DIR/flatten_lean_roots.py" ]; then
        deferred_flatten="$SUPPLEMENTAL_DIR/flatten_lean_roots.py"
    fi
    if [ -f "$SUPPLEMENTAL_DIR/archive_readme.py" ]; then
        deferred_archive_readme="$SUPPLEMENTAL_DIR/archive_readme.py"
    fi

    if [ -n "$deferred_combine" ]; then
        run_python_script "$deferred_combine"
        if [ -f "$ARTIFACTS_DIR/lean_coverage_reports.json" ]; then
            rm -f "${COVERAGE_JSON_FILES[@]}"
        fi
    fi
    if [ -n "$deferred_dashboard" ]; then
        run_python_script "$deferred_dashboard"
    fi
    if [ -n "$deferred_flatten" ]; then
        run_python_script "$deferred_flatten"
    fi
    if [ -n "$deferred_archive_readme" ]; then
        run_python_script "$deferred_archive_readme"
    fi
    echo "=== Scripts copied and executed ==="
else
    echo "No supplemental directory found."
fi

# Extract and display warnings
echo ""
echo "=========================================="
echo "=== LaTeX Warnings ==="
echo "=========================================="
if [ -f "$BUILD_DIR/$MAIN_NAME.log" ]; then
    grep -E "(Warning|Overfull|Underfull)" "$BUILD_DIR/$MAIN_NAME.log" || echo "No warnings found."
fi

echo ""
echo "=== Build complete ==="
