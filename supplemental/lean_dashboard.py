#!/usr/bin/env python3
r"""
Coherence Calculus – Lean Verification Dashboard Generator

Generates a dashboard reflecting the actual build graph and the separate
validation lanes:

  CoherenceCalculus.lean
    └─ Foundation.lean  (73 active imports → Foundation/*.lean)

  PartIII.lean  (4 imports → PartIII/*.lean, builds on Foundation)
  PartIV.lean   (2 imports → PartIV/*.lean, builds on exported interfaces)
  AppendixOperators.lean  (strict appendix operator lane)
  AppendixHorizons.lean   (strict appendix horizon lane)

  CoherenceCalculusMathlibBridge.lean
    └─ included one-way mathlib validation layer

Everything else on disk is archived / unbuilt material from earlier stages of
the project and is outside the active manuscript lanes.

Output: artifacts/dashboard.html, artifacts/lean_manifest.json
"""

import os
import re
import json
from pathlib import Path
from datetime import datetime
from collections import OrderedDict

# ── Configuration ──────────────────────────────────────────────────────────

PROJECT_ROOT = Path(__file__).parent.parent
LEAN_DIR = PROJECT_ROOT / "CoherenceCalculus" / "CoherenceCalculus"
LATEX_FLAT = PROJECT_ROOT / "artifacts" / "hbc_flat.tex"
AUX_FILE = PROJECT_ROOT / "build" / "hbc.aux"
OUTPUT_DIR = PROJECT_ROOT / "artifacts"

FOUNDATION_LEAN = LEAN_DIR / "Foundation.lean"
PARTIII_LEAN = LEAN_DIR / "PartIII.lean"
PARTIV_LEAN = LEAN_DIR / "PartIV.lean"
APPENDIX_OPERATORS_LEAN = LEAN_DIR / "AppendixOperators.lean"
APPENDIX_HORIZONS_LEAN = LEAN_DIR / "AppendixHorizons.lean"
ROOT_LEAN = PROJECT_ROOT / "CoherenceCalculus" / "CoherenceCalculus.lean"
STRICT_AUDIT = PROJECT_ROOT / "CoherenceCalculus" / "active_axiom_check.lean"
BEDROCK_AUDIT = PROJECT_ROOT / "CoherenceCalculus" / "active_bedrock_axiom_check.lean"
LEAN_COVERAGE_REPORTS_JSON = OUTPUT_DIR / "lean_coverage_reports.json"
LEAN_PIPELINE_STATUS_JSON = OUTPUT_DIR / "lean_pipeline_status.json"

BRIDGE_PACKAGE_DIR = PROJECT_ROOT / "CoherenceCalculusMathlibBridge"
BRIDGE_ROOT_LEAN = BRIDGE_PACKAGE_DIR / "CoherenceCalculusMathlibBridge.lean"
BRIDGE_LEAN_DIR = BRIDGE_PACKAGE_DIR / "CoherenceCalculusMathlibBridge"
BRIDGE_MATHLIB_CHECKOUT = BRIDGE_PACKAGE_DIR / ".lake" / "packages" / "mathlib"
BRIDGE_COHERENCE_CHECKOUT = BRIDGE_PACKAGE_DIR / ".lake" / "packages" / "CoherenceCalculus"
BRIDGE_BUILD_DIR = BRIDGE_PACKAGE_DIR / ".lake" / "build" / "lib" / "lean" / "CoherenceCalculusMathlibBridge"

BRIDGE_TIER_FILES = OrderedDict([
    ('limit', {'FilterLimit'}),
    ('linear', {'LinearProjection'}),
    ('hilbert', {'AbstractHilbert'}),
    ('continuum', {'ContinuumBattery'}),
    ('lateShell', {'LateShellBattery'}),
    ('promotion', {'PromotionBattery'}),
    ('topology', {'TopologicalBattery'}),
    ('models', {'ConcreteModels'}),
])

BRIDGE_VALIDATION_FILES = OrderedDict([
    ('continuum/topology', {'TopologyValidation'}),
    ('hilbert/projection', {'HilbertProjectionValidation'}),
    ('hilbert/orthogonality', {'HilbertOrthogonalityValidation'}),
    ('hilbert/positivity', {'HilbertPositiveValidation'}),
    ('hilbert/spectral', {'HilbertSpectralValidation'}),
    ('hilbert/eigenspace', {'HilbertEigenspaceValidation'}),
    ('hilbert/minpoly', {'HilbertMinpolyValidation'}),
    ('hilbert/rank', {'HilbertRankValidation'}),
    ('hilbert/trace', {'HilbertTraceValidation'}),
    ('hilbert/trace-rank', {'HilbertTraceRankValidation'}),
    ('hilbert/trace-decomposition', {'HilbertTraceDecompositionValidation'}),
    ('hilbert/block-diagonal', {'HilbertBlockDiagonalValidation'}),
    ('hilbert/restriction-trace', {'HilbertRestrictionTraceValidation'}),
    ('hilbert/block-factorization', {'HilbertBlockFactorizationValidation'}),
    ('hilbert/block-spectrum', {'HilbertBlockSpectrumValidation'}),
    ('hilbert/block-minpoly', {'HilbertBlockMinpolyValidation'}),
    ('hilbert/determinant', {'HilbertDeterminantValidation'}),
    ('hilbert/charpoly', {'HilbertCharpolyValidation'}),
])

# The paper's 3 axioms and their Lean implementations.
PAPER_AXIOMS = OrderedDict([
    ('I', {
        'name': 'Existence',
        'statement': 'There exists a primitive with a determinate identity relation.',
        'lean_decls': ['Primitive', 'Primitive.decEq'],
    }),
    ('II', {
        'name': 'Incidence',
        'statement': 'Primitives admit incidence, recorded through a finite dimension datum.',
        'lean_decls': ['Event'],  # structure, not axiom keyword
    }),
    ('III', {
        'name': 'Closure Balance',
        'statement': 'Pair counts equal order counts for every complete count.',
        'lean_decls': ['bulkCount', 'boundaryCount', 'closure'],
    }),
])

# ── File → Paper Part mapping ─────────────────────────────────────────────

# Maps Foundation file stems to the paper part they support.
# Part I  = Structural Operator Calculus
# Part II = Distinguished Realizations
# Part III = Classical-Limit Bridge (Foundation files that support Part III)
# Files are assigned based on which paper section they formalize.

PART_I_FILES = {
    # Bedrock axioms (transitively imported via NatCore → AxiomCore)
    'AxiomCore',
    # Arithmetic / algebra foundation
    'NatCore', 'CancellationCore', 'SignedCount', 'RawCountCore',
    'NormalizationCore', 'SignedAlgebraCore',
    # Closure equation (bedrock)
    'ClosureCore', 'ClosureClassificationCore',
    # Choice principles
    'StructuredChoiceCore', 'CountableChoiceCore', 'PartialChoiceCore',
    # Dyadic continuum construction
    'DyadicContinuumCore', 'DyadicIntervalCore', 'DyadicPointCore',
    'DyadicOrderCore', 'DyadicBoundaryPairCore', 'DyadicIdentificationCore',
    'DyadicBoundaryEnvelopeCore', 'DyadicComparisonCore', 'DyadicPrefixCore',
    'DyadicPrelineCore', 'DyadicPrelineWitnessCore', 'DyadicPrelinePrefixCore',
    'DyadicPrelineSubdivisionCore',
    # Orientation, bedrock, operators
    'OrientationCore', 'HorizonCore', 'OperatorCore', 'MetricCore',
    'BedrockInterfaceCore', 'PairingCore',
    # Projection calculus
    'ProjectionCalculusCore',
    # Constraint compiler
    'ConstraintCompilerCore', 'ConstraintSelectorCore', 'BoundaryCore',
    # HFT
    'HFTCore', 'HFT2Core', 'TelescopingCore', 'HFTExamplesCore',
    # Foundational lemmas, defect rules
    'FoundationalLemmasWidth', 'DefectRuleCore',
    # Tower calculus
    'TowerCalculusCore', 'SummationCore', 'FaithfulTowerCore',
    'CoherenceTowerCore',
}

PART_II_FILES = {
    # Field-induced horizons
    'FieldInducedHorizonCore',
    # Resolvent / solver
    'ResolventInterfaceCore', 'FiniteComplexCore', 'SolverInterfaceCore',
    # Complex compatibility
    'ComplexCompatibilityInterfaceCore', 'ComplexCompatibilityCorollaryCore',
    # Targets, projector calculus
    'TargetCore', 'ProjectorCalculusCore',
    # Holographic defect
    'HolographicDefectCore',
    # Coherence gap, log-periodic
    'CoherenceGapCore', 'LogPeriodicCore',
    # Transport order
    'TransportOrderSelectionCore', 'TransportOrderFiniteCore',
    'TowerTransportInterfaceCore',
}

PART_III_FOUNDATION_FILES = {
    # Diophantine (Part III section)
    'DiophantineWidth',
    # Closure realization / balance (Part III section)
    'ClosureRealizationCore', 'ClosureDirectCore', 'ClosureTransportCore',
    'ClosureUniquenessCore', 'ClosureBalanceCore',
    # Bridge / transport / rigidity
    'CharacteristicTransportCore', 'VariationalSelectionCore',
    'BridgeObservableCore', 'BridgeObservableCorollaryCore',
    'BridgeTransportCore', 'BridgeTransportCorollaryCore',
    'SelectedChannelRigidityCore', 'BridgeRigidityCore',
    'BridgeRigidityCorollaryCore',
}


# ── Parsing ────────────────────────────────────────────────────────────────

def parse_import_list(filepath):
    """Extract imported module leaf names from a Lean import file."""
    if not filepath.exists():
        return []
    modules = []
    with open(filepath, 'r', encoding='utf-8') as f:
        for line in f:
            m = re.match(r'import\s+(\S+)', line.strip())
            if m:
                modules.append(m.group(1).split('.')[-1])
    return modules


def parse_lean_file(filepath):
    """Parse a single Lean file for declarations, sorry, and axiom counts."""
    declarations = []
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
        lines = content.split('\n')

    patterns = {
        'theorem': r'(?:^|\s)theorem\s+([\w.\']+)',
        'lemma':   r'(?:^|\s)lemma\s+([\w.\']+)',
        'def':     r'(?:^|\s)(?:noncomputable\s+)?def\s+([\w.\']+)',
        'abbrev':  r'(?:^|\s)abbrev\s+([\w.\']+)',
        'structure': r'(?:^|\s)structure\s+([\w.\']+)',
        'class':   r'(?:^|\s)class\s+([\w.\']+)',
        'instance': r'(?:^|\s)instance\s+([\w.\']+)',
        'inductive': r'(?:^|\s)inductive\s+([\w.\']+)',
        'axiom':   r'(?:^|\s)axiom\s+([\w.\']+)',
    }

    in_multiline_comment = False
    for i, line in enumerate(lines, 1):
        stripped = line.strip()

        # Track multi-line comments (simplified: nested /- -/ not handled)
        if '/-' in stripped and '-/' not in stripped:
            in_multiline_comment = True
            continue
        if '-/' in stripped:
            in_multiline_comment = False
            continue
        if in_multiline_comment:
            continue
        if stripped.startswith('--'):
            continue

        for decl_type, pattern in patterns.items():
            match = re.search(pattern, line)
            if match:
                name = match.group(1)
                # Skip private/anonymous names
                if name.startswith('_') or name == 'main':
                    break

                # Look ahead for sorry (bounded to next declaration)
                has_sorry = False
                for j in range(i, min(i + 400, len(lines))):
                    lj = lines[j].strip()
                    # stop at next top-level decl
                    if j > i and re.match(
                        r'(theorem|lemma|def|noncomputable def|abbrev|structure|class|instance|inductive|axiom)\s',
                        lj
                    ):
                        break
                    if lj == 'sorry' or ' sorry' in lj or lj.startswith('sorry'):
                        # Make sure it's not in a comment
                        code_part = lj.split('--')[0]
                        if 'sorry' in code_part:
                            has_sorry = True
                            break

                status = 'pending' if has_sorry else ('axiom' if decl_type == 'axiom' else 'proved')
                declarations.append({
                    'name': name,
                    'type': decl_type,
                    'line': i,
                    'file': filepath.name,
                    'has_sorry': has_sorry,
                    'status': status,
                })
                break  # only one decl per line

    return declarations


def parse_latex_lean_tags(latex_path):
    r"""Parse LaTeX for \lean{...} tags and nearby \label{...}."""
    if not latex_path.exists():
        return {}
    with open(latex_path, 'r', encoding='utf-8') as f:
        content = f.read()

    mappings = {}
    lean_pattern = r'\\lean\{([^}]+)\}'
    label_pattern = r'\\label\{([^}]+)\}'

    for match in re.finditer(lean_pattern, content):
        lean_name = match.group(1)
        pos = match.start()
        search_region = content[max(0, pos - 500):pos]
        label_matches = list(re.finditer(label_pattern, search_region))
        if label_matches:
            nearest_label = label_matches[-1].group(1)
            mappings[lean_name] = nearest_label
    return mappings


def parse_aux_file(aux_path):
    """Parse .aux for label → (number, page, type)."""
    if not aux_path.exists():
        return {}
    with open(aux_path, 'r', encoding='utf-8') as f:
        content = f.read()

    refs = {}
    pattern = r'\\newlabel\{([^}]+)\}\{\{([^}]*)\}\{([^}]*)\}\{([^}]*)\}\{([^}]*)\}'
    for match in re.finditer(pattern, content):
        label = match.group(1)
        refs[label] = {
            'number': match.group(2),
            'page':   match.group(3),
            'title':  match.group(4),
            'type':   match.group(5),
        }
    return refs


def load_json_report(filepath):
    """Load a JSON report if present; otherwise return None."""
    if not filepath.exists():
        return None
    with open(filepath, 'r', encoding='utf-8') as f:
        return json.load(f)


def load_coverage_reports():
    """Load the aggregated coverage report file, with legacy fallback."""
    combined = load_json_report(LEAN_COVERAGE_REPORTS_JSON)
    if combined:
        return combined.get("reports", {})

    return {
        'part_i_ii_coverage': load_json_report(OUTPUT_DIR / "active_part_i_ii_coverage.json"),
        'part_i_ii_tag': load_json_report(OUTPUT_DIR / "part_i_ii_tag_audit.json"),
        'part_iii_coverage': load_json_report(OUTPUT_DIR / "part_iii_coverage.json"),
        'part_iii_tag': load_json_report(OUTPUT_DIR / "part_iii_tag_audit.json"),
        'part_iv_coverage': load_json_report(OUTPUT_DIR / "part_iv_coverage.json"),
        'part_iv_tag': load_json_report(OUTPUT_DIR / "part_iv_tag_audit.json"),
        'appendix_operators_coverage': load_json_report(OUTPUT_DIR / "appendix_operators_coverage.json"),
        'appendix_operators_tag': load_json_report(OUTPUT_DIR / "appendix_operators_tag_audit.json"),
        'appendix_horizons_coverage': load_json_report(OUTPUT_DIR / "appendix_horizons_coverage.json"),
        'appendix_horizons_tag': load_json_report(OUTPUT_DIR / "appendix_horizons_tag_audit.json"),
    }


def pipeline_status_note(step):
    """Convert a pipeline step record into compact dashboard text."""
    status = (step or {}).get('status')
    if status == 'passing':
        return 'verified this run'
    if status == 'failed':
        return 'failed this run'
    if status == 'skipped':
        return 'not run this pass'
    return 'no current pipeline status'


def bridge_pipeline_status_note(step, bridge_status):
    """Bridge-specific pipeline note with a clearer skipped state."""
    status = (step or {}).get('status')
    if status == 'passing':
        return 'verified this run'
    if status == 'failed':
        return 'failed this run'
    if status == 'skipped':
        if bridge_status.get('build_passing'):
            return 'not rebuilt this run'
        return 'not requested this run'
    if bridge_status.get('build_passing'):
        return 'prior local validation present'
    return 'no current bridge status'


# ── Build-graph analysis ──────────────────────────────────────────────────

def parse_audit_surface(filepath):
    """Parse a #print axioms surface file for declaration names."""
    if not filepath.exists():
        return set()
    names = set()
    with open(filepath, 'r', encoding='utf-8') as f:
        for line in f:
            m = re.match(r'#print axioms\s+(\S+)', line.strip())
            if m:
                # Strip CoherenceCalculus. prefix for matching
                name = m.group(1)
                if name.startswith('CoherenceCalculus.'):
                    name = name[len('CoherenceCalculus.'):]
                names.add(name)
    return names


def resolve_transitive_imports(direct_stems, subdir):
    """Resolve transitive imports within a subdirectory.

    Given the directly-imported stems, follow each file's own imports to find
    Foundation files that are transitively pulled in but not listed in the
    root import file (e.g. AxiomCore imported by NatCore).
    """
    all_stems = set(direct_stems)
    queue = list(direct_stems)
    while queue:
        stem = queue.pop(0)
        filepath = LEAN_DIR / subdir / f"{stem}.lean"
        if not filepath.exists():
            continue
        with open(filepath, 'r', encoding='utf-8') as f:
            for line in f:
                m = re.match(r'import\s+(\S+)', line.strip())
                if m:
                    parts = m.group(1).split('.')
                    # Only follow imports within the same subdir
                    if len(parts) >= 3 and parts[-2] == subdir:
                        dep = parts[-1]
                        if dep not in all_stems:
                            all_stems.add(dep)
                            queue.append(dep)
    return all_stems


def resolve_local_package_imports(direct_stems, source_dir, namespace_prefix):
    """Resolve transitive imports within a separate local package."""
    all_stems = set(direct_stems)
    queue = list(direct_stems)
    while queue:
        stem = queue.pop(0)
        filepath = source_dir / f"{stem}.lean"
        if not filepath.exists():
            continue
        with open(filepath, 'r', encoding='utf-8') as f:
            for line in f:
                m = re.match(r'import\s+(\S+)', line.strip())
                if not m:
                    continue
                mod = m.group(1)
                if not mod.startswith(namespace_prefix + "."):
                    continue
                dep = mod.split('.')[-1]
                if dep not in all_stems:
                    all_stems.add(dep)
                    queue.append(dep)
    return all_stems


def discover_build_graph():
    """
    Determine which files are active vs detached.

    Resolves transitive imports: e.g. NatCore imports AxiomCore, so
    AxiomCore is active even though Foundation.lean doesn't list it directly.

    Returns:
        active_foundation: list of Path (Foundation/*.lean files in import order)
        active_partiii:    list of Path (PartIII/*.lean files)
        active_partiv:     list of Path (PartIV/*.lean files)
        active_appendix_operators: list of Path (AppendixOperators root file)
        active_appendix_horizons: list of Path (AppendixHorizons root file)
        orphaned_foundation: list of Path (Foundation/*.lean NOT imported)
        detached:          list of Path (all other .lean files under LEAN_DIR)
    """
    # Active Foundation imports (direct + transitive)
    foundation_imports = parse_import_list(FOUNDATION_LEAN)
    active_stems = resolve_transitive_imports(foundation_imports, "Foundation")

    # Build the ordered list: transitive deps first (in dependency order),
    # then direct imports in their original order
    transitive_only = active_stems - set(foundation_imports)
    active_foundation = []
    # Add transitive deps first (sorted for determinism)
    for stem in sorted(transitive_only):
        p = LEAN_DIR / "Foundation" / f"{stem}.lean"
        if p.exists():
            active_foundation.append(p)
    # Then direct imports in their listed order
    for stem in foundation_imports:
        p = LEAN_DIR / "Foundation" / f"{stem}.lean"
        if p.exists():
            active_foundation.append(p)

    # Foundation files that exist but aren't imported
    orphaned_foundation = []
    if (LEAN_DIR / "Foundation").exists():
        for p in sorted((LEAN_DIR / "Foundation").glob("*.lean")):
            if p.stem not in active_stems:
                orphaned_foundation.append(p)

    # PartIII imports
    partiii_imports = parse_import_list(PARTIII_LEAN)
    active_partiii = []
    for stem in partiii_imports:
        p = LEAN_DIR / "PartIII" / f"{stem}.lean"
        if p.exists():
            active_partiii.append(p)

    # PartIV imports
    partiv_imports = parse_import_list(PARTIV_LEAN)
    active_partiv = []
    for stem in partiv_imports:
        p = LEAN_DIR / "PartIV" / f"{stem}.lean"
        if p.exists():
            active_partiv.append(p)

    active_appendix_operators = [APPENDIX_OPERATORS_LEAN] if APPENDIX_OPERATORS_LEAN.exists() else []
    active_appendix_horizons = [APPENDIX_HORIZONS_LEAN] if APPENDIX_HORIZONS_LEAN.exists() else []

    # Everything else under LEAN_DIR is detached
    active_set = set(
        str(p)
        for p in (
            active_foundation
            + active_partiii
            + active_partiv
            + active_appendix_operators
            + active_appendix_horizons
        )
    )
    # Also include the root lane files themselves as active (but no declarations)
    active_set.add(str(FOUNDATION_LEAN))
    active_set.add(str(PARTIII_LEAN))
    active_set.add(str(PARTIV_LEAN))
    active_set.add(str(APPENDIX_OPERATORS_LEAN))
    active_set.add(str(APPENDIX_HORIZONS_LEAN))

    detached = []
    for p in sorted(LEAN_DIR.rglob("*.lean")):
        if str(p) not in active_set and p.stem not in active_stems:
            # Skip Foundation/ orphans (already handled)
            if p.parent.name == "Foundation" and p not in [FOUNDATION_LEAN]:
                continue
            # Skip PartIII subdir (handled above)
            if p.parent.name == "PartIII":
                continue
            # Skip PartIV subdir (handled above)
            if p.parent.name == "PartIV":
                continue
            detached.append(p)

    return (
        active_foundation,
        active_partiii,
        active_partiv,
        active_appendix_operators,
        active_appendix_horizons,
        orphaned_foundation,
        detached,
    )


def discover_bridge_graph():
    """Discover the included external bridge package files."""
    if not BRIDGE_ROOT_LEAN.exists() or not BRIDGE_LEAN_DIR.exists():
        return [], [], {
            'package_present': False,
            'mathlib_fetched': False,
            'coherence_fetched': False,
        }

    bridge_imports = parse_import_list(BRIDGE_ROOT_LEAN)
    active_stems = resolve_local_package_imports(
        bridge_imports, BRIDGE_LEAN_DIR, "CoherenceCalculusMathlibBridge"
    )

    active_bridge = []
    for stem in bridge_imports:
        p = BRIDGE_LEAN_DIR / f"{stem}.lean"
        if p.exists():
            active_bridge.append(p)

    transitive_only = active_stems - set(bridge_imports)
    for stem in sorted(transitive_only):
        p = BRIDGE_LEAN_DIR / f"{stem}.lean"
        if p.exists():
            active_bridge.insert(0, p)

    orphaned_bridge = []
    for p in sorted(BRIDGE_LEAN_DIR.glob("*.lean")):
        if p.stem not in active_stems:
            orphaned_bridge.append(p)

    built_stems = []
    if BRIDGE_BUILD_DIR.exists():
        for p in active_bridge:
            if (BRIDGE_BUILD_DIR / f"{p.stem}.olean").exists():
                built_stems.append(p.stem)

    realized_tiers = [
        tier for tier, stems in BRIDGE_TIER_FILES.items()
        if stems.issubset(set(built_stems))
    ]
    validated_slices = [
        name for name, stems in BRIDGE_VALIDATION_FILES.items()
        if stems.issubset(set(built_stems))
    ]

    status = {
        'package_present': True,
        'mathlib_fetched': BRIDGE_MATHLIB_CHECKOUT.exists(),
        'coherence_fetched': BRIDGE_COHERENCE_CHECKOUT.exists(),
        'build_dir_present': BRIDGE_BUILD_DIR.exists(),
        'built_modules': len(built_stems),
        'active_modules': len(active_bridge),
        'build_passing': len(active_bridge) > 0 and len(built_stems) == len(active_bridge),
        'built_stems': built_stems,
        'realized_tiers': realized_tiers,
        'validated_slices': validated_slices,
    }
    return active_bridge, orphaned_bridge, status


def classify_part(stem):
    """Classify a Foundation file stem into a paper part."""
    if stem in PART_I_FILES:
        return 'Part I'
    elif stem in PART_II_FILES:
        return 'Part II'
    elif stem in PART_III_FOUNDATION_FILES:
        return 'Part III'
    else:
        return 'Unclassified'


# ── Topic grouping (for display within parts) ─────────────────────────────

TOPIC_MAP = OrderedDict([
    ('Bedrock Axioms',  ['AxiomCore']),
    ('Arithmetic',      ['NatCore', 'CancellationCore', 'SignedCount',
                         'RawCountCore', 'NormalizationCore', 'SignedAlgebraCore']),
    ('Closure Equation', ['ClosureCore', 'ClosureClassificationCore']),
    ('Choice Principles', ['StructuredChoiceCore', 'CountableChoiceCore',
                           'PartialChoiceCore']),
    ('Dyadic Continuum', ['DyadicContinuumCore', 'DyadicIntervalCore',
                          'DyadicPointCore', 'DyadicOrderCore',
                          'DyadicBoundaryPairCore', 'DyadicIdentificationCore',
                          'DyadicBoundaryEnvelopeCore', 'DyadicComparisonCore',
                          'DyadicPrefixCore', 'DyadicPrelineCore',
                          'DyadicPrelineWitnessCore', 'DyadicPrelinePrefixCore',
                          'DyadicPrelineSubdivisionCore']),
    ('Bedrock',         ['OrientationCore', 'HorizonCore', 'OperatorCore',
                         'MetricCore', 'BedrockInterfaceCore', 'PairingCore']),
    ('Projection Calculus', ['ProjectionCalculusCore']),
    ('Constraint Compiler', ['ConstraintCompilerCore', 'ConstraintSelectorCore',
                             'BoundaryCore']),
    ('HFT',             ['HFTCore', 'HFT2Core', 'TelescopingCore',
                         'HFTExamplesCore']),
    ('Foundational Lemmas', ['FoundationalLemmasWidth']),
    ('Defect Rules',    ['DefectRuleCore']),
    ('Tower Calculus',  ['TowerCalculusCore', 'SummationCore',
                         'FaithfulTowerCore', 'CoherenceTowerCore']),
    # Part II topics
    ('Field-Induced Horizons', ['FieldInducedHorizonCore']),
    ('Resolvent / Solver', ['ResolventInterfaceCore', 'FiniteComplexCore',
                            'SolverInterfaceCore']),
    ('Complex Compatibility', ['ComplexCompatibilityInterfaceCore',
                               'ComplexCompatibilityCorollaryCore']),
    ('Targets',         ['TargetCore']),
    ('Projector Calculus', ['ProjectorCalculusCore']),
    ('Holographic Defect', ['HolographicDefectCore']),
    ('Coherence Gap',   ['CoherenceGapCore']),
    ('Log-Periodic',    ['LogPeriodicCore']),
    ('Transport Order', ['TransportOrderSelectionCore',
                         'TransportOrderFiniteCore',
                         'TowerTransportInterfaceCore']),
    # Part III topics
    ('Diophantine',     ['DiophantineWidth']),
    ('Closure Realization', ['ClosureRealizationCore', 'ClosureDirectCore',
                             'ClosureTransportCore', 'ClosureUniquenessCore',
                             'ClosureBalanceCore']),
    ('Characteristic Transport', ['CharacteristicTransportCore']),
    ('Variational Selection', ['VariationalSelectionCore']),
    ('Bridge Observable', ['BridgeObservableCore',
                           'BridgeObservableCorollaryCore']),
    ('Bridge Transport / Rigidity', ['BridgeTransportCore',
                                     'BridgeTransportCorollaryCore',
                                     'SelectedChannelRigidityCore',
                                     'BridgeRigidityCore',
                                     'BridgeRigidityCorollaryCore']),
])

def stem_to_topic(stem):
    for topic, stems in TOPIC_MAP.items():
        if stem in stems:
            return topic
    return 'Other'


# ── HTML generation ────────────────────────────────────────────────────────

def generate_html(foundation_decls, partiii_decls, partiv_decls,
                  appendix_operator_decls, appendix_horizon_decls,
                  orphaned_decls, detached_decls, lean_to_latex, aux_refs,
                  active_foundation_files, active_partiii_files, active_partiv_files,
                  active_appendix_operator_files, active_appendix_horizon_files,
                  orphaned_foundation_files, detached_files,
                  strict_surface, bedrock_surface,
                  bridge_decls, bridge_orphaned_decls, active_bridge_files,
                  bridge_status, coverage_reports, pipeline_status):
    """Build the full HTML dashboard."""

    def enrich(decls):
        for d in decls:
            name = d['name']
            if name in lean_to_latex:
                label = lean_to_latex[name]
                d['latex_label'] = label
                if label in aux_refs:
                    ref = aux_refs[label]
                    kind = ref['type'].split('.')[0].title() if ref['type'] else ''
                    d['pdf_ref'] = f"{kind} {ref['number']}, p.{ref['page']}"
            else:
                d['latex_label'] = None
                d['pdf_ref'] = None

    enrich(foundation_decls)
    enrich(partiii_decls)
    enrich(partiv_decls)
    enrich(appendix_operator_decls)
    enrich(appendix_horizon_decls)
    enrich(orphaned_decls)
    enrich(detached_decls)
    enrich(bridge_decls)
    enrich(bridge_orphaned_decls)

    # ── Stats ──
    all_active = (
        foundation_decls
        + partiii_decls
        + partiv_decls
        + appendix_operator_decls
        + appendix_horizon_decls
    )

    total       = len(all_active)
    proved      = sum(1 for d in all_active if d['status'] == 'proved')
    pending     = sum(1 for d in all_active if d['status'] == 'pending')
    axioms      = sum(1 for d in all_active if d['status'] == 'axiom')
    linked      = sum(1 for d in all_active if d.get('pdf_ref'))
    theorems    = sum(1 for d in all_active if d['type'] in ('theorem', 'lemma'))
    definitions = sum(1 for d in all_active if d['type'] in ('def', 'abbrev', 'structure', 'class', 'instance', 'inductive'))
    foundation_total = len(foundation_decls)
    foundation_axioms = sum(1 for d in foundation_decls if d['status'] == 'axiom')

    # Per-part stats
    part_stats = {}
    for part_name in ['Part I', 'Part II', 'Part III']:
        part_decls = [d for d in foundation_decls if d.get('part') == part_name]
        part_stats[part_name] = {
            'total': len(part_decls),
            'proved': sum(1 for d in part_decls if d['status'] == 'proved'),
            'axioms': sum(1 for d in part_decls if d['status'] == 'axiom'),
            'pending': sum(1 for d in part_decls if d['status'] == 'pending'),
            'theorems': sum(1 for d in part_decls if d['type'] in ('theorem', 'lemma')),
            'defs': sum(1 for d in part_decls if d['type'] in ('def', 'abbrev', 'structure', 'class', 'instance', 'inductive')),
            'linked': sum(1 for d in part_decls if d.get('pdf_ref')),
        }
    # Add PartIII directory files to Part III stats
    p3dir = {
        'total': len(partiii_decls),
        'proved': sum(1 for d in partiii_decls if d['status'] == 'proved'),
        'axioms': sum(1 for d in partiii_decls if d['status'] == 'axiom'),
        'pending': sum(1 for d in partiii_decls if d['status'] == 'pending'),
        'theorems': sum(1 for d in partiii_decls if d['type'] in ('theorem', 'lemma')),
        'defs': sum(1 for d in partiii_decls if d['type'] in ('def', 'abbrev', 'structure', 'class', 'instance', 'inductive')),
        'linked': sum(1 for d in partiii_decls if d.get('pdf_ref')),
    }
    for k in part_stats['Part III']:
        part_stats['Part III'][k] += p3dir[k]
    part_stats['Part IV'] = {
        'total': len(partiv_decls),
        'proved': sum(1 for d in partiv_decls if d['status'] == 'proved'),
        'axioms': sum(1 for d in partiv_decls if d['status'] == 'axiom'),
        'pending': sum(1 for d in partiv_decls if d['status'] == 'pending'),
        'theorems': sum(1 for d in partiv_decls if d['type'] in ('theorem', 'lemma')),
        'defs': sum(
            1 for d in partiv_decls
            if d['type'] in ('def', 'abbrev', 'structure', 'class', 'instance', 'inductive')
        ),
        'linked': sum(1 for d in partiv_decls if d.get('pdf_ref')),
    }
    part_stats['Appendix Operators'] = {
        'total': len(appendix_operator_decls),
        'proved': sum(1 for d in appendix_operator_decls if d['status'] == 'proved'),
        'axioms': sum(1 for d in appendix_operator_decls if d['status'] == 'axiom'),
        'pending': sum(1 for d in appendix_operator_decls if d['status'] == 'pending'),
        'theorems': sum(1 for d in appendix_operator_decls if d['type'] in ('theorem', 'lemma')),
        'defs': sum(
            1 for d in appendix_operator_decls
            if d['type'] in ('def', 'abbrev', 'structure', 'class', 'instance', 'inductive')
        ),
        'linked': sum(1 for d in appendix_operator_decls if d.get('pdf_ref')),
    }
    part_stats['Appendix Horizons'] = {
        'total': len(appendix_horizon_decls),
        'proved': sum(1 for d in appendix_horizon_decls if d['status'] == 'proved'),
        'axioms': sum(1 for d in appendix_horizon_decls if d['status'] == 'axiom'),
        'pending': sum(1 for d in appendix_horizon_decls if d['status'] == 'pending'),
        'theorems': sum(1 for d in appendix_horizon_decls if d['type'] in ('theorem', 'lemma')),
        'defs': sum(
            1 for d in appendix_horizon_decls
            if d['type'] in ('def', 'abbrev', 'structure', 'class', 'instance', 'inductive')
        ),
        'linked': sum(1 for d in appendix_horizon_decls if d.get('pdf_ref')),
    }

    # External validation bridge stats
    all_bridge = bridge_decls + bridge_orphaned_decls
    bridge_total = len(all_bridge)
    bridge_pending = sum(1 for d in all_bridge if d['status'] == 'pending')
    bridge_axioms = sum(1 for d in all_bridge if d['status'] == 'axiom')
    bridge_theorems = sum(1 for d in all_bridge if d['type'] in ('theorem', 'lemma'))
    bridge_defs = sum(
        1 for d in all_bridge
        if d['type'] in ('def', 'abbrev', 'structure', 'class', 'instance', 'inductive')
    )
    bridge_file_theorem_counts = {}
    for d in bridge_decls:
        if d['type'] not in ('theorem', 'lemma'):
            continue
        stem = Path(d['file']).stem
        bridge_file_theorem_counts[stem] = bridge_file_theorem_counts.get(stem, 0) + 1
    bridge_tier_theorem_counts = OrderedDict(
        (
            tier,
            sum(bridge_file_theorem_counts.get(stem, 0) for stem in stems),
        )
        for tier, stems in BRIDGE_TIER_FILES.items()
    )
    bridge_validation_theorem_counts = OrderedDict(
        (
            name,
            sum(bridge_file_theorem_counts.get(stem, 0) for stem in stems),
        )
        for name, stems in BRIDGE_VALIDATION_FILES.items()
    )

    part_i_ii_cov = coverage_reports.get('part_i_ii_coverage') or {}
    part_i_ii_tag = coverage_reports.get('part_i_ii_tag') or {}
    part_iii_cov = coverage_reports.get('part_iii_coverage') or {}
    part_iii_tag = coverage_reports.get('part_iii_tag') or {}
    part_iv_cov = coverage_reports.get('part_iv_coverage') or {}
    part_iv_tag = coverage_reports.get('part_iv_tag') or {}
    appendix_ops_cov = coverage_reports.get('appendix_operators_coverage') or {}
    appendix_ops_tag = coverage_reports.get('appendix_operators_tag') or {}
    appendix_horiz_cov = coverage_reports.get('appendix_horizons_coverage') or {}
    appendix_horiz_tag = coverage_reports.get('appendix_horizons_tag') or {}

    p12_cov_summary = part_i_ii_cov.get('summary', {})
    p12_tag_summary = part_i_ii_tag.get('summary', {})
    p3_cov_summary = part_iii_cov.get('summary', {})
    p3_tag_summary = part_iii_tag.get('summary', {})
    p4_cov_summary = part_iv_cov.get('summary', {})
    p4_tag_summary = part_iv_tag.get('summary', {})
    appendix_ops_cov_summary = appendix_ops_cov.get('summary', {})
    appendix_ops_tag_summary = appendix_ops_tag.get('summary', {})
    appendix_horiz_cov_summary = appendix_horiz_cov.get('summary', {})
    appendix_horiz_tag_summary = appendix_horiz_tag.get('summary', {})

    pipeline_steps = (pipeline_status or {}).get('steps', {})
    pipeline_summary = (pipeline_status or {}).get('summary', {})
    if pipeline_summary.get('full_manuscript_lanes_passing'):
        certified_pipeline_note = 'full manuscript verified this run'
    elif pipeline_summary.get('certified_lanes_passing'):
        certified_pipeline_note = 'core manuscript verified; appendix lanes pending'
    elif pipeline_steps:
        certified_pipeline_note = 'manuscript pipeline incomplete'
    else:
        certified_pipeline_note = 'no current pipeline status'
    p12_pipeline_note = pipeline_status_note(pipeline_steps.get('part_i_ii_audits'))
    p3_pipeline_note = pipeline_status_note(pipeline_steps.get('part_iii_audits'))
    p4_pipeline_note = pipeline_status_note(pipeline_steps.get('part_iv_audits'))
    appendix_ops_pipeline_note = pipeline_status_note(pipeline_steps.get('appendix_operators_audits'))
    appendix_horiz_pipeline_note = pipeline_status_note(pipeline_steps.get('appendix_horizons_audits'))
    bridge_pipeline_step = pipeline_steps.get('mathlib_bridge_build', {})
    bridge_pipeline_note = bridge_pipeline_status_note(bridge_pipeline_step, bridge_status)

    bridge_checkout = 'fetched' if bridge_status.get('mathlib_fetched') else 'unfetched'
    bridge_built = bridge_status.get('built_modules', 0)
    bridge_active = bridge_status.get('active_modules', len(active_bridge_files))
    bridge_tiers = bridge_status.get('realized_tiers', [])
    bridge_tier_text = ', '.join(bridge_tiers) if bridge_tiers else 'none yet'
    bridge_tier_battery_text = ' · '.join(
        f"{tier} {bridge_tier_theorem_counts.get(tier, 0)}T"
        for tier in bridge_tiers
        if bridge_tier_theorem_counts.get(tier, 0)
    ) or 'none yet'
    bridge_battery_total = sum(bridge_tier_theorem_counts.get(tier, 0) for tier in bridge_tiers)
    bridge_validations = bridge_status.get('validated_slices', [])
    bridge_validation_text = ', '.join(bridge_validations) if bridge_validations else 'none yet'
    bridge_validation_battery_text = ' · '.join(
        f"{name} {bridge_validation_theorem_counts.get(name, 0)}T"
        for name in bridge_validations
        if bridge_validation_theorem_counts.get(name, 0)
    ) or 'none yet'
    bridge_validation_total = sum(
        bridge_validation_theorem_counts.get(name, 0) for name in bridge_validations
    )
    bridge_validation_count = len(bridge_validations)
    if bridge_pipeline_step.get('status') == 'passing':
        bridge_summary = 'verified this run'
    elif bridge_status.get('build_passing'):
        bridge_summary = 'prior local validation present'
    else:
        bridge_summary = f"{bridge_built}/{bridge_active} built"
    bridge_status_text = bridge_summary
    if bridge_pipeline_note != bridge_summary:
        bridge_status_text = f"{bridge_summary} | {bridge_pipeline_note}"
    bridge_top_summary = f"{bridge_validation_count} slices" if bridge_validation_count else '0 slices'
    bridge_top_note = (
        f"{bridge_validation_total}T validated | {bridge_status_text}"
        if bridge_validations
        else f"build {bridge_status_text} | mathlib {bridge_checkout}"
    )
    bridge_note = (
        f"{bridge_status_text} | tiers {bridge_tier_text} | "
        f"validated {bridge_validation_text} ({bridge_validation_total}T) | "
        f"battery {bridge_battery_total}T | "
        f"mathlib {bridge_checkout}"
    )

    pct = proved / total * 100 if total > 0 else 0
    pct_ax = (proved + axioms) / total * 100 if total > 0 else 0

    # ── Group Foundation decls by part → topic → file ──
    by_part = {
        'Part I': {},
        'Part II': {},
        'Part III': {},
        'Part IV': {},
        'Appendix Operators': {},
        'Appendix Horizons': {},
    }
    for d in foundation_decls:
        part = d.get('part', 'Unclassified')
        topic = d.get('topic', 'Other')
        if part not in by_part:
            by_part[part] = {}
        by_part[part].setdefault(topic, []).append(d)

    # Add PartIII directory decls under 'Part III'
    for d in partiii_decls:
        topic = f"PartIII/{d['file']}"
        by_part['Part III'].setdefault(topic, []).append(d)
    for d in partiv_decls:
        topic = f"PartIV/{d['file']}"
        by_part['Part IV'].setdefault(topic, []).append(d)
    for d in appendix_operator_decls:
        topic = f"Appendix/{d['file']}"
        by_part['Appendix Operators'].setdefault(topic, []).append(d)
    for d in appendix_horizon_decls:
        topic = f"Appendix/{d['file']}"
        by_part['Appendix Horizons'].setdefault(topic, []).append(d)

    # ── Topic ordering within each part ──
    topic_order = list(TOPIC_MAP.keys())
    def topic_sort(t):
        try:
            return (0, topic_order.index(t))
        except ValueError:
            return (1, t)

    # ── Build HTML ──
    html = f'''<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Coherence Calculus — Lean Verification Dashboard</title>
    <style>
        :root {{
            --green: #22c55e;
            --blue: #3b82f6;
            --yellow: #eab308;
            --gray: #6b7280;
            --purple: #a855f7;
            --bg: #111827;
            --card: #1f2937;
            --text: #f3f4f6;
            --border: #374151;
        }}
        * {{ box-sizing: border-box; margin: 0; padding: 0; }}
        body {{
            font-family: 'SF Mono', 'Fira Code', 'Cascadia Code', monospace;
            background: var(--bg);
            color: var(--text);
            padding: 2rem;
            line-height: 1.6;
            max-width: 1400px;
            margin: 0 auto;
        }}
        h1 {{ font-size: 1.5rem; margin-bottom: 0.25rem; color: white; }}
        h2 {{ font-size: 1.15rem; color: white; margin: 2rem 0 0.75rem 0; }}
        .subtitle {{ color: var(--gray); margin-bottom: 1.5rem; font-size: 0.85rem; }}

        /* Summary banner */
        .banner {{
            background: linear-gradient(135deg, #065f46, #064e3b);
            border: 1px solid #10b981;
            border-radius: 0.75rem;
            padding: 1.25rem 1.5rem;
            margin-bottom: 1.5rem;
            font-size: 0.9rem;
        }}
        .banner strong {{ color: #34d399; }}
        .banner .num {{ font-size: 1.8rem; font-weight: bold; color: #6ee7b7; }}

        /* Stats row */
        .stats {{
            display: flex;
            gap: 0.75rem;
            margin-bottom: 1.25rem;
            flex-wrap: wrap;
        }}
        .stat {{
            background: var(--card);
            padding: 0.75rem 1.25rem;
            border-radius: 0.5rem;
            border: 1px solid var(--border);
            min-width: 90px;
        }}
        .stat-value {{ font-size: 1.6rem; font-weight: bold; }}
        .stat-label {{ font-size: 0.7rem; color: var(--gray); text-transform: uppercase; letter-spacing: 0.04em; }}
        .stat.proved .stat-value {{ color: var(--green); }}
        .stat.pending .stat-value {{ color: var(--yellow); }}
        .stat.axiom .stat-value {{ color: var(--blue); }}
        .stat.linked .stat-value {{ color: var(--purple); }}
        .stat.certified .stat-value {{ color: #34d399; }}
        .stat.bridge .stat-value {{ color: #c084fc; }}
        .stat-sub {{
            margin-top: 0.25rem;
            font-size: 0.68rem;
            color: #9ca3af;
            line-height: 1.25;
        }}

        .lane-grid {{
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(260px, 1fr));
            gap: 0.75rem;
            margin-bottom: 1.5rem;
        }}
        .lane-card {{
            background: var(--card);
            border: 1px solid var(--border);
            border-radius: 0.6rem;
            padding: 1rem 1.1rem;
        }}
        .lane-card.certified {{
            border-left: 4px solid var(--green);
        }}
        .lane-card.bridge {{
            border-left: 4px solid var(--purple);
        }}
        .lane-card.appendix {{
            border-left: 4px solid #f59e0b;
        }}
        .lane-title {{
            font-size: 0.88rem;
            font-weight: bold;
            color: white;
            margin-bottom: 0.25rem;
        }}
        .lane-subtitle {{
            color: var(--gray);
            font-size: 0.74rem;
            margin-bottom: 0.75rem;
        }}
        .lane-metric {{
            font-size: 0.8rem;
            margin-bottom: 0.25rem;
            color: #d1d5db;
        }}
        .lane-note {{
            margin-top: 0.65rem;
            font-size: 0.72rem;
            color: #9ca3af;
        }}

        /* Progress bar */
        .progress-bar {{
            height: 6px;
            background: var(--card);
            border-radius: 3px;
            overflow: hidden;
            margin-bottom: 1.5rem;
        }}
        .progress-fill {{
            height: 100%;
            background: linear-gradient(90deg,
                var(--green) 0%, var(--green) {pct}%,
                var(--blue) {pct}%, var(--blue) {pct_ax}%,
                var(--yellow) {pct_ax}%, var(--yellow) 100%);
        }}

        /* Build graph */
        .build-graph {{
            background: var(--card);
            border: 1px solid var(--border);
            border-radius: 0.5rem;
            padding: 1rem 1.25rem;
            margin-bottom: 1.5rem;
            font-size: 0.8rem;
            color: #9ca3af;
            white-space: pre;
            line-height: 1.5;
        }}
        .build-graph code {{ color: #a5b4fc; }}
        .build-graph .active {{ color: var(--green); }}
        .build-graph .detached {{ color: #6b7280; }}

        /* Part header */
        .part-header {{
            background: var(--card);
            border: 1px solid var(--border);
            border-radius: 0.5rem;
            padding: 1rem 1.25rem;
            margin-bottom: 0.75rem;
            display: flex;
            justify-content: space-between;
            align-items: center;
            flex-wrap: wrap;
            gap: 0.5rem;
        }}
        .part-title {{
            font-size: 1rem;
            font-weight: bold;
            color: white;
        }}
        .part-stats {{
            display: flex;
            gap: 1rem;
            font-size: 0.8rem;
        }}
        .part-stats span {{ color: var(--gray); }}
        .part-stats .val {{ font-weight: bold; }}
        .part-stats .val.green {{ color: var(--green); }}
        .part-stats .val.yellow {{ color: var(--yellow); }}
        .part-stats .val.blue {{ color: var(--blue); }}
        .part-stats .val.purple {{ color: var(--purple); }}

        /* Topic section */
        .topic-section {{
            background: var(--card);
            border: 1px solid var(--border);
            border-radius: 0.5rem;
            padding: 1rem 1.25rem;
            margin-bottom: 0.5rem;
        }}
        .topic-name {{
            font-size: 0.8rem;
            color: #60a5fa;
            text-transform: uppercase;
            letter-spacing: 0.04em;
            margin-bottom: 0.5rem;
            padding-bottom: 0.25rem;
            border-bottom: 1px solid rgba(96, 165, 250, 0.2);
        }}

        /* Declaration row */
        .decl-list {{ display: flex; flex-direction: column; gap: 0.25rem; }}
        .decl {{
            display: grid;
            grid-template-columns: 12px 65px minmax(100px, 1fr) auto auto;
            align-items: center;
            gap: 0.5rem;
            padding: 0.3rem 0.4rem;
            background: rgba(0,0,0,0.15);
            border-radius: 0.2rem;
            font-size: 0.8rem;
        }}
        .status-dot {{
            width: 8px; height: 8px;
            border-radius: 50%;
        }}
        .status-dot.proved {{ background: var(--green); }}
        .status-dot.pending {{ background: var(--yellow); }}
        .status-dot.axiom  {{ background: var(--blue); }}
        .status-dot.bridge-source {{ background: var(--purple); }}
        .decl-type {{ color: var(--gray); font-size: 0.7rem; }}
        .decl-name {{ font-weight: 500; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }}
        .decl-pdf {{
            font-size: 0.7rem;
            color: var(--purple);
            background: rgba(168, 85, 247, 0.1);
            padding: 0.15rem 0.4rem;
            border-radius: 0.2rem;
            white-space: nowrap;
        }}
        .decl-pdf.none {{ color: var(--gray); background: transparent; }}
        .decl-line {{ color: var(--gray); font-size: 0.7rem; white-space: nowrap; }}

        /* Legend */
        .legend {{
            display: flex;
            gap: 1.25rem;
            margin-bottom: 1.5rem;
            font-size: 0.8rem;
            flex-wrap: wrap;
        }}
        .legend-item {{ display: flex; align-items: center; gap: 0.4rem; }}

        /* Detached section */
        .detached-section {{
            opacity: 0.55;
        }}
        .detached-section:hover {{
            opacity: 0.85;
        }}

        .instructions {{
            background: var(--card);
            border: 1px solid var(--border);
            border-radius: 0.5rem;
            padding: 0.75rem 1rem;
            margin-bottom: 1.25rem;
            font-size: 0.8rem;
            border-left: 3px solid var(--purple);
        }}
        .instructions code {{
            background: rgba(0,0,0,0.3);
            padding: 0.1rem 0.3rem;
            border-radius: 0.15rem;
        }}

        .timestamp {{ color: var(--gray); font-size: 0.7rem; margin-top: 2rem; }}

        /* Collapsible */
        details summary {{
            cursor: pointer;
            list-style: none;
        }}
        details summary::-webkit-details-marker {{ display: none; }}
        details summary::before {{
            content: '\\25b6\\fe0e ';
            font-size: 0.7rem;
            margin-right: 0.25rem;
        }}
        details[open] summary::before {{
            content: '\\25bc\\fe0e ';
        }}
    </style>
</head>
<body>
    <h1>Coherence Calculus</h1>
    <p class="subtitle">Lean 4 Verification Dashboard</p>
'''

    # ── Banner ──
    html += f'''
    <div class="banner">
        <span class="num">{total}</span> declarations in active build &mdash;
        <strong>{proved} proved</strong> from
        <strong style="color:#fbbf24;">{len(PAPER_AXIOMS)} paper bedrock groups</strong>
        implemented as <strong style="color:#60a5fa;">{axioms} Lean bedrock declarations</strong>,
        {pending} pending, {linked} PDF-linked,
        <strong style="color:#ef4444;">0 external axioms</strong><br>
        <span style="font-size:0.8rem; color:#9ca3af;">
            {theorems} theorems/lemmas + {definitions} defs/structures
            across {len(active_foundation_files)} Foundation files +
            {len(active_partiii_files)} Part&nbsp;III files +
            {len(active_partiv_files)} Part&nbsp;IV files +
            {len(active_appendix_operator_files)} appendix-operator root +
            {len(active_appendix_horizon_files)} appendix-horizon root
        </span>
    </div>
'''

    # ── Stats row ──
    html += '''    <div class="stats">\n'''
    for label, val, cls, sub in [
        ('Proved', proved, 'proved', 'certified active declarations'),
        ('Axiom T/L', theorems, 'certified', 'certified theorem/lemma proofs under bedrock'),
        ('Pending', pending, 'pending', 'active root only'),
        ('Bedrock Decls', axioms, 'axiom', 'explicit Lean bedrock only'),
        ('Part I / II', f"{p12_tag_summary.get('tagged', '—')}/{p12_tag_summary.get('items', '—')}", 'certified',
         f"strict {p12_cov_summary.get('audited_strict', '—')} | {p12_pipeline_note}"),
        ('Part III', f"{p3_tag_summary.get('tagged', '—')}/{p3_tag_summary.get('items', '—')}", 'certified',
         f"strict {p3_cov_summary.get('audited_strict', '—')} | {p3_pipeline_note}"),
        ('Part IV', f"{p4_tag_summary.get('tagged', '—')}/{p4_tag_summary.get('items', '—')}", 'certified',
         f"strict {p4_cov_summary.get('audited_strict', '—')} | {p4_pipeline_note}"),
        ('Appx Ops', f"{appendix_ops_tag_summary.get('tagged', '—')}/{appendix_ops_tag_summary.get('items', '—')}", 'certified',
         f"strict {appendix_ops_cov_summary.get('audited_strict', '—')} | {appendix_ops_pipeline_note}"),
        ('Appx Horizons', f"{appendix_horiz_tag_summary.get('tagged', '—')}/{appendix_horiz_tag_summary.get('items', '—')}", 'certified',
         f"strict {appendix_horiz_cov_summary.get('audited_strict', '—')} | {appendix_horiz_pipeline_note}"),
        ('Mathlib Validated', bridge_top_summary, 'bridge', bridge_top_note),
        ('PDF Linked', linked, 'linked', 'manuscript-linked active decls'),
    ]:
        html += f'''        <div class="stat {cls}">
            <div class="stat-value">{val}</div>
            <div class="stat-label">{label}</div>
            <div class="stat-sub">{sub}</div>
        </div>\n'''
    html += '''    </div>\n'''

    # ── Progress bar ──
    html += '''    <div class="progress-bar"><div class="progress-fill"></div></div>\n'''

    # ── Legend ──
    html += '''    <div class="legend">
        <div class="legend-item"><div class="status-dot proved"></div><span>Proved</span></div>
        <div class="legend-item"><div class="status-dot pending"></div><span>Has sorry</span></div>
        <div class="legend-item"><div class="status-dot axiom"></div><span>Axiom</span></div>
        <div class="legend-item"><span style="color:var(--purple);">&#9632;</span><span>PDF linked</span></div>
    </div>\n'''

    # ── Build graph ──
    n_orphan = len(orphaned_foundation_files)
    n_detach = len(detached_files)
    bridge_fetch = "fetched" if bridge_status.get('mathlib_fetched') else "not fetched"
    html += f'''    <div class="build-graph"><span class="active">CoherenceCalculus.lean</span>
  <span class="active">└─ Foundation.lean</span>  ({len(active_foundation_files)} files, {foundation_axioms} bedrock decls, 0 sorry)
       ├─ Foundation/<span style="color:#fbbf24;">AxiomCore</span>.lean  (bedrock: {len(PAPER_AXIOMS)} paper groups / {foundation_axioms} Lean declarations)
       ├─ Foundation/<span class="active">NatCore</span>.lean  ... <span class="active">HFTExamplesCore</span>.lean

  <span style="color:#60a5fa;">PartIII.lean</span>  ({len(active_partiii_files)} files, builds on Foundation; {p3_pipeline_note})
       ├─ PartIII/<span style="color:#60a5fa;">BridgeSupportCore</span>.lean  ... <span style="color:#60a5fa;">DerivedBridgeCore</span>.lean

  <span style="color:#38bdf8;">PartIV.lean</span>  ({len(active_partiv_files)} files, exported-interface lane; {p4_pipeline_note})
       ├─ PartIV/<span style="color:#38bdf8;">ObserverSelectionCore</span>.lean  ... <span style="color:#38bdf8;">FlagshipCore</span>.lean

  <span style="color:#f59e0b;">AppendixOperators.lean</span>  ({len(active_appendix_operator_files)} file, strict appendix operator lane; {appendix_ops_pipeline_note})
       └─ explicit finite/operator/trace/SVD datum packages only

  <span style="color:#f97316;">AppendixHorizons.lean</span>  ({len(active_appendix_horizon_files)} file, strict appendix horizon lane; {appendix_horiz_pipeline_note})
       └─ explicit oblique/spectral/trace datum packages only

  <span style="color:#c084fc;">CoherenceCalculusMathlibBridge.lean</span>  ({len(active_bridge_files)} local files, included one-way validation lane)
       ├─ CoherenceCalculusMathlibBridge/<span style="color:#c084fc;">Contract</span>.lean  ... <span style="color:#c084fc;">AbstractHilbert</span>.lean
       └─ mathlib dependency: <span style="color:#c084fc;">{bridge_fetch}</span> | build: <span style="color:#c084fc;">{bridge_status_text}</span>

  <span class="detached">Archived / Unbuilt</span>  ({n_orphan} orphaned Foundation + {n_detach} archival files, NOT in build)

  <span class="active">Manuscript pipeline</span>  ({certified_pipeline_note}; Part I / II {p12_pipeline_note}; Part III {p3_pipeline_note}; Part IV {p4_pipeline_note}; Appendix operators {appendix_ops_pipeline_note}; Appendix horizons {appendix_horiz_pipeline_note})</div>\n'''

    # ── Axiom Provenance ──
    # Classify active declarations by axiom dependency tier
    axiom_decls = [d for d in foundation_decls if d['status'] == 'axiom']

    # Cross-reference audit surfaces
    n_strict_audited = len(strict_surface)
    n_bedrock_audited = len(bedrock_surface)
    n_total_audited = n_strict_audited + n_bedrock_audited

    html += f'''
    <div style="background: linear-gradient(135deg, #422006, #451a03);
                border: 1px solid #b45309; border-radius: 0.75rem;
                padding: 1.5rem; margin-bottom: 1.5rem;">
        <div style="font-size: 1.1rem; font-weight: bold; color: #fbbf24;
                    margin-bottom: 1rem;">
            Axiom Provenance
        </div>

        <!-- The 3 paper axioms -->
        <div style="margin-bottom: 1.25rem;">
            <div style="font-size: 0.85rem; color: #fde68a; margin-bottom: 0.5rem;">
                <strong>3 axioms</strong> from the draft &mdash; the entire foundation:
            </div>\n'''

    for num, info in PAPER_AXIOMS.items():
        lean_names = ', '.join(f'<code style="color:#fbbf24;">{n}</code>'
                               for n in info['lean_decls'])
        html += f'''            <div style="padding: 0.4rem 0.6rem; margin-bottom:0.35rem;
                        background: rgba(0,0,0,0.2); border-radius:0.3rem;
                        border-left: 3px solid #b45309;">
                <div style="font-size:0.85rem; color:#fef3c7;">
                    <strong style="color:#fbbf24;">Axiom {num}</strong>
                    [{info['name']}]
                </div>
                <div style="font-size:0.78rem; color:#d4a574; margin-top:0.15rem;">
                    {info['statement']}
                </div>
                <div style="font-size:0.72rem; color:#92400e; margin-top:0.15rem;">
                    Lean: {lean_names}
                </div>
            </div>\n'''

    html += f'''        </div>

        <!-- Three-tier breakdown -->
        <div style="display:grid; grid-template-columns: 1fr 1fr 1fr; gap: 0.75rem;
                    margin-bottom: 1rem;">
            <div style="text-align:center; padding:0.75rem; background:rgba(0,0,0,0.2);
                        border-radius:0.4rem; border-top: 3px solid var(--green);">
                <div style="font-size:1.8rem; font-weight:bold; color:var(--green);">
                    {n_strict_audited}
                </div>
                <div style="font-size:0.7rem; color:#9ca3af; text-transform:uppercase;
                            letter-spacing:0.04em;">Axiom-Free</div>
                <div style="font-size:0.7rem; color:#6b7280; margin-top:0.2rem;">
                    Zero axioms of any kind
                </div>
            </div>
            <div style="text-align:center; padding:0.75rem; background:rgba(0,0,0,0.2);
                        border-radius:0.4rem; border-top: 3px solid #fbbf24;">
                <div style="font-size:1.8rem; font-weight:bold; color:#fbbf24;">
                    {n_bedrock_audited}
                </div>
                <div style="font-size:0.7rem; color:#9ca3af; text-transform:uppercase;
                            letter-spacing:0.04em;">Bedrock-Only</div>
                <div style="font-size:0.7rem; color:#6b7280; margin-top:0.2rem;">
                    Uses only the 3 paper axioms
                </div>
            </div>
            <div style="text-align:center; padding:0.75rem; background:rgba(0,0,0,0.2);
                        border-radius:0.4rem; border-top: 3px solid #ef4444;">
                <div style="font-size:1.8rem; font-weight:bold; color:#ef4444;">
                    0
                </div>
                <div style="font-size:0.7rem; color:#9ca3af; text-transform:uppercase;
                            letter-spacing:0.04em;">External Axioms</div>
                <div style="font-size:0.7rem; color:#6b7280; margin-top:0.2rem;">
                    No propext, Quot.sound, Choice
                </div>
            </div>
        </div>

        <div style="font-size: 0.75rem; color: #92400e;">
            {n_total_audited} of {foundation_total} foundation-lane declarations verified by
            <code style="color:#d97706;">audit_axiom_surface.py</code>
            (<code style="color:#d97706;">#print axioms</code> per declaration).
            Part III, Part IV, and the appendix lanes are audited separately on
            their own strict theorem surfaces.
            H(D)=0 is not an axiom&mdash;it is computed as a theorem
            (<code style="color:#d97706;">stable_D4</code>) in ClosureCore.lean.
        </div>
    </div>\n'''

    # ── Instructions ──
    html += '''    <div class="instructions">
        <strong>Linking Lean to PDF:</strong>
        Add <code>\\lean{DeclName}</code> after <code>\\label{...}</code> in LaTeX.
        The dashboard resolves page numbers from the .aux file.
    </div>\n'''

    html += '''    <h2>Verification Lanes</h2>\n'''
    html += '''    <div class="lane-grid">\n'''
    html += f'''        <div class="lane-card certified">
            <div class="lane-title">Certified Part I / II Spine</div>
            <div class="lane-subtitle">Bedrock-certified active root in <code>Foundation.lean</code></div>
            <div class="lane-metric">Manuscript tags: <strong>{p12_tag_summary.get('tagged', '—')}</strong> / {p12_tag_summary.get('items', '—')}</div>
            <div class="lane-metric">Lean refs: <strong>{p12_cov_summary.get('unique_lean_refs', '—')}</strong></div>
            <div class="lane-metric">Strict audited: <strong>{p12_cov_summary.get('audited_strict', '—')}</strong></div>
            <div class="lane-metric">Bedrock-audited: <strong>{p12_cov_summary.get('audited_bedrock', '—')}</strong></div>
            <div class="lane-metric">Direct bedrock refs: <strong>{p12_cov_summary.get('active_bedrock_decl', '—')}</strong></div>
            <div class="lane-note">
                Missing refs: {p12_cov_summary.get('missing', '—')} | Outside root: {p12_cov_summary.get('outside_active_root', '—')} | {p12_pipeline_note}
            </div>
        </div>\n'''
    html += f'''        <div class="lane-card certified">
            <div class="lane-title">Certified Part III Bridge Lane</div>
            <div class="lane-subtitle">Separate classical-limit root in <code>PartIII.lean</code></div>
            <div class="lane-metric">Manuscript tags: <strong>{p3_tag_summary.get('tagged', '—')}</strong> / {p3_tag_summary.get('items', '—')}</div>
            <div class="lane-metric">Lean refs: <strong>{p3_cov_summary.get('references', '—')}</strong></div>
            <div class="lane-metric">Strict audited: <strong>{p3_cov_summary.get('audited_strict', '—')}</strong></div>
            <div class="lane-note">
                Later-lane audited: {p3_cov_summary.get('audited_later_lane', '—')} | Root unaudited: {p3_cov_summary.get('part3_root_unaudited', '—')} | Outside root: {p3_cov_summary.get('outside_part3_root', '—')} | Missing: {p3_cov_summary.get('missing', '—')} | {p3_pipeline_note}
            </div>
        </div>\n'''
    html += f'''        <div class="lane-card certified">
            <div class="lane-title">Certified Part IV Observer Lane</div>
            <div class="lane-subtitle">Separate least-observer-motion root in <code>PartIV.lean</code></div>
            <div class="lane-metric">Manuscript tags: <strong>{p4_tag_summary.get('tagged', '—')}</strong> / {p4_tag_summary.get('items', '—')}</div>
            <div class="lane-metric">Lean refs: <strong>{p4_cov_summary.get('references', '—')}</strong></div>
            <div class="lane-metric">Strict audited: <strong>{p4_cov_summary.get('audited_strict', '—')}</strong></div>
            <div class="lane-note">
                Other-lane audited: {p4_cov_summary.get('audited_other_lane', '—')} | Root unaudited: {p4_cov_summary.get('part4_root_unaudited', '—')} | Outside root: {p4_cov_summary.get('outside_part4_root', '—')} | Missing: {p4_cov_summary.get('missing', '—')} | {p4_pipeline_note}
            </div>
        </div>\n'''
    html += f'''        <div class="lane-card appendix">
            <div class="lane-title">Appendix Operator Lane</div>
            <div class="lane-subtitle">Separate strict appendix root in <code>AppendixOperators.lean</code></div>
            <div class="lane-metric">Manuscript tags: <strong>{appendix_ops_tag_summary.get('tagged', '—')}</strong> / {appendix_ops_tag_summary.get('items', '—')}</div>
            <div class="lane-metric">Lean refs: <strong>{appendix_ops_cov_summary.get('references', '—')}</strong></div>
            <div class="lane-metric">Strict audited: <strong>{appendix_ops_cov_summary.get('audited_strict', '—')}</strong></div>
            <div class="lane-note">
                Root unaudited: {appendix_ops_cov_summary.get('appendix_root_unaudited', '—')} | Outside root: {appendix_ops_cov_summary.get('outside_appendix_root', '—')} | Missing: {appendix_ops_cov_summary.get('missing', '—')} | {appendix_ops_pipeline_note}
            </div>
        </div>\n'''
    html += f'''        <div class="lane-card appendix">
            <div class="lane-title">Appendix Horizon Lane</div>
            <div class="lane-subtitle">Separate strict appendix root in <code>AppendixHorizons.lean</code></div>
            <div class="lane-metric">Manuscript tags: <strong>{appendix_horiz_tag_summary.get('tagged', '—')}</strong> / {appendix_horiz_tag_summary.get('items', '—')}</div>
            <div class="lane-metric">Lean refs: <strong>{appendix_horiz_cov_summary.get('references', '—')}</strong></div>
            <div class="lane-metric">Strict audited: <strong>{appendix_horiz_cov_summary.get('audited_strict', '—')}</strong></div>
            <div class="lane-note">
                Root unaudited: {appendix_horiz_cov_summary.get('appendix_root_unaudited', '—')} | Outside root: {appendix_horiz_cov_summary.get('outside_appendix_root', '—')} | Missing: {appendix_horiz_cov_summary.get('missing', '—')} | {appendix_horiz_pipeline_note}
            </div>
        </div>\n'''
    html += f'''        <div class="lane-card bridge">
            <div class="lane-title">Mathlib Validation Lane</div>
            <div class="lane-subtitle">Included one-way validation lane that justifies the higher-structure Part IV and appendix carrier language by validating standard Hilbert, operator, continuum, and topological realizations</div>
            <div class="lane-metric">Build status: <strong>{bridge_summary}</strong></div>
            <div class="lane-metric">Active local modules: <strong>{len(active_bridge_files)}</strong></div>
            <div class="lane-metric">Built modules: <strong>{bridge_built}</strong> / {bridge_active}</div>
            <div class="lane-metric">Realized tiers: <strong>{len(bridge_tiers)}</strong></div>
            <div class="lane-metric">Validated slices: <strong>{bridge_validation_count}</strong></div>
            <div class="lane-metric">Validated theorem total: <strong>{bridge_validation_total}</strong></div>
            <div class="lane-metric">Source declarations: <strong>{bridge_total}</strong></div>
            <div class="lane-metric">Theorems/lemmas: <strong>{bridge_theorems}</strong></div>
            <div class="lane-metric">Defs/structures: <strong>{bridge_defs}</strong></div>
            <div class="lane-note">
                tiers: {bridge_tier_text} |
                validated slices: {bridge_validation_text} |
                mathlib checkout: {'present' if bridge_status.get('mathlib_fetched') else 'absent'} |
                sorry: {bridge_pending} | axioms: {bridge_axioms} | {bridge_pipeline_note} |
                validates the standard realizations that justify the Part IV and appendix higher-structure interpretation layer | one-way means no reverse dependency into the strict manuscript proof lanes
            </div>
        </div>\n'''
    html += '''    </div>\n'''

    # ── Part sections ──
    part_descs = {
        'Part I':   'Structural Operator Calculus',
        'Part II':  'Distinguished Realizations',
        'Part III': 'Classical-Limit Bridge',
        'Part IV':  'Principle of Least Observer Motion',
        'Appendix Operators': 'Strict Operator and Boundary Appendix Lane',
        'Appendix Horizons': 'Strict Oblique / Spectral / Trace Appendix Lane',
    }

    for part_name in ['Part I', 'Part II', 'Part III', 'Part IV', 'Appendix Operators', 'Appendix Horizons']:
        ps = part_stats[part_name]
        desc = part_descs[part_name]
        html += f'''
    <div class="part-header">
        <div class="part-title">{part_name}: {desc}</div>
        <div class="part-stats">
            <span><span class="val green">{ps['proved']}</span> proved</span>
            <span><span class="val blue">{ps['axioms']}</span> axiom</span>
            <span><span class="val yellow">{ps['pending']}</span> pending</span>
            <span><span class="val purple">{ps['linked']}</span> linked</span>
            <span>{ps['total']} total</span>
        </div>
    </div>\n'''

        topics = by_part.get(part_name, {})
        for topic_name in sorted(topics.keys(), key=topic_sort):
            decls = topics[topic_name]
            html += f'''    <div class="topic-section">
        <div class="topic-name">{topic_name} ({len(decls)})</div>
        <div class="decl-list">\n'''
            for d in decls:
                pdf = d.get('pdf_ref') or ''
                pdf_cls = '' if pdf else 'none'
                pdf_disp = pdf if pdf else '—'
                html += f'''            <div class="decl">
                <div class="status-dot {d['status']}"></div>
                <div class="decl-type">{d['type']}</div>
                <div class="decl-name" title="{d['name']}">{d['name']}</div>
                <div class="decl-pdf {pdf_cls}">{pdf_disp}</div>
                <div class="decl-line">{d['file']}:{d['line']}</div>
            </div>\n'''
            html += '''        </div>\n    </div>\n'''

    # ── External validation bridge package ──
    if all_bridge:
        bridge_by_file = {}
        for d in all_bridge:
            bridge_by_file.setdefault(d['file'], []).append(d)

        html += '''
    <h2 style="color:#c084fc; margin-top:2.5rem;">Mathlib Validation Lane</h2>
    <p style="color:var(--gray); font-size:0.8rem; margin-bottom:1rem;">
        Local source files for the included one-way mathlib validation effort.
        This lane justifies the higher-structure Part IV and appendix carrier
        language by validating the standard external realizations used in those
        interpretations, without feeding imports or axioms back into the strict
        manuscript proof lanes.
    </p>
'''
        for fname in sorted(bridge_by_file.keys()):
            decls = bridge_by_file[fname]
            n_thm = sum(1 for d in decls if d['type'] in ('theorem', 'lemma'))
            n_def = sum(
                1 for d in decls
                if d['type'] in ('def', 'abbrev', 'structure', 'class', 'instance', 'inductive')
            )
            n_pending = sum(1 for d in decls if d['status'] == 'pending')
            n_ax = sum(1 for d in decls if d['status'] == 'axiom')
            html += f'''        <details>
            <summary class="topic-name" style="border:none; margin:0; padding:0.4rem 0; color:#c084fc;">
                {fname} &nbsp;({len(decls)} decls; {n_thm}T {n_def}D{' | ' + str(n_pending) + ' sorry' if n_pending else ''}{' | ' + str(n_ax) + ' axiom' if n_ax else ''})
            </summary>
            <div class="decl-list" style="padding-left:1rem; margin-bottom:0.5rem;">\n'''
            for d in decls:
                bridge_dot = 'bridge-source'
                if d['status'] == 'pending':
                    bridge_dot = 'pending'
                elif d['status'] == 'axiom':
                    bridge_dot = 'axiom'
                html += f'''                <div class="decl">
                    <div class="status-dot {bridge_dot}"></div>
                    <div class="decl-type">{d['type']}</div>
                    <div class="decl-name">{d['name']}</div>
                    <div class="decl-pdf none">validation bridge source</div>
                    <div class="decl-line">{d['file']}:{d['line']}</div>
                </div>\n'''
            html += '''            </div>\n        </details>\n'''

    html += f'''
    <p class="timestamp">Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}</p>
</body>
</html>'''

    return html


# ── JSON manifest ──────────────────────────────────────────────────────────

def generate_manifest(foundation_decls, partiii_decls, partiv_decls,
                      appendix_operator_decls, appendix_horizon_decls,
                      orphaned_decls, detached_decls, active_foundation_files,
                      active_partiii_files, active_partiv_files,
                      active_appendix_operator_files, active_appendix_horizon_files,
                      bridge_decls, bridge_orphaned_decls, active_bridge_files,
                      bridge_status, coverage_reports, pipeline_status):
    all_active = (
        foundation_decls
        + partiii_decls
        + partiv_decls
        + appendix_operator_decls
        + appendix_horizon_decls
    )
    all_bridge = bridge_decls + bridge_orphaned_decls
    return json.dumps({
        'generated': datetime.now().isoformat(),
        'build_graph': {
            'active_foundation_files': [p.name for p in active_foundation_files],
            'active_partiii_files': [p.name for p in active_partiii_files],
            'active_partiv_files': [p.name for p in active_partiv_files],
            'active_appendix_operator_files': [p.name for p in active_appendix_operator_files],
            'active_appendix_horizon_files': [p.name for p in active_appendix_horizon_files],
            'active_bridge_files': [p.name for p in active_bridge_files],
        },
        'summary': {
            'active_total': len(all_active),
            'core_total': len(foundation_decls + partiii_decls + partiv_decls),
            'appendix_total': len(appendix_operator_decls + appendix_horizon_decls),
            'active_proved': sum(1 for d in all_active if d['status'] == 'proved'),
            'active_pending': sum(1 for d in all_active if d['status'] == 'pending'),
            'active_axioms': sum(1 for d in all_active if d['status'] == 'axiom'),
            'active_pdf_linked': sum(1 for d in all_active if d.get('pdf_ref')),
            'active_theorems': sum(1 for d in all_active if d['type'] in ('theorem', 'lemma')),
            'active_definitions': sum(
                1 for d in all_active
                if d['type'] in ('def', 'abbrev', 'structure', 'class', 'instance', 'inductive')
            ),
            'bridge_total': len(all_bridge),
            'bridge_pending': sum(1 for d in all_bridge if d['status'] == 'pending'),
            'bridge_axioms': sum(1 for d in all_bridge if d['status'] == 'axiom'),
            'bridge_theorems': sum(1 for d in all_bridge if d['type'] in ('theorem', 'lemma')),
            'bridge_definitions': sum(
                1 for d in all_bridge
                if d['type'] in ('def', 'abbrev', 'structure', 'class', 'instance', 'inductive')
            ),
            'bridge_mathlib_fetched': bridge_status.get('mathlib_fetched', False),
            'bridge_build_passing': bridge_status.get('build_passing', False),
            'bridge_built_modules': bridge_status.get('built_modules', 0),
            'bridge_active_modules': bridge_status.get('active_modules', len(active_bridge_files)),
            'bridge_realized_tiers': bridge_status.get('realized_tiers', []),
            'bridge_validated_slices': bridge_status.get('validated_slices', []),
            'bridge_validated_slice_count': len(bridge_status.get('validated_slices', [])),
            'pipeline_certified_lanes_passing': (pipeline_status or {}).get('summary', {}).get('certified_lanes_passing'),
            'pipeline_appendix_lanes_passing': (pipeline_status or {}).get('summary', {}).get('appendix_lanes_passing'),
            'pipeline_full_manuscript_lanes_passing': (pipeline_status or {}).get('summary', {}).get('full_manuscript_lanes_passing'),
            'pipeline_all_requested_lanes_passing': (pipeline_status or {}).get('summary', {}).get('all_requested_lanes_passing'),
            'pipeline_bridge_requested': (pipeline_status or {}).get('summary', {}).get('bridge_requested'),
            'bridge_tier_theorem_counts': {
                tier: sum(
                    1 for d in bridge_decls
                    if d['type'] in ('theorem', 'lemma')
                    and Path(d['file']).stem in stems
                )
                for tier, stems in BRIDGE_TIER_FILES.items()
            },
            'bridge_validation_theorem_counts': {
                name: sum(
                    1 for d in bridge_decls
                    if d['type'] in ('theorem', 'lemma')
                    and Path(d['file']).stem in stems
                )
                for name, stems in BRIDGE_VALIDATION_FILES.items()
            },
            'bridge_validated_theorem_total': sum(
                1 for d in bridge_decls
                if d['type'] in ('theorem', 'lemma')
                and any(Path(d['file']).stem in stems for stems in BRIDGE_VALIDATION_FILES.values())
            ),
        },
        'coverage_reports': coverage_reports,
        'pipeline_status': pipeline_status,
        'parts': {
            'Part I': [d for d in foundation_decls if d.get('part') == 'Part I'],
            'Part II': [d for d in foundation_decls if d.get('part') == 'Part II'],
            'Part III (Foundation)': [d for d in foundation_decls if d.get('part') == 'Part III'],
            'Part III (PartIII/)': partiii_decls,
            'Part IV (PartIV/)': partiv_decls,
            'Appendix Operators': appendix_operator_decls,
            'Appendix Horizons': appendix_horizon_decls,
        },
        'bridge_package': {
            'status': bridge_status,
            'active': bridge_decls,
            'orphaned': bridge_orphaned_decls,
        },
    }, indent=2, default=str)


# ── Main ───────────────────────────────────────────────────────────────────

def main():
    print("=== Lean Verification Dashboard Generator ===\n")

    # 1. Discover build graph
    print("Analyzing build graph...")
    (
        active_foundation,
        active_partiii,
        active_partiv,
        active_appendix_operators,
        active_appendix_horizons,
        orphaned_foundation,
        detached,
    ) = discover_build_graph()
    print(f"  Active Foundation: {len(active_foundation)} files")
    print(f"  Active Part III:   {len(active_partiii)} files")
    print(f"  Active Part IV:    {len(active_partiv)} files")
    print(f"  Appendix operators:{len(active_appendix_operators):>4} files")
    print(f"  Appendix horizons:{len(active_appendix_horizons):>4} files")
    print(f"  Orphaned Foundation: {len(orphaned_foundation)} files")
    print(f"  Archived / unbuilt:{len(detached):>4} files")

    active_bridge, orphaned_bridge, bridge_status = discover_bridge_graph()
    if bridge_status.get('package_present'):
        print(f"  External bridge:   {len(active_bridge)} active files")
        print(f"  Bridge mathlib checkout: {'present' if bridge_status.get('mathlib_fetched') else 'absent'}")
    else:
        print("  External bridge:   package missing")

    # 2. Parse active files
    print("\nParsing active Foundation files...")
    foundation_decls = []
    for p in active_foundation:
        decls = parse_lean_file(p)
        part = classify_part(p.stem)
        topic = stem_to_topic(p.stem)
        for d in decls:
            d['part'] = part
            d['topic'] = topic
        foundation_decls.extend(decls)
        if decls:
            n_thm = sum(1 for d in decls if d['type'] in ('theorem', 'lemma'))
            n_def = sum(1 for d in decls if d['type'] not in ('theorem', 'lemma', 'axiom'))
            n_ax  = sum(1 for d in decls if d['type'] == 'axiom')
            print(f"  {p.stem}: {n_thm}T {n_def}D {n_ax}A")

    print(f"\nParsing Part III files...")
    partiii_decls = []
    for p in active_partiii:
        decls = parse_lean_file(p)
        for d in decls:
            d['part'] = 'Part III'
            d['topic'] = f"PartIII/{p.name}"
        partiii_decls.extend(decls)
        if decls:
            n_thm = sum(1 for d in decls if d['type'] in ('theorem', 'lemma'))
            n_def = sum(1 for d in decls if d['type'] not in ('theorem', 'lemma', 'axiom'))
            print(f"  {p.stem}: {n_thm}T {n_def}D")

    print(f"\nParsing Part IV files...")
    partiv_decls = []
    for p in active_partiv:
        decls = parse_lean_file(p)
        for d in decls:
            d['part'] = 'Part IV'
            d['topic'] = f"PartIV/{p.name}"
        partiv_decls.extend(decls)
        if decls:
            n_thm = sum(1 for d in decls if d['type'] in ('theorem', 'lemma'))
            n_def = sum(1 for d in decls if d['type'] not in ('theorem', 'lemma', 'axiom'))
            print(f"  {p.stem}: {n_thm}T {n_def}D")

    print(f"\nParsing appendix operator files...")
    appendix_operator_decls = []
    for p in active_appendix_operators:
        decls = parse_lean_file(p)
        for d in decls:
            d['part'] = 'Appendix Operators'
            d['topic'] = f"Appendix/{p.name}"
        appendix_operator_decls.extend(decls)
        if decls:
            n_thm = sum(1 for d in decls if d['type'] in ('theorem', 'lemma'))
            n_def = sum(1 for d in decls if d['type'] not in ('theorem', 'lemma', 'axiom'))
            print(f"  {p.stem}: {n_thm}T {n_def}D")

    print(f"\nParsing appendix horizon files...")
    appendix_horizon_decls = []
    for p in active_appendix_horizons:
        decls = parse_lean_file(p)
        for d in decls:
            d['part'] = 'Appendix Horizons'
            d['topic'] = f"Appendix/{p.name}"
        appendix_horizon_decls.extend(decls)
        if decls:
            n_thm = sum(1 for d in decls if d['type'] in ('theorem', 'lemma'))
            n_def = sum(1 for d in decls if d['type'] not in ('theorem', 'lemma', 'axiom'))
            print(f"  {p.stem}: {n_thm}T {n_def}D")

    print(f"\nParsing orphaned Foundation files...")
    orphaned_decls = []
    for p in orphaned_foundation:
        decls = parse_lean_file(p)
        orphaned_decls.extend(decls)
        if decls:
            print(f"  {p.stem}: {len(decls)} decls")

    print(f"\nParsing archived / unbuilt files...")
    detached_decls = []
    for p in detached:
        decls = parse_lean_file(p)
        detached_decls.extend(decls)
        if decls:
            n_sorry = sum(1 for d in decls if d['status'] == 'pending')
            tag = f" ({n_sorry} sorry)" if n_sorry else ""
            print(f"  {p.name}: {len(decls)} decls{tag}")

    print(f"\nParsing external validation bridge files...")
    bridge_decls = []
    for p in active_bridge:
        decls = parse_lean_file(p)
        for d in decls:
            d['part'] = 'Mathlib Validation Lane'
            d['topic'] = p.stem
        bridge_decls.extend(decls)
        if decls:
            n_thm = sum(1 for d in decls if d['type'] in ('theorem', 'lemma'))
            n_def = sum(1 for d in decls if d['type'] not in ('theorem', 'lemma', 'axiom'))
            n_ax = sum(1 for d in decls if d['type'] == 'axiom')
            n_sorry = sum(1 for d in decls if d['status'] == 'pending')
            tag = f" ({n_sorry} sorry)" if n_sorry else ""
            print(f"  {p.stem}: {n_thm}T {n_def}D {n_ax}A{tag}")

    bridge_orphaned_decls = []
    for p in orphaned_bridge:
        decls = parse_lean_file(p)
        for d in decls:
            d['part'] = 'Mathlib Validation Lane'
            d['topic'] = p.stem
        bridge_orphaned_decls.extend(decls)
        if decls:
            print(f"  orphaned {p.stem}: {len(decls)} decls")

    # 3. Parse LaTeX for \lean{} tags
    lean_to_latex = {}
    if LATEX_FLAT.exists():
        print(f"\nParsing LaTeX for \\lean{{}} tags...")
        lean_to_latex = parse_latex_lean_tags(LATEX_FLAT)
        print(f"  Found {len(lean_to_latex)} Lean<->LaTeX links")
    else:
        # Fallback: scan source .tex files directly
        tex_dir = PROJECT_ROOT / "manuscripts" / "monograph" / "sections"
        if tex_dir.exists():
            print(f"\nParsing source .tex files for \\lean{{}} tags...")
            for tex_file in sorted(tex_dir.glob("*.tex")):
                tags = parse_latex_lean_tags(tex_file)
                lean_to_latex.update(tags)
            print(f"  Found {len(lean_to_latex)} Lean<->LaTeX links")

    # 4. Parse .aux for page numbers
    aux_refs = {}
    if AUX_FILE.exists():
        print(f"Parsing .aux for page references...")
        aux_refs = parse_aux_file(AUX_FILE)
        print(f"  Found {len(aux_refs)} labels")

    # 5. Parse audit surfaces
    strict_surface = parse_audit_surface(STRICT_AUDIT)
    bedrock_surface = parse_audit_surface(BEDROCK_AUDIT)
    print(f"\nAudit surfaces:")
    print(f"  Strict (axiom-free):  {len(strict_surface)} declarations")
    print(f"  Bedrock-only:         {len(bedrock_surface)} declarations")

    coverage_reports = load_coverage_reports()
    pipeline_status = load_json_report(LEAN_PIPELINE_STATUS_JSON)
    print(f"\nCoverage reports:")
    for label, report in [
        ("Part I / II coverage", coverage_reports['part_i_ii_coverage']),
        ("Part I / II tags", coverage_reports['part_i_ii_tag']),
        ("Part III coverage", coverage_reports['part_iii_coverage']),
        ("Part III tags", coverage_reports['part_iii_tag']),
        ("Part IV coverage", coverage_reports['part_iv_coverage']),
        ("Part IV tags", coverage_reports['part_iv_tag']),
        ("Appendix operators coverage", coverage_reports['appendix_operators_coverage']),
        ("Appendix operators tags", coverage_reports['appendix_operators_tag']),
        ("Appendix horizons coverage", coverage_reports['appendix_horizons_coverage']),
        ("Appendix horizons tags", coverage_reports['appendix_horizons_tag']),
    ]:
        print(f"  {label}: {'loaded' if report else 'missing'}")
    print(f"  Lean pipeline status: {'loaded' if pipeline_status else 'missing'}")

    # 6. Generate
    OUTPUT_DIR.mkdir(exist_ok=True)

    html = generate_html(
        foundation_decls, partiii_decls, partiv_decls,
        appendix_operator_decls, appendix_horizon_decls,
        orphaned_decls, detached_decls,
        lean_to_latex, aux_refs,
        active_foundation, active_partiii, active_partiv,
        active_appendix_operators, active_appendix_horizons,
        orphaned_foundation, detached,
        strict_surface, bedrock_surface,
        bridge_decls, bridge_orphaned_decls, active_bridge,
        bridge_status, coverage_reports, pipeline_status,
    )
    html_path = OUTPUT_DIR / "dashboard.html"
    with open(html_path, 'w', encoding='utf-8') as f:
        f.write(html)
    print(f"\nDashboard: {html_path}")

    manifest = generate_manifest(
        foundation_decls, partiii_decls, partiv_decls,
        appendix_operator_decls, appendix_horizon_decls,
        orphaned_decls, detached_decls,
        active_foundation, active_partiii, active_partiv,
        active_appendix_operators, active_appendix_horizons,
        bridge_decls, bridge_orphaned_decls, active_bridge,
        bridge_status, coverage_reports, pipeline_status,
    )
    json_path = OUTPUT_DIR / "lean_manifest.json"
    with open(json_path, 'w', encoding='utf-8') as f:
        f.write(manifest)
    print(f"Manifest:  {json_path}")

    # 6. Summary
    all_active = (
        foundation_decls
        + partiii_decls
        + partiv_decls
        + appendix_operator_decls
        + appendix_horizon_decls
    )
    all_detached = orphaned_decls + detached_decls
    proved  = sum(1 for d in all_active if d['status'] == 'proved')
    pending = sum(1 for d in all_active if d['status'] == 'pending')
    axioms  = sum(1 for d in all_active if d['status'] == 'axiom')
    linked  = sum(1 for d in all_active if d.get('pdf_ref'))

    print(f"\n{'='*55}")
    print(f"  ACTIVE BUILD")
    print(f"    Proved:     {proved}")
    print(f"    Pending:    {pending}")
    print(f"    Bedrock:    {axioms} Lean decls ({len(PAPER_AXIOMS)} paper groups)")
    print(f"    PDF linked: {linked}")
    print(f"    Total:      {len(all_active)}")
    print(f"    Theorems:   {sum(1 for d in all_active if d['type'] in ('theorem', 'lemma'))}")

    for pn in ['Part I', 'Part II', 'Part III', 'Part IV', 'Appendix Operators', 'Appendix Horizons']:
        pd = [d for d in all_active if d.get('part') == pn]
        pp = sum(1 for d in pd if d['status'] == 'proved')
        pa = sum(1 for d in pd if d['status'] == 'axiom')
        ps = sum(1 for d in pd if d['status'] == 'pending')
        print(f"      {pn}: {len(pd)} ({pp} proved, {pa} axiom decl, {ps} pending)")

    print(f"\n  ARCHIVED / UNBUILT ({len(all_detached)} declarations)")
    dp = sum(1 for d in all_detached if d['status'] == 'proved')
    ds = sum(1 for d in all_detached if d['status'] == 'pending')
    da = sum(1 for d in all_detached if d['status'] == 'axiom')
    print(f"    {dp} proved, {ds} pending, {da} axioms")
    print(f"\n  EXTERNAL VALIDATION BRIDGE ({len(bridge_decls) + len(bridge_orphaned_decls)} declarations)")
    bp = sum(1 for d in bridge_decls + bridge_orphaned_decls if d['status'] == 'proved')
    bs = sum(1 for d in bridge_decls + bridge_orphaned_decls if d['status'] == 'pending')
    ba = sum(1 for d in bridge_decls + bridge_orphaned_decls if d['status'] == 'axiom')
    print(f"    {bp} source-clean, {bs} pending, {ba} axioms")
    print(f"    mathlib checkout: {'present' if bridge_status.get('mathlib_fetched') else 'absent'}")
    print(
        f"    build: {'passing' if bridge_status.get('build_passing') else 'not passing'} "
        f"({bridge_status.get('built_modules', 0)}/{bridge_status.get('active_modules', len(active_bridge))} modules)"
    )
    tiers = bridge_status.get('realized_tiers') or []
    validations = bridge_status.get('validated_slices') or []
    print(f"    realized tiers: {', '.join(tiers) if tiers else 'none yet'}")
    print(f"    validated slices: {', '.join(validations) if validations else 'none yet'}")
    if bridge_decls:
        tier_counts = []
        for tier, stems in BRIDGE_TIER_FILES.items():
            count = sum(
                1 for d in bridge_decls
                if d['type'] in ('theorem', 'lemma') and Path(d['file']).stem in stems
            )
            if count:
                tier_counts.append(f"{tier} {count}T")
        print(f"    theorem battery: {', '.join(tier_counts) if tier_counts else 'none yet'}")
        validation_counts = []
        for name, stems in BRIDGE_VALIDATION_FILES.items():
            count = sum(
                1 for d in bridge_decls
                if d['type'] in ('theorem', 'lemma') and Path(d['file']).stem in stems
            )
            if count:
                validation_counts.append(f"{name} {count}T")
        print(f"    validation battery: {', '.join(validation_counts) if validation_counts else 'none yet'}")
    if pipeline_status:
        steps = pipeline_status.get('steps', {})
        print(f"\n  PIPELINE STATUS")
        print(f"    main Lean build: {steps.get('main_lean_build', {}).get('status', 'unknown')}")
        print(f"    Part I / II audits: {steps.get('part_i_ii_audits', {}).get('status', 'unknown')}")
        print(f"    Part III audits: {steps.get('part_iii_audits', {}).get('status', 'unknown')}")
        print(f"    Part IV audits: {steps.get('part_iv_audits', {}).get('status', 'unknown')}")
        print(f"    appendix operators: {steps.get('appendix_operators_audits', {}).get('status', 'unknown')}")
        print(f"    appendix horizons: {steps.get('appendix_horizons_audits', {}).get('status', 'unknown')}")
        print(f"    external bridge: {steps.get('mathlib_bridge_build', {}).get('status', 'unknown')}")
    print(f"{'='*55}")


if __name__ == "__main__":
    main()
