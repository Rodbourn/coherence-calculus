# CoherenceCalculus

This package contains the Lean 4 formalization of the certified Coherence
Calculus development used by the public monograph.

## Scope

- `Foundation.lean` is the narrow bedrock-certified spine.
- `PartIII.lean` and `PartIV.lean` are separate audited lanes covering the
  continuum bridge and the later conditional theorem surfaces.
- `AppendixOperators.lean` and `AppendixHorizons.lean` cover the theorem-bearing
  appendix lanes under the same audit discipline.
- `CoherenceCalculusMathlibBridge/` is a separate package outside this
  certification boundary.

## Build and audit

From this directory:

```bash
lake build
bash audit_axiom_levels.sh
bash audit_part3_axioms.sh
bash audit_part4_axioms.sh
bash audit_appendix_operators_axioms.sh
bash audit_appendix_horizons_axioms.sh
```

## Naming note

Some module names, especially `PartIII` and `PartIV`, are historical names
retained for source stability. The manuscript and top-level repository README
state the current conceptual organization more directly.
