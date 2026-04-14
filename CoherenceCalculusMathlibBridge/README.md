# CoherenceCalculusMathlibBridge

This package is a separate, one-way compatibility layer from the certified
`CoherenceCalculus` spine into standard Lean/mathlib structures.

It is not part of the bedrock-certified claim.

## Purpose

The certified spine proves Parts I, II, and the current Part III bridge
interfaces without importing `Mathlib`. This package exists for a different
reason: to show that those abstract interfaces can be instantiated inside
ordinary mathlib models, so the calculus can be used as a general tool rather
than only as a bespoke internal grammar.

## Boundary

- `CoherenceCalculus/` remains the certified package.
- `CoherenceCalculusMathlibBridge/` is outside that certification boundary.
- Imports from `Mathlib` are allowed here.
- The bridge direction is one-way only:
  certified calculus interfaces -> mathlib realizations.

## Initial bridge levels

The bridge package is organized around a stable external contract:

1. `Contract.lean`
   This is the external API surface. Future mathlib-facing realizations should
   target these bundled bridge tiers rather than raw internal names from the
   derived Part III development.

2. `FilterLimit.lean`
   Interprets Part III `LimitInterface` using mathlib filter eventuality at
   `Filter.atTop`. This is intentionally lower than topology-based convergence,
   because the current abstract `LimitInterface.map` law is stronger than
   ordinary `Tendsto` under arbitrary maps.

3. `LinearProjection.lean`
   The first broad mathlib-facing tier. It packages module-level linear
   projection towers and linear recovery data into the detached observation and
   recovery contracts. This file now also carries the first compiled theorem
   battery: realized calculus towers and recovery operators inherit standard
   mathlib linear identities such as `map_add` and `map_smul`.

4. `AbstractHilbert.lean`
   Provides detached realization shells using mathlib continuous linear maps and
   Hilbert-space structure, then packages them against the stable detached
   contract surface in `Contract.lean`. The current source-level shells cover:
   - observation
   - recovery
   - completion
   - continuum reconstruction
   - late-shell flow
   - promotion
   - fibered recovery / promotion
   It now also carries a compiled Hilbert-tier theorem battery showing that the
   realized calculus towers, observed operators, defects, and recovery
   operators inherit standard `ContinuousLinearMap` identities and continuity
   facts on the exported calculus operators.

5. `ContinuumBattery.lean`
   Lifts the bridge from operator shells to actual Part III consequences on
   mathlib-carried continuum models. The current theorem battery specializes
   the certified continuum-identification and forcing theorems to detached
   mathlib realizations, including:
   - uniqueness of asymptotically consistent continuum laws
   - forcing of a consistent law from a uniqueness witness
   - exact reconstruction/sample convergence on the exported bridge datum

6. `LateShellBattery.lean`
   Provides the first theorem battery on the late-shell contract. This tier is
   still exact-data oriented in the certified Part III surface, so the detached
   theorems are intentionally exact wrapper results: they show the exported
   late-shell contract preserves the packaged interpolation, block-derivative,
   effective-flow, and flow-vs-tower data without loss.

7. `PromotionBattery.lean`
   Provides the first detached theorem battery on the promotion/fibered
   promotion side. This is likewise exact and algebraic rather than analytic:
   it unfolds the promoted observed-law formulas and shows the detached
   promotion contracts preserve the certified characteristic/admissible/
   minimum-energy data exactly.

8. `TopologicalBattery.lean`
   Upgrades the detached bridge from eventual-equality limits to standard
   mathlib neighborhood convergence and Cauchy-sequence facts. This is the
   first battery that turns the certified bridge limit notion into genuinely
   topological consequences on realized Hilbert/continuum models:
   - faithful projection towers converge in `𝓝 x`
   - observed and defect sequences converge in `𝓝 (operator x)` and `𝓝 0`
   - reconstruction/sample and asymptotically consistent law sequences are
     Cauchy and converge in the standard mathlib sense

9. `ConcreteModels.lean`
   Provides named explicit detached realizations rather than only abstract
   bridge shells. The current concrete models are:
   - a stabilized identity projection tower that becomes the identity after a
     finite cutoff
   - a stabilized operator-recovery model built from any
     `ContinuousLinearMap`
   - a constant observed-law continuum model whose reconstruction/sample maps
     are literally the identity
   These are used to show that the bridge consequences are instantiated on
   concrete mathlib objects, not only available abstractly.

10. `TopologyValidation.lean`
   This is the first actual validated mathlib-consumer slice, not just a bridge
   battery. It imports standard mathlib topology/uniform-space modules and uses
   their own theorems directly on the concrete detached models:
   - `tendsto_nhds_unique`
   - `cauchySeq_tendsto_of_complete`
   - `cauchySeq_iff_tendsto`
   - `CauchySeq.comp_injective`
   The current validated slice is the continuum/topology band: mathlib's own
   Hausdorff uniqueness, completeness, and subsequence-Cauchy machinery recover
   exactly the limits predicted by the detached calculus models.

11. `HilbertProjectionValidation.lean`
   This is the next validated mathlib-consumer slice: the standard Hilbert
   orthogonal-projection band. It uses actual mathlib projection theorems on
   concrete calculus-generated operators:
   - self-adjointness of `U.starProjection`
   - star-projection structure
   - orthogonal decomposition `U.starProjection x + Uᗮ.starProjection x = x`
   - Pythagorean norm splitting
   - membership criterion via projection norm
   - concrete observed/defect limits in the stabilized recovery model built from
     `U.starProjection`

12. `HilbertOrthogonalityValidation.lean`
   This extends the Hilbert validated surface from basic projection identities
   to the standard orthogonality laws actually consumed elsewhere in mathlib.
   On the same concrete recovery model built from `U.starProjection`, it now
   validates:
   - membership of the projected point in the subspace
   - residual membership in the orthogonal complement
   - the `starProjection_eq_self_iff` criterion
   - idempotence on the concrete recovery operator
   - the complement formula `Uᗮ.starProjection = id - U.starProjection`
   - norm nonexpansion
   - orthogonal composition vanishing
   - monotonic composition under subspace inclusion
   - top/bottom subspace projection formulas

13. `HilbertPositiveValidation.lean`
   This extends the same concrete `U.starProjection` model into the Loewner
   order / positive-operator band from mathlib. It validates:
   - positivity of the concrete recovery operator
   - operator nonnegativity and the interval bound `0 ≤ p ≤ id`
   - order/equality comparison against other subspace projections
   - positivity of compressed operators
   - positivity of the induced subspace orthogonal-compression operator

14. `HilbertSpectralValidation.lean`
   This extends the same concrete projection model into the spectral band used
   by mathlib's Banach/C*-algebra interface. It validates:
   - nonnegative-real spectral restriction for the concrete recovery operator
   - `{0, 1}` spectral support from idempotence
   - the corresponding spectral-radius dichotomy `r = 0 ∨ r = 1`
   - the same spectral control for the orthogonal-complement operator

15. `HilbertEigenspaceValidation.lean`
   This extends the same concrete projection model into the finite-dimensional
   eigenspace band. It validates:
   - exact eigenspace identities for eigenvalues `1` and `0`
   - `HasEigenvalue` criteria in terms of `U ≠ ⊥` and `U ≠ ⊤`
   - the corresponding finite-dimensional spectrum-membership criteria
   - the same eigenspace/eigenvalue facts for the orthogonal-complement operator

16. `HilbertDeterminantValidation.lean`
   This extends the same finite-dimensional projection model into the
   determinant/invertibility band. It validates:
   - exact invertibility criteria for the operator and its orthogonal complement
   - determinant vanishing/nonvanishing criteria in terms of `U = ⊤` and
     `U = ⊥`
   - determinant `1` on the extremal top/bottom projection cases

17. `HilbertCharpolyValidation.lean`
   This extends the same finite-dimensional `Module.End` projection model into
   the characteristic-polynomial band. It validates:
   - the mathlib equivalence between spectrum-membership and `charpoly.IsRoot`
     on both the operator and its orthogonal complement
   - the concrete root criteria at `1` and `0` in terms of `U ≠ ⊥` and
     `U ≠ ⊤`

18. `HilbertMinpolyValidation.lean`
   This extends the same finite-dimensional `Module.End` projection model into
   the minimal-polynomial band. It validates:
   - the mathlib equivalence between `HasEigenvalue` and `minpoly.IsRoot` on
     both the operator and its orthogonal complement
   - the concrete minimal-polynomial root criteria at `1` and `0`
   - divisibility of the minimal polynomial by the projection quadratic
     `X * (X - 1)`
   - the exact extremal minimal polynomials on the top/bottom projection cases

19. `HilbertRankValidation.lean`
   This extends the same finite-dimensional projection model into the
   range/kernel rank band. It validates:
   - exact range and kernel identities for the operator and its orthogonal
     complement
   - exact `finrank` identities for those ranges and kernels
   - rank-nullity on the concrete recovery operator
   - the dimension split between the projected and orthogonal projected ranges

20. `HilbertTraceValidation.lean`
   This extends the same finite-dimensional projection model into the trace
   band. It validates:
   - exact projected-plus-orthogonal trace splitting
   - top/bottom trace identities
   - zero mixed trace on orthogonal compositions
   - trace stability under idempotent squaring for both the operator and its
     orthogonal complement

21. `HilbertTraceRankValidation.lean`
   This links the same finite-dimensional projection model to mathlib's
   projection-trace theorem family. It validates:
   - the recovered operator and its orthogonal complement as genuine
     `LinearMap.IsProj` instances
   - exact trace = projected-dimension identities via `LinearMap.IsProj.trace`
   - the corresponding trace = range-dimension identities
   - zero-trace criteria characterizing the trivial/top subspace cases

22. `HilbertTraceDecompositionValidation.lean`
   This extends the same projection model into trace decomposition for arbitrary
   endomorphisms. It validates:
   - trace commutation with the projected and orthogonal projected pieces
   - exact left/right trace splitting through the `U ⊕ Uᗮ` decomposition
   - vanishing of the mixed projected/orthogonal trace blocks
   - exact diagonal trace decomposition through the projected and orthogonal
     diagonal blocks

23. `HilbertBlockDiagonalValidation.lean`
   This extends the same projection model into block-diagonal normal form. It
   validates:
   - the concrete recovery operator as a genuine complemented projection
   - exact conjugacy to `prodMap id 0` under the complement decomposition
   - exact `id`/`0` criteria for the operator and its orthogonal complement
   - coordinate-zero membership tests under the complement equivalence

24. `HilbertRestrictionTraceValidation.lean`
   This extends the same projection model into invariant-subspace and
   restriction-trace consumer laws. It validates:
   - the `U ⊕ Uᗮ` complement pair as a genuine internal direct-sum family
   - exact restriction-trace identities for the projected and orthogonal
     projected operators via `LinearMap.trace_restrict_eq_of_forall_mem`
   - a block-diagonal trace splitting theorem for arbitrary endomorphisms on
     the concrete `U ⊕ Uᗮ` decomposition via
     `LinearMap.trace_eq_sum_trace_restrict`
   - vanishing trace of the off-diagonal block operator via
     `LinearMap.trace_eq_zero_of_mapsTo_ne`

25. `HilbertBlockFactorizationValidation.lean`
   This extends the same projection model into exact product-factorization
   laws for the block-diagonal operator on `U ⊕ Uᗮ`. It validates:
   - exact conjugacy of the block-diagonal operator to a genuine
     `LinearMap.prodMap` built from its restricted subspace and orthogonal
     blocks
   - exact determinant factorization through those two blocks via
     `LinearMap.det_conj` and `LinearMap.det_prodMap`
   - exact characteristic-polynomial factorization through those two blocks
     via `LinearEquiv.charpoly_conj` and `LinearMap.charpoly_prodMap`

26. `HilbertBlockSpectrumValidation.lean`
   This extends the same projection model into block-spectrum and
   block-eigenvalue consumer laws on the exact `U ⊕ Uᗮ` decomposition. It
   validates:
   - exact characteristic-polynomial root splitting for the block-diagonal
     operator into the subspace and orthogonal blocks
   - exact spectrum splitting for the block-diagonal operator into the union of
     the two block spectra
   - exact `HasEigenvalue` splitting for the block-diagonal operator into the
     two restricted block endomorphisms
   - direct spectrum and eigenvalue transport from either block into the full
     block-diagonal operator

27. `HilbertBlockMinpolyValidation.lean`
   This extends the same projection model into block-level minimal-polynomial
   consumer laws on the exact `U ⊕ Uᗮ` decomposition. It validates:
   - divisibility of the full block-diagonal minimal polynomial by the exact
     product of the two block characteristic polynomials
   - exact minimal-polynomial root splitting for the block-diagonal operator
     into the two restricted blocks
   - direct minimal-polynomial root transport from each block into the full
     block-diagonal operator

## Planned bridge ladder

The intended development order is:

1. Linear / projection tier
   Target: the lowest broad-use algebraic/operator band supported by Parts I and II.

2. Hilbert / completion tier
   Target: the part of Part III that packages faithful towers, completion, and
   recovery in a standard functional-analytic setting.

3. Continuum / promotion tier
   Target: the asymptotic-consistency, late-shell flow, and promotion packages
   already formalized in Part III.
   The first theorem batteries for this zone now live in
   `ContinuumBattery.lean`, `LateShellBattery.lean`, and
   `PromotionBattery.lean`.

Each new mathlib-facing module should do two things:

- instantiate one of the detached contracts in `Contract.lean`
- prove a small theorem battery showing which standard mathlib results become
  available on the realized calculus objects

## Non-goals

- replacing the foundation of mathlib
- claiming that the entire import graph is now supported
- duplicating the certified spine inside mathlib
- letting the detached bridge influence the bedrock-certified claim

## Build policy

Do not copy mathlib into the certified package.

If a vendored checkout is ever needed for reproducibility, keep it inside this
detached bridge package only. The certified `CoherenceCalculus/` package must
remain independent of `Mathlib`.

## Current bridge status

- pinned to `mathlib4 v4.26.0`
- local `CoherenceCalculus` path dependency attached
- bridge package builds successfully
- currently realized tiers: `limit`, `linear`, `hilbert`, `continuum`,
  `lateShell`, `promotion`, `topology`, and `models`
- currently validated mathlib-consumer slices: `continuum/topology`,
  `hilbert/projection`, `hilbert/orthogonality`, `hilbert/positivity`,
  `hilbert/spectral`, `hilbert/eigenspace`, `hilbert/minpoly`,
  `hilbert/rank`, `hilbert/trace`, `hilbert/trace-rank`,
  `hilbert/trace-decomposition`, `hilbert/block-diagonal`,
  `hilbert/restriction-trace`, `hilbert/block-factorization`,
  `hilbert/block-spectrum`, `hilbert/block-minpoly`,
  `hilbert/determinant`, and `hilbert/charpoly`
- theorem batteries compiled on the `linear`, `hilbert`, `continuum`,
  `lateShell`, `promotion`, `topology`, and `models` tiers
- consumer validations compiled in `TopologyValidation.lean` and
  `HilbertProjectionValidation.lean`, `HilbertOrthogonalityValidation.lean`,
  `HilbertPositiveValidation.lean`, `HilbertSpectralValidation.lean`,
  `HilbertEigenspaceValidation.lean`, `HilbertMinpolyValidation.lean`,
  `HilbertRankValidation.lean`, `HilbertTraceValidation.lean`,
  `HilbertTraceRankValidation.lean`,
  `HilbertTraceDecompositionValidation.lean`,
  `HilbertBlockDiagonalValidation.lean`,
  `HilbertRestrictionTraceValidation.lean`,
  `HilbertBlockFactorizationValidation.lean`,
  `HilbertBlockSpectrumValidation.lean`,
  `HilbertBlockMinpolyValidation.lean`,
  `HilbertDeterminantValidation.lean`, and
  `HilbertCharpolyValidation.lean`
