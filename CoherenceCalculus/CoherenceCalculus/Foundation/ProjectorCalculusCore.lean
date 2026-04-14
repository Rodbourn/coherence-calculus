import CoherenceCalculus.Foundation.TowerCalculusCore

/-!
# Foundation.ProjectorCalculusCore

Rebuilt projector-calculus layer on the active additive operator spine.

This module certifies the manuscript-facing Grassmannian/projection surface
without reintroducing the archived `LinOp` or Hilbert-space hierarchy. The
results are expressed directly over:

- `Projection`
- `AddMap`
- the explicit shadow/block calculus from `ProjectionCalculusCore`

The only non-forced stationarity ingredient is kept explicit in
`GradientFunctional.stationary_spec`.
-/

namespace CoherenceCalculus

/-- Tangent condition for a first-order projector variation. -/
def isTangentAt (P : Projection) (δP : AddMap) : Prop :=
  ∀ x : State, State.add (P (δP x)) (δP (P x)) = δP x

/-- The commutator of an additive map with a projection, written as
`A ∘ P - P ∘ A`. -/
def projectionCommutator (A : AddMap) (P : Projection) : AddMap :=
  AddMap.sub
    (AddMap.comp A (AddMap.ofProjection P))
    (AddMap.comp (AddMap.ofProjection P) A)

/-- A commutator with a projection is always tangent to the Grassmannian. -/
theorem commutator_is_tangent (A : AddMap) (P : Projection) :
    isTangentAt P (projectionCommutator A P) := by
  intro x
  have hsub :
      P (State.sub (A (P x)) (P (A x))) =
        State.sub (P (A (P x))) (P (P (A x))) := by
    simpa using AddMap.map_sub_state (AddMap.ofProjection P) (A (P x)) (P (A x))
  change
    State.add
        (P (State.sub (A (P x)) (P (A x))))
        (State.sub (A (P (P x))) (P (A (P x)))) =
      State.sub (A (P x)) (P (A x))
  rw [hsub]
  rw [P.idem x, P.idem (A x)]
  calc
    State.add
        (State.sub (P (A (P x))) (P (A x)))
        (State.sub (A (P x)) (P (A (P x))))
        =
      State.add
        (State.sub (A (P x)) (P (A (P x))))
        (State.sub (P (A (P x))) (P (A x))) := by
          rw [State.add_comm]
    _ = State.sub (A (P x)) (P (A x)) := by
          exact sub_eq_add_sub (A (P x)) (P (A (P x))) (P (A x))

/-- Tangent vectors have vanishing `PP` block. -/
theorem tangent_PP_zero (P : Projection) (δP : AddMap) (h : isTangentAt P δP)
    (x : State) :
    P (δP (P x)) = State.zero := by
  have htang := h (P x)
  rw [P.idem x] at htang
  have hcancel :
      State.add (P (δP (P x))) (δP (P x)) =
        State.add State.zero (δP (P x)) := by
    calc
      State.add (P (δP (P x))) (δP (P x)) = δP (P x) := htang
      _ = State.add State.zero (δP (P x)) := by
            rw [State.zero_add]
  exact State.add_right_cancel hcancel

/-- Tangent vectors have vanishing `QQ` block. -/
theorem tangent_QQ_zero (P : Projection) (δP : AddMap) (h : isTangentAt P δP)
    (x : State) :
    projectionShadow P (δP (projectionShadow P x)) = State.zero := by
  have htang := h (projectionShadow P x)
  rw [proj_shadow_orthogonal P x] at htang
  rw [δP.map_zero, State.add_zero] at htang
  calc
    projectionShadow P (δP (projectionShadow P x))
        = projectionShadow P (P (δP (projectionShadow P x))) := by
            exact congrArg (projectionShadow P) htang.symm
    _ = State.zero := by
          exact shadow_proj_orthogonal P (δP (projectionShadow P x))

/-- Tangent vectors are exactly off-diagonal with respect to the chosen
projection split. -/
theorem tangent_is_offdiag (P : Projection) (δP : AddMap) (h : isTangentAt P δP)
    (x : State) :
    δP x = State.add (blockQP P δP x) (blockPQ P δP x) := by
  have hdecomp := blockDecomposition P δP x
  have hPP : blockPP P δP x = State.zero := by
    calc
      blockPP P δP x = P (δP (P x)) := by
        exact operatorCompression_eq_blockPP P δP x
      _ = State.zero := tangent_PP_zero P δP h x
  have hQQ : blockQQ P δP x = State.zero := by
    rw [blockQQ_apply]
    exact tangent_QQ_zero P δP h x
  calc
    δP x
        = State.add
            (blockPP P δP x)
            (State.add (blockPQ P δP x)
              (State.add (blockQP P δP x) (blockQQ P δP x))) := hdecomp
    _ = State.add State.zero
          (State.add (blockPQ P δP x)
            (State.add (blockQP P δP x) (blockQQ P δP x))) := by
          rw [hPP]
    _ = State.add (blockPQ P δP x)
          (State.add (blockQP P δP x) (blockQQ P δP x)) := by
          rw [State.zero_add]
    _ = State.add (blockPQ P δP x) (blockQP P δP x) := by
          rw [hQQ, State.add_zero]
    _ = State.add (blockQP P δP x) (blockPQ P δP x) := by
          rw [State.add_comm]

/-- First variation of the `PP` block. -/
def variationPP (P : Projection) (A δP : AddMap) : AddMap :=
  AddMap.add
    (AddMap.comp δP (AddMap.comp A (AddMap.ofProjection P)))
    (AddMap.comp (AddMap.ofProjection P) (AddMap.comp A δP))

/-- First variation of the `QQ` block. -/
def variationQQ (P : Projection) (A δP : AddMap) : AddMap :=
  AddMap.add
    (AddMap.sub AddMap.zero
      (AddMap.comp δP (AddMap.comp A (AddMap.ofProjection (complementProjection P)))))
    (AddMap.sub AddMap.zero
      (AddMap.comp (AddMap.ofProjection (complementProjection P)) (AddMap.comp A δP)))

/-- First variation of the `PQ` block. -/
def variationPQ (P : Projection) (A δP : AddMap) : AddMap :=
  AddMap.sub
    (AddMap.comp δP (AddMap.comp A (AddMap.ofProjection (complementProjection P))))
    (AddMap.comp (AddMap.ofProjection P) (AddMap.comp A δP))

/-- First variation of the `QP` block. -/
def variationQP (P : Projection) (A δP : AddMap) : AddMap :=
  AddMap.sub
    (AddMap.comp (AddMap.ofProjection (complementProjection P)) (AddMap.comp A δP))
    (AddMap.comp δP (AddMap.comp A (AddMap.ofProjection P)))

/-- Pointwise formula for the first variation of `PAP`. -/
theorem variation_compression_PP (P : Projection) (A δP : AddMap)
    (_h : isTangentAt P δP) (x : State) :
    variationPP P A δP x = State.add (δP (A (P x))) (P (A (δP x))) := by
  rfl

/-- Pointwise formula for the first variation of `QAQ`. -/
theorem variation_compression_QQ (P : Projection) (A δP : AddMap)
    (_h : isTangentAt P δP) (x : State) :
    variationQQ P A δP x =
      State.add
        (State.sub State.zero (δP (A (projectionShadow P x))))
        (State.sub State.zero (projectionShadow P (A (δP x)))) := by
  rfl

/-- Pointwise formula for the first variation of `PAQ`. -/
theorem variation_compression_PQ (P : Projection) (A δP : AddMap)
    (_h : isTangentAt P δP) (x : State) :
    variationPQ P A δP x = State.sub (δP (A (projectionShadow P x))) (P (A (δP x))) := by
  rfl

/-- Explicit two-sided inverse witness for an additive endomap. -/
structure HasInverse (B : AddMap) where
  inv : AddMap
  left_inv : ∀ x : State, inv (B x) = x
  right_inv : ∀ x : State, B (inv x) = x

/-- First variation of an explicit inverse: `-B⁻¹ δB B⁻¹`. -/
def variationInverse (B : AddMap) (hB : HasInverse B) (δB : AddMap) : AddMap :=
  AddMap.sub AddMap.zero (AddMap.comp hB.inv (AddMap.comp δB hB.inv))

/-- Pointwise inverse-variation formula. -/
theorem variation_inverse_formula (B : AddMap) (hB : HasInverse B) (δB : AddMap)
    (x : State) :
    variationInverse B hB δB x = State.sub State.zero (hB.inv (δB (hB.inv x))) := by
  rfl

/-- Differentiating `B ∘ B⁻¹ = id` yields the inverse-variation law. -/
theorem variation_inverse_derivation (B : AddMap) (hB : HasInverse B) (δB : AddMap)
    (x : State) :
    State.add (δB (hB.inv x)) (B (variationInverse B hB δB x)) = State.zero := by
  unfold variationInverse AddMap.sub AddMap.zero AddMap.comp
  change
    State.add (δB (hB.inv x))
      (B (State.sub State.zero (hB.inv (δB (hB.inv x))))) = State.zero
  rw [AddMap.map_sub_state B State.zero (hB.inv (δB (hB.inv x)))]
  rw [B.map_zero, hB.right_inv, State.sub_eq_add_negate, State.zero_add]
  exact State.add_negate_right (δB (hB.inv x))

/-- An additive endomap is stationary for a projection when it preserves the
observable sector exactly. -/
def isStationary (P : Projection) (A : AddMap) : Prop :=
  ∀ x : State, A (P x) = P (A x)

/-- Vanishing commutator is equivalent to stationarity. -/
theorem stationary_iff_commutator_zero (P : Projection) (A : AddMap) :
    isStationary P A ↔ ∀ x : State, projectionCommutator A P x = State.zero := by
  constructor
  · intro h x
    change State.sub (A (P x)) (P (A x)) = State.zero
    rw [h x]
    exact State.sub_self (P (A x))
  · intro h x
    have hcomm := h x
    change State.sub (A (P x)) (P (A x)) = State.zero at hcomm
    calc
      A (P x) = State.add (State.sub (A (P x)) (P (A x))) (P (A x)) := by
        exact (State.add_sub_cancel_right (A (P x)) (P (A x))).symm
      _ = State.add State.zero (P (A x)) := by
        rw [hcomm]
      _ = P (A x) := by
        rw [State.zero_add]

private theorem stationary_blockdiag_iff (P : Projection) (A : AddMap) :
    isStationary P A ↔
      (∀ x : State, blockPQ P A x = State.zero) ∧
      (∀ x : State, blockQP P A x = State.zero) := by
  constructor
  · intro h
    constructor
    · intro x
      rw [blockPQ_apply]
      have hstat := h (projectionShadow P x)
      rw [proj_shadow_orthogonal P x] at hstat
      rw [A.map_zero] at hstat
      exact hstat.symm
    · intro x
      rw [blockQP_apply, h x]
      exact shadow_proj_orthogonal P (A x)
  · intro h
    rcases h with ⟨hPQ, hQP⟩
    intro x
    have hqp_zero : projectionShadow P (A (P x)) = State.zero := by
      simpa [blockQP_apply] using hQP x
    have hsplitP : A (P x) = P (A (P x)) := by
      have hsplit := shadow_plus_proj_identity P (A (P x))
      rw [hqp_zero, State.add_zero] at hsplit
      exact hsplit.symm
    have hresolveA : A x = State.add (A (P x)) (A (projectionShadow P x)) := by
      have hsplitx : x = State.add (P x) (projectionShadow P x) := by
        exact (shadow_plus_proj_identity P x).symm
      calc
        A x = A (State.add (P x) (projectionShadow P x)) := by
          exact congrArg A hsplitx
        _ = State.add (A (P x)) (A (projectionShadow P x)) := by
          rw [A.map_add]
    have hPQ_zero : P (A (projectionShadow P x)) = State.zero := by
      simpa [blockPQ_apply] using hPQ x
    have hprojA : P (A x) = P (A (P x)) := by
      rw [hresolveA, P.map_add, hPQ_zero, State.add_zero]
    calc
      A (P x) = P (A (P x)) := hsplitP
      _ = P (A x) := hprojA.symm

/-- A manuscript-facing objective surface: the directional derivative is kept
explicit, while the bridge to the stationary commutator criterion is part of
the supplied data. -/
structure GradientFunctional where
  gradient : Projection → AddMap
  directional : Projection → AddMap → Nat
  stationary_spec :
    ∀ P : Projection,
      (∀ δP : AddMap, isTangentAt P δP → directional P δP = 0) ↔
        isStationary P (gradient P)

/-- The directional derivative supplied by the objective data. -/
def directionalDerivative (J : GradientFunctional) (P : Projection) (δP : AddMap) : Nat :=
  J.directional P δP

/-- Stationarity for an objective means vanishing directional derivative along
all tangent directions. -/
def isStationaryFor (J : GradientFunctional) (P : Projection) : Prop :=
  ∀ δP : AddMap, isTangentAt P δP → directionalDerivative J P δP = 0

/-- Stationarity is equivalent to vanishing projection commutator of the
supplied gradient. -/
theorem stationarity_condition (J : GradientFunctional) (P : Projection) :
    isStationaryFor J P ↔
      ∀ x : State, projectionCommutator (J.gradient P) P x = State.zero := by
  unfold isStationaryFor directionalDerivative
  exact (J.stationary_spec P).trans (stationary_iff_commutator_zero P (J.gradient P))

/-- Stationarity is equivalent to vanishing off-diagonal blocks of the
supplied gradient. -/
theorem stationarity_blockdiag (J : GradientFunctional) (P : Projection) :
    isStationaryFor J P ↔
      (∀ x : State, blockPQ P (J.gradient P) x = State.zero) ∧
      (∀ x : State, blockQP P (J.gradient P) x = State.zero) := by
  unfold isStationaryFor directionalDerivative
  exact (J.stationary_spec P).trans (stationary_blockdiag_iff P (J.gradient P))

/-- Checking vanishing commutator suffices to certify stationarity. -/
theorem check_stationarity (J : GradientFunctional) (P : Projection)
    (h : ∀ x : State, projectionCommutator (J.gradient P) P x = State.zero) :
    isStationaryFor J P :=
  (stationarity_condition J P).mpr h

/-- Checking vanishing off-diagonal blocks suffices to certify stationarity. -/
theorem check_stationarity_blockdiag (J : GradientFunctional) (P : Projection)
    (hPQ : ∀ x : State, blockPQ P (J.gradient P) x = State.zero)
    (hQP : ∀ x : State, blockQP P (J.gradient P) x = State.zero) :
    isStationaryFor J P :=
  (stationarity_blockdiag J P).mpr ⟨hPQ, hQP⟩

/-- Stationarity forces the off-diagonal gradient blocks to vanish. -/
theorem stationary_implies_offdiag_zero (J : GradientFunctional) (P : Projection)
    (h : isStationaryFor J P) :
    (∀ x : State, blockPQ P (J.gradient P) x = State.zero) ∧
    (∀ x : State, blockQP P (J.gradient P) x = State.zero) :=
  (stationarity_blockdiag J P).mp h

end CoherenceCalculus
