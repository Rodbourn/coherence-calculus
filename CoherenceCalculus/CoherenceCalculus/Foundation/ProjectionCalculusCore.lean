import CoherenceCalculus.Foundation.OperatorCore

/-!
# Foundation.ProjectionCalculusCore

Generic projection/block algebra on the rebuilt additive state space.

This module stays entirely inside the active `Projection` / `AddMap` interface.
It rebuilds the exact algebra needed for the manuscript's projection-facing
Part I surfaces:

- projection/complement resolution
- block components relative to an arbitrary projection
- diagonal/off-diagonal splitting
- horizon-band increments and their nesting/orthogonality laws

No spectral, Hilbert-space, or archived `LinOp` machinery is reintroduced here.
-/

namespace CoherenceCalculus

namespace AddMap

/-- Pointwise sum of additive endomaps. -/
def add (A B : AddMap) : AddMap where
  toFun := fun x => State.add (A x) (B x)
  map_add := by
    intro x y
    rw [A.map_add, B.map_add]
    calc
      State.add (State.add (A x) (A y)) (State.add (B x) (B y))
          = State.add (A x) (State.add (A y) (State.add (B x) (B y))) := by
              rw [State.add_assoc]
      _ = State.add (A x) (State.add (State.add (A y) (B x)) (B y)) := by
            rw [State.add_assoc]
      _ = State.add (A x) (State.add (State.add (B x) (A y)) (B y)) := by
            rw [State.add_comm (A y) (B x)]
      _ = State.add (A x) (State.add (B x) (State.add (A y) (B y))) := by
            rw [State.add_assoc]
      _ = State.add (State.add (A x) (B x)) (State.add (A y) (B y)) := by
            rw [← State.add_assoc]
  map_zero := by
    rw [A.map_zero, B.map_zero]
    exact State.add_zero State.zero

end AddMap

/-- The complement of a projection on the rebuilt state space. -/
def projectionShadow (P : Projection) : State → State :=
  fun x => State.sub x (P x)

/-- The complement of a projection is additive. -/
theorem projectionShadow_add (P : Projection) (x y : State) :
    projectionShadow P (State.add x y) =
      State.add (projectionShadow P x) (projectionShadow P y) := by
  unfold projectionShadow
  rw [P.map_add]
  exact State.sub_add_distrib x y (P x) (P y)

/-- The complement of a projection preserves zero. -/
theorem projectionShadow_zero (P : Projection) :
    projectionShadow P State.zero = State.zero := by
  unfold projectionShadow
  rw [P.map_zero]
  exact State.sub_self State.zero

/-- Observable and shadow pieces resolve the identity. -/
theorem shadow_plus_proj_identity (P : Projection) (x : State) :
    State.add (P x) (projectionShadow P x) = x := by
  unfold projectionShadow
  exact State.add_sub_cancel_left x (P x)

/-- The projection annihilates its shadow complement. -/
theorem proj_shadow_orthogonal (P : Projection) (x : State) :
    P (projectionShadow P x) = State.zero := by
  have hproj :
      State.add (P (P x)) (P (projectionShadow P x)) = P x := by
    calc
      State.add (P (P x)) (P (projectionShadow P x))
          = P (State.add (P x) (projectionShadow P x)) := by
              symm
              exact P.map_add (P x) (projectionShadow P x)
      _ = P x := by
            rw [shadow_plus_proj_identity]
  rw [P.idem x] at hproj
  have hproj' :
      State.add (P x) (P (projectionShadow P x)) =
        State.add (P x) State.zero := by
    calc
      State.add (P x) (P (projectionShadow P x)) = P x := hproj
      _ = State.add (P x) State.zero := by
            rw [State.add_zero]
  exact State.add_left_cancel hproj'

/-- The shadow complement annihilates observable points. -/
theorem shadow_proj_orthogonal (P : Projection) (x : State) :
    projectionShadow P (P x) = State.zero := by
  unfold projectionShadow
  rw [P.idem]
  exact State.sub_self (P x)

/-- The complement of a projection is idempotent. -/
theorem projectionShadow_idem (P : Projection) (x : State) :
    projectionShadow P (projectionShadow P x) = projectionShadow P x := by
  have hz : P (projectionShadow P x) = State.zero := proj_shadow_orthogonal P x
  unfold projectionShadow at hz ⊢
  rw [hz]
  exact State.sub_zero (State.sub x (P x))

/-- The complement of a projection packaged again as a projection. -/
def complementProjection (P : Projection) : Projection where
  toFun := projectionShadow P
  map_add := projectionShadow_add P
  map_zero := projectionShadow_zero P
  idem := projectionShadow_idem P

/-- Block `PAP`. -/
def blockPP (P : Projection) (A : AddMap) : AddMap :=
  AddMap.comp (AddMap.ofProjection P) (AddMap.comp A (AddMap.ofProjection P))

/-- Block `PAQ`. -/
def blockPQ (P : Projection) (A : AddMap) : AddMap :=
  AddMap.comp (AddMap.ofProjection P) (AddMap.comp A (AddMap.ofProjection (complementProjection P)))

/-- Block `QAP`. -/
def blockQP (P : Projection) (A : AddMap) : AddMap :=
  AddMap.comp (AddMap.ofProjection (complementProjection P))
    (AddMap.comp A (AddMap.ofProjection P))

/-- Block `QAQ`. -/
def blockQQ (P : Projection) (A : AddMap) : AddMap :=
  AddMap.comp (AddMap.ofProjection (complementProjection P))
    (AddMap.comp A (AddMap.ofProjection (complementProjection P)))

/-- Observable compression is exactly the `PP` block. -/
theorem operatorCompression_eq_blockPP (P : Projection) (A : AddMap) (x : State) :
    blockPP P A x = P (A (P x)) := by
  rfl

/-- Transport from `Q` back into `P`. -/
theorem blockPQ_apply (P : Projection) (A : AddMap) (x : State) :
    blockPQ P A x = P (A (projectionShadow P x)) := by
  rfl

/-- Transport from `P` out into `Q`. -/
theorem blockQP_apply (P : Projection) (A : AddMap) (x : State) :
    blockQP P A x = projectionShadow P (A (P x)) := by
  rfl

/-- Internal shadow block. -/
theorem blockQQ_apply (P : Projection) (A : AddMap) (x : State) :
    blockQQ P A x = projectionShadow P (A (projectionShadow P x)) := by
  rfl

/-- Schur/Feshbach correction once a `Q`-block propagator has been provided
explicitly. -/
def schurComplement (P : Projection) (A Rqq : AddMap) : AddMap :=
  AddMap.comp (blockPQ P A) (AddMap.comp Rqq (blockQP P A))

/-- Effective `P`-space operator associated to an explicit `Q`-propagator. -/
def effectiveOp (P : Projection) (A Rqq : AddMap) : AddMap :=
  AddMap.add (blockPP P A) (schurComplement P A Rqq)

/-- Split transform returning the effective observable operator together with
its Schur correction. -/
def splitTransform (P : Projection) (A Rqq : AddMap) : AddMap × AddMap :=
  (effectiveOp P A Rqq, schurComplement P A Rqq)

/-- Data of a `P`/`Q` splitting. -/
structure PQSplitting where
  proj : Projection

/-- A generic resolvent witness for an additive endomap. -/
structure HasResolvent (A : AddMap) where
  inverse : AddMap
  left_inv : ∀ x, inverse (A x) = x
  right_inv : ∀ x, A (inverse x) = x

/-- Two projections are nested when the coarser one survives composition from
either side. -/
structure NestedProjections where
  coarse : Projection
  fine : Projection
  nested : ∀ x, coarse (fine x) = coarse x
  nested_ge : ∀ x, fine (coarse x) = coarse x

/-- The horizon cut at level `h` is a canonical `P`/`Q` splitting. -/
def HorizonSpecialization (T : HorizonTower) (h : Nat) : PQSplitting where
  proj := T.π h

/-- Residual transport data across a projection split. -/
structure ResidualSignature where
  transportIn : AddMap
  internal : AddMap
  transportOut : AddMap

/-- Residual signature induced by an additive map and a projection cut. -/
def residualSignatureOf (P : Projection) (A : AddMap) : ResidualSignature where
  transportIn := blockPQ P A
  internal := blockQQ P A
  transportOut := blockQP P A

/-- A residual return field on a projection cut packages the residual transport
signature together with a chosen shadow propagator. -/
structure ResidualReturnField where
  signature : ResidualSignature
  shadowPropagator : AddMap

/-- The canonical residual return field induced by a projection cut, an additive
law, and a chosen shadow propagator. -/
def residualReturnFieldOf (P : Projection) (A shadowPropagator : AddMap) :
    ResidualReturnField where
  signature := residualSignatureOf P A
  shadowPropagator := shadowPropagator

/-- The residual field is the shadow datum generated by transport out of the
observable sector and propagation in the residual sector. -/
def residualFieldState (field : ResidualReturnField) : AddMap :=
  AddMap.comp field.shadowPropagator field.signature.transportOut

/-- Returned residual is the observable forcing generated by transporting the
residual field back into the visible sector. -/
def returnedResidual (field : ResidualReturnField) : AddMap :=
  AddMap.comp field.signature.transportIn (residualFieldState field)

/-- The Schur correction factors as transport into the shadow, explicit
shadow propagation, and transport back out. -/
theorem schur_factorization (P : Projection) (A Rqq : AddMap) (x : State) :
    schurComplement P A Rqq x = blockPQ P A (Rqq (blockQP P A x)) := by
  rfl

/-- The returned residual of the canonical residual return field is exactly the
Schur correction. -/
theorem returnedResidual_eq_schur
    (P : Projection) (A shadowPropagator : AddMap) :
    returnedResidual (residualReturnFieldOf P A shadowPropagator) =
      schurComplement P A shadowPropagator := by
  rfl

/-- Diagonal part relative to an arbitrary projection split. -/
def diagPart (P : Projection) (A : AddMap) : AddMap :=
  AddMap.add (blockPP P A) (blockQQ P A)

/-- Off-diagonal part relative to an arbitrary projection split. -/
def offDiagPart (P : Projection) (A : AddMap) : AddMap :=
  AddMap.add (blockPQ P A) (blockQP P A)

private theorem state_add_four_swap (a b c d : State) :
    State.add (State.add a b) (State.add c d) =
      State.add (State.add a c) (State.add b d) := by
  calc
    State.add (State.add a b) (State.add c d)
        = State.add a (State.add b (State.add c d)) := by
            rw [State.add_assoc]
    _ = State.add a (State.add (State.add b c) d) := by
          rw [State.add_assoc]
    _ = State.add a (State.add (State.add c b) d) := by
          rw [State.add_comm b c]
    _ = State.add a (State.add c (State.add b d)) := by
          rw [State.add_assoc]
    _ = State.add (State.add a c) (State.add b d) := by
          rw [← State.add_assoc]

private theorem state_add_diag_offdiag (pp pq qp qq : State) :
    State.add pp (State.add pq (State.add qp qq)) =
      State.add (State.add pp qq) (State.add pq qp) := by
  calc
    State.add pp (State.add pq (State.add qp qq))
        = State.add (State.add pp pq) (State.add qp qq) := by
            rw [← State.add_assoc, ← State.add_assoc]
    _ = State.add (State.add pp pq) (State.add qq qp) := by
          rw [State.add_comm qp qq]
    _ = State.add (State.add pp qq) (State.add pq qp) := by
          exact state_add_four_swap pp pq qq qp

/-- Exact four-block decomposition relative to a projection split. -/
theorem blockDecomposition (P : Projection) (A : AddMap) (x : State) :
    A x =
      State.add
        (blockPP P A x)
        (State.add (blockPQ P A x) (State.add (blockQP P A x) (blockQQ P A x))) := by
  have hresolve :
      A x = State.add (A (P x)) (A (projectionShadow P x)) := by
    calc
      A x = A (State.add (P x) (projectionShadow P x)) := by
            rw [shadow_plus_proj_identity]
      _ = State.add (A (P x)) (A (projectionShadow P x)) := by
            rw [A.map_add]
  have hobs :
      A (P x) = State.add (blockPP P A x) (blockQP P A x) := by
    change A (P x) = State.add (P (A (P x))) (projectionShadow P (A (P x)))
    exact (shadow_plus_proj_identity P (A (P x))).symm
  have hsh :
      A (projectionShadow P x) = State.add (blockPQ P A x) (blockQQ P A x) := by
    change A (projectionShadow P x) =
      State.add (P (A (projectionShadow P x))) (projectionShadow P (A (projectionShadow P x)))
    exact (shadow_plus_proj_identity P (A (projectionShadow P x))).symm
  calc
    A x = State.add (A (P x)) (A (projectionShadow P x)) := hresolve
    _ = State.add
          (State.add (blockPP P A x) (blockQP P A x))
          (State.add (blockPQ P A x) (blockQQ P A x)) := by
            rw [hobs, hsh]
    _ = State.add
          (State.add (blockPP P A x) (blockPQ P A x))
          (State.add (blockQP P A x) (blockQQ P A x)) := by
            exact state_add_four_swap
              (blockPP P A x) (blockQP P A x) (blockPQ P A x) (blockQQ P A x)
    _ = State.add
          (blockPP P A x)
          (State.add (blockPQ P A x) (State.add (blockQP P A x) (blockQQ P A x))) := by
            rw [State.add_assoc]

/-- Diagonal plus off-diagonal parts reconstruct the original additive map. -/
theorem diagonal_offdiagonal_decomposition (P : Projection) (A : AddMap) (x : State) :
    A x = State.add (diagPart P A x) (offDiagPart P A x) := by
  calc
    A x = State.add
        (blockPP P A x)
        (State.add (blockPQ P A x) (State.add (blockQP P A x) (blockQQ P A x))) := by
          exact blockDecomposition P A x
    _ = State.add
        (State.add (blockPP P A x) (blockQQ P A x))
        (State.add (blockPQ P A x) (blockQP P A x)) := by
          exact state_add_diag_offdiag
            (blockPP P A x) (blockPQ P A x) (blockQP P A x) (blockQQ P A x)
    _ = State.add (diagPart P A x) (offDiagPart P A x) := by
          rfl

/-- Projection algebra gives the core identities used throughout the defect
grammar. -/
theorem unifiedGrammar_projection_algebra (P : Projection) :
    (∀ x, State.add (P x) (projectionShadow P x) = x) ∧
    (∀ x, P (projectionShadow P x) = State.zero) ∧
    (∀ x, P (P x) = P x) := by
  refine ⟨shadow_plus_proj_identity P, proj_shadow_orthogonal P, P.idem⟩

/-- Increment band of a horizon tower, using the predecessor convention from the
draft (`h - 1` truncates at `0`). -/
def incrementProj (T : HorizonTower) (h : Nat) : AddMap where
  toFun := fun x => State.sub ((T.π h).toFun x) ((T.π (h - 1)).toFun x)
  map_add := by
    intro x y
    rw [(T.π h).map_add, (T.π (h - 1)).map_add]
    exact State.sub_add_distrib ((T.π h).toFun x) ((T.π h).toFun y)
      ((T.π (h - 1)).toFun x) ((T.π (h - 1)).toFun y)
  map_zero := by
    rw [(T.π h).map_zero, (T.π (h - 1)).map_zero]
    exact State.sub_self State.zero

/-- Nested horizon projections compose to the lower level. -/
theorem multiresolution_nesting (T : HorizonTower) (h₁ h₂ : Nat) (hle : h₁ ≤ h₂) (x : State) :
    (T.π h₁).toFun x = (T.π h₁).toFun ((T.π h₂).toFun x) := by
  exact (nested_proj_comp T h₁ h₂ hle x).symm

/-- The increment band is the difference between adjacent projections. -/
theorem wavelet_detail_analog (T : HorizonTower) (h : Nat) (x : State) :
    incrementProj T h x =
      State.add ((T.π h).toFun x) (State.negate ((T.π (h - 1)).toFun x)) := by
  unfold incrementProj
  exact State.sub_eq_add_negate ((T.π h).toFun x) ((T.π (h - 1)).toFun x)

private theorem incrementProj_orthog_lt (T : HorizonTower) (h k : Nat) (hlt : h < k) (x : State) :
    incrementProj T h (incrementProj T k x) = State.zero := by
  change State.sub
      ((T.π h).toFun (State.add ((T.π k).toFun x) (State.negate ((T.π (k - 1)).toFun x))))
      ((T.π (h - 1)).toFun (State.add ((T.π k).toFun x) (State.negate ((T.π (k - 1)).toFun x))))
      = State.zero
  rw [(T.π h).map_add, (T.π (h - 1)).map_add]
  have hneg_h :
      (T.π h).toFun (State.negate ((T.π (k - 1)).toFun x)) =
        State.negate ((T.π h).toFun ((T.π (k - 1)).toFun x)) := by
    exact AddMap.map_negate (AddMap.ofProjection (T.π h)) ((T.π (k - 1)).toFun x)
  have hneg_hm1 :
      (T.π (h - 1)).toFun (State.negate ((T.π (k - 1)).toFun x)) =
        State.negate ((T.π (h - 1)).toFun ((T.π (k - 1)).toFun x)) := by
    exact AddMap.map_negate (AddMap.ofProjection (T.π (h - 1))) ((T.π (k - 1)).toFun x)
  rw [hneg_h, hneg_hm1]
  have hle_k : h ≤ k := Nat.le_of_lt hlt
  have hle_k1 : h ≤ k - 1 := Nat.le_sub_one_of_lt hlt
  have hm1_le_k : h - 1 ≤ k := Nat.le_trans (Nat.sub_le h 1) hle_k
  have hm1_le_k1 : h - 1 ≤ k - 1 := Nat.le_trans (Nat.sub_le h 1) hle_k1
  rw [nested_proj_comp T h k hle_k x,
    nested_proj_comp T h (k - 1) hle_k1 x,
    nested_proj_comp T (h - 1) k hm1_le_k x,
    nested_proj_comp T (h - 1) (k - 1) hm1_le_k1 x]
  rw [State.add_negate_right, State.add_negate_right]
  exact State.sub_self State.zero

private theorem incrementProj_orthog_gt (T : HorizonTower) (h k : Nat) (hlt : h < k) (x : State) :
    incrementProj T k (incrementProj T h x) = State.zero := by
  change State.sub
      ((T.π k).toFun (State.add ((T.π h).toFun x) (State.negate ((T.π (h - 1)).toFun x))))
      ((T.π (k - 1)).toFun (State.add ((T.π h).toFun x) (State.negate ((T.π (h - 1)).toFun x))))
      = State.zero
  rw [(T.π k).map_add, (T.π (k - 1)).map_add]
  have hneg_k :
      (T.π k).toFun (State.negate ((T.π (h - 1)).toFun x)) =
        State.negate ((T.π k).toFun ((T.π (h - 1)).toFun x)) := by
    exact AddMap.map_negate (AddMap.ofProjection (T.π k)) ((T.π (h - 1)).toFun x)
  have hneg_km1 :
      (T.π (k - 1)).toFun (State.negate ((T.π (h - 1)).toFun x)) =
        State.negate ((T.π (k - 1)).toFun ((T.π (h - 1)).toFun x)) := by
    exact AddMap.map_negate (AddMap.ofProjection (T.π (k - 1))) ((T.π (h - 1)).toFun x)
  rw [hneg_k, hneg_km1]
  have hle_k1 : h ≤ k - 1 := Nat.le_sub_one_of_lt hlt
  have hle_k : h ≤ k := Nat.le_of_lt hlt
  have hm1_le_k1 : h - 1 ≤ k - 1 := Nat.le_trans (Nat.sub_le h 1) hle_k1
  have hm1_le_k : h - 1 ≤ k := Nat.le_trans (Nat.sub_le h 1) hle_k
  rw [nested_proj_comp_ge T k h hle_k x,
    nested_proj_comp_ge T k (h - 1) hm1_le_k x,
    nested_proj_comp_ge T (k - 1) h hle_k1 x,
    nested_proj_comp_ge T (k - 1) (h - 1) hm1_le_k1 x]
  calc
    State.sub (State.sub ((T.π h).toFun x) ((T.π (h - 1)).toFun x))
        (State.sub ((T.π h).toFun x) ((T.π (h - 1)).toFun x))
        = State.zero := by
            exact State.sub_self (State.sub ((T.π h).toFun x) ((T.π (h - 1)).toFun x))

/-- Distinct horizon bands are algebraically orthogonal. -/
theorem increment_orthogonality (T : HorizonTower) (h k : Nat) (hne : h ≠ k) (x : State) :
    incrementProj T h (incrementProj T k x) = State.zero := by
  cases Nat.lt_or_gt_of_ne hne with
  | inl hlt =>
      exact incrementProj_orthog_lt T h k hlt x
  | inr hgt =>
      exact incrementProj_orthog_gt T k h hgt x

end CoherenceCalculus
