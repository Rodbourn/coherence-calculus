import CoherenceCalculus.Foundation.BoundaryCore

/-!
# Foundation.HFTCore

First horizon-fundamental identities rebuilt above the clean operator spine.

This module starts with the defect-side identity and then upgrades it to the
exact HFT-1 form using the rebuilt state-level negation.
-/

namespace CoherenceCalculus

/-- The observed component is fixed by the horizon projection. -/
theorem projection_observed_fixed (T : HorizonTower) (h : Nat) (A : State → State) (x : State) :
    (T.π h).toFun (observedOp T h A x) = observedOp T h A x := by
  unfold observedOp
  exact (T.π h).idem (A ((T.π h).toFun x))

/-- Projecting the image of the observed component gives the observed operator
applied twice. -/
theorem projection_A_observed_eq_observed_sq
    (T : HorizonTower) (h : Nat) (A : State → State) (x : State) :
    (T.π h).toFun (A (observedOp T h A x)) =
      observedOp T h A (observedOp T h A x) := by
  unfold observedOp
  rw [(T.π h).idem (A ((T.π h).toFun x))]

/-- Projecting the image of the leakage component gives the round-trip defect. -/
theorem projection_A_leakage_eq_defect
    (T : HorizonTower) (h : Nat) (A : State → State) (x : State) :
    (T.π h).toFun (A (leakageOp T h A x)) = defectOp T h A x := by
  unfold defectOp returnOp
  rw [leakage_shadow_fixed]

/-- Additive HFT-1: for a nilpotent additive map, the square of the observed
operator and the round-trip defect sum to zero. -/
theorem HFT1_zero_sum (T : HorizonTower) (h : Nat) (A : AddMap) (x : State)
    (hA : isNilpotent A.toFun) :
    State.add
      (observedOp T h A.toFun (observedOp T h A.toFun x))
      (defectOp T h A.toFun x)
      =
    State.zero := by
  have hsplit : State.add (observedOp T h A.toFun x) (leakageOp T h A.toFun x) =
      A ((T.π h).toFun x) := by
    exact observed_leakage_split T h A.toFun x
  have hAapplied :
      State.add (A (observedOp T h A.toFun x)) (A (leakageOp T h A.toFun x)) = State.zero := by
    calc
      State.add (A (observedOp T h A.toFun x)) (A (leakageOp T h A.toFun x))
          = A (State.add (observedOp T h A.toFun x) (leakageOp T h A.toFun x)) := by
              rw [← A.map_add]
      _ = A (A ((T.π h).toFun x)) := by
            rw [hsplit]
      _ = State.zero := by
            exact hA ((T.π h).toFun x)
  have hproj := congrArg (fun z => (T.π h).toFun z) hAapplied
  change
      (T.π h).toFun (State.add (A (observedOp T h A.toFun x)) (A (leakageOp T h A.toFun x)))
        =
      (T.π h).toFun State.zero at hproj
  rw [(T.π h).map_add, (T.π h).map_zero] at hproj
  rw [projection_A_observed_eq_observed_sq, projection_A_leakage_eq_defect] at hproj
  exact hproj

/-- General HFT-1: for any nilpotent additive map, the square of the observed
operator equals the negation of the round-trip defect. -/
theorem HFT1_general_nilpotent (T : HorizonTower) (h : Nat) (A : AddMap) (x : State)
    (hA : isNilpotent A.toFun) :
    observedOp T h A.toFun (observedOp T h A.toFun x) =
      State.negate (defectOp T h A.toFun x) := by
  exact State.eq_negate_of_add_eq_zero (HFT1_zero_sum T h A x hA)

/-- Backward-compatible name for the general nilpotent form of HFT-1. -/
theorem HFT1_exact (T : HorizonTower) (h : Nat) (A : AddMap) (x : State)
    (hA : isNilpotent A.toFun) :
    observedOp T h A.toFun (observedOp T h A.toFun x) =
      State.negate (defectOp T h A.toFun x) :=
  HFT1_general_nilpotent T h A x hA

/-- Coherence-calculus HFT-1: the observed cut of the canonical full boundary
fails to close exactly by the round-trip defect. -/
theorem HFT1_boundary_exact
    (T : HorizonTower) (h : Nat) (x : State) :
    observedBoundary T h (observedBoundary T h x) =
      State.negate (boundaryDefect T h x) := by
  exact HFT1_general_nilpotent T h trueBoundary x trueBoundary_nilpotent

/-- Backward-compatible name for the coherence-calculus specialization of
HFT-1. -/
theorem observedBoundary_square_eq_neg_defect
    (T : HorizonTower) (h : Nat) (x : State) :
    observedBoundary T h (observedBoundary T h x) =
      State.negate (boundaryDefect T h x) :=
  HFT1_boundary_exact T h x

/-- The full coherence boundary closes on itself before any horizon cut is
applied. -/
theorem fullBoundary_closes (x : State) :
    trueBoundary (trueBoundary x) = State.zero := by
  exact trueBoundary_nilpotent x

end CoherenceCalculus
