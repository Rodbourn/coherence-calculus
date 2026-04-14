import CoherenceCalculus.Foundation.HFTCore

/-!
# Foundation.HFTExamplesCore

Small explicit witness configurations used in the manuscript-facing HFT layer.
-/

namespace CoherenceCalculus

/-- First basis-like state. -/
def e0 : State :=
  ⟨SignedCount.ofNat 1, SignedCount.zero, SignedCount.zero, SignedCount.zero⟩

/-- Projection onto the first coordinate. -/
def silentLeakProjection : Projection where
  toFun := fun x => ⟨x.c0, SignedCount.zero, SignedCount.zero, SignedCount.zero⟩
  map_add := by
    intro x y
    apply State.ext
    · rfl
    · exact (SignedCount.zero_addCount SignedCount.zero).symm
    · exact (SignedCount.zero_addCount SignedCount.zero).symm
    · exact (SignedCount.zero_addCount SignedCount.zero).symm
  map_zero := by
    rfl
  idem := by
    intro x
    apply State.ext <;> rfl

/-- Constant horizon tower at the silent-leak projection. -/
def silentLeakTower : HorizonTower where
  π := fun _ => silentLeakProjection
  nested := by
    intro _ _ _ x
    exact silentLeakProjection.idem x
  nested_ge := by
    intro _ _ _ x
    exact silentLeakProjection.idem x

/-- Nilpotent map sending the visible coordinate into the shadow and killing the
shadow on a second application. -/
def silentLeakMap : AddMap where
  toFun := fun x => ⟨SignedCount.zero, x.c0, SignedCount.zero, SignedCount.zero⟩
  map_add := by
    intro x y
    apply State.ext
    · exact (SignedCount.zero_addCount SignedCount.zero).symm
    · rfl
    · exact (SignedCount.zero_addCount SignedCount.zero).symm
    · exact (SignedCount.zero_addCount SignedCount.zero).symm
  map_zero := by
    rfl

/-- The silent-leak map is nilpotent. -/
theorem silentLeak_nilpotent : isNilpotent silentLeakMap.toFun := by
  intro x
  apply State.ext <;> rfl

/-- Under the silent-leak tower, the witness `e0` leaks into the shadow. -/
theorem silentLeak_witness_nonzero :
    leakageOp silentLeakTower 0 silentLeakMap.toFun e0 ≠ State.zero := by
  intro hzero
  have hcoord : (leakageOp silentLeakTower 0 silentLeakMap.toFun e0).c1 = State.zero.c1 :=
    congrArg State.c1 hzero
  change SignedCount.ofNat 1 = SignedCount.zero at hcoord
  exact SignedCount.ofNat_succ_ne_zero 0 hcoord

/-- Standard silent-leak witness: observed closure is algebraically exact,
leakage is nonzero, and the round-trip defect vanishes. -/
theorem silent_leak_configuration :
    ∃ T : HorizonTower, ∃ h : Nat, ∃ d : AddMap, ∃ x : State,
      isNilpotent d.toFun ∧
      observedOp T h d.toFun (observedOp T h d.toFun x) = State.zero ∧
      leakageOp T h d.toFun x ≠ State.zero ∧
      defectOp T h d.toFun x = State.zero := by
  refine ⟨silentLeakTower, 0, silentLeakMap, e0, silentLeak_nilpotent, ?_, ?_, ?_⟩
  · apply State.ext <;> rfl
  · exact silentLeak_witness_nonzero
  · apply State.ext <;> rfl

end CoherenceCalculus
