import CoherenceCalculus.Foundation.OperatorCore

/-!
# Foundation.BoundaryCore

Canonical boundary data for the rebuilt coherence-calculus spine.

This module makes the full-space boundary explicit instead of treating the
nilpotent operator in HFT-1 as an arbitrary input. The guiding picture is:

- the full coherence space carries a true boundary `d`
- `d^2 = 0` in the full space
- observation is a horizon cut of that full boundary

HFT-1 can then be specialized to this canonical boundary without any extra
nilpotency premise.
-/

namespace CoherenceCalculus

/-- The full coherence boundary lowers the odd grades and annihilates the even
grades. On the rebuilt four-grade state space this is the canonical
boundary-of-boundary-zero operator. -/
def trueBoundaryFun (x : State) : State :=
  ⟨x.c1, SignedCount.zero, x.c3, SignedCount.zero⟩

/-- The full coherence boundary packaged as an additive map. -/
def trueBoundary : AddMap where
  toFun := trueBoundaryFun
  map_add := by
    intro x y
    apply State.ext
    · rfl
    · exact SignedCount.zero_addCount SignedCount.zero
    · rfl
    · exact SignedCount.zero_addCount SignedCount.zero
  map_zero := by
    rfl

/-- The full boundary closes on itself in the rebuilt coherence space. -/
theorem trueBoundary_nilpotent : isNilpotent trueBoundary.toFun := by
  intro x
  apply State.ext
  · rfl
  · rfl
  · rfl
  · rfl

/-- Observation is the horizon cut of the full coherence boundary. -/
def observedBoundary (T : HorizonTower) (h : Nat) : State → State :=
  observedOp T h trueBoundary.toFun

/-- Observable-to-shadow transport induced by the full coherence boundary. -/
def boundaryLeakage (T : HorizonTower) (h : Nat) : State → State :=
  leakageOp T h trueBoundary.toFun

/-- Shadow-to-observable return induced by the full coherence boundary. -/
def boundaryReturn (T : HorizonTower) (h : Nat) : State → State :=
  returnOp T h trueBoundary.toFun

/-- Observational failure of closure induced by cutting the true boundary. -/
def boundaryDefect (T : HorizonTower) (h : Nat) : State → State :=
  defectOp T h trueBoundary.toFun

/-- Packaged observed boundary map. -/
def observedBoundaryMap (T : HorizonTower) (h : Nat) : AddMap :=
  AddMap.observedMap T h trueBoundary

/-- Packaged defect map induced by the full boundary. -/
def boundaryDefectMap (T : HorizonTower) (h : Nat) : AddMap :=
  AddMap.defectMap T h trueBoundary

end CoherenceCalculus
