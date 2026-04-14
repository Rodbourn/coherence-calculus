import CoherenceCalculus.Foundation.OperatorCore
import CoherenceCalculus.Foundation.MetricCore
import CoherenceCalculus.Foundation.FoundationalLemmasWidth

/-!
# Foundation.PairingCore

Minimal pairing layer for the rebuilt finite state space.

This module does not reintroduce a full Hilbert/adjoint hierarchy. Instead it
records:
- the concrete coordinate pairing induced by the rebuilt signed-count energy
- an explicit notion of energy adjoint for additive maps
- the operator-theoretic form of defect energy whenever such an adjoint exists
-/

namespace CoherenceCalculus

namespace SignedCount

/-- Coordinate pairing induced by the rebuilt signed-count energy. -/
def pair (a b : SignedCount) : Nat :=
  a.pos * b.pos + a.neg * b.neg

/-- The pairing recovers signed-count energy on the diagonal. -/
theorem pair_self (a : SignedCount) : pair a a = energy a := by
  unfold pair energy
  rfl

end SignedCount

namespace State

/-- Canonical coordinate pairing on the rebuilt four-grade state space. -/
def pair (x y : State) : Nat :=
  SignedCount.pair x.c0 y.c0 +
  SignedCount.pair x.c1 y.c1 +
  SignedCount.pair x.c2 y.c2 +
  SignedCount.pair x.c3 y.c3

/-- The coordinate pairing recovers state energy on the diagonal. -/
theorem pair_self (x : State) : pair x x = energy x := by
  unfold pair energy
  rw [SignedCount.pair_self, SignedCount.pair_self,
      SignedCount.pair_self, SignedCount.pair_self]

end State

/-- `Astar` is an energy adjoint of `A` for the rebuilt coordinate pairing. -/
def HasEnergyAdjoint (A Astar : AddMap) : Prop :=
  ∀ x y : State, State.pair (A x) y = State.pair x (Astar y)

/-- Operator-valued defect energy when the leakage map admits an energy
adjoint. -/
def defectEnergyOperator
    (T : HorizonTower) (h : Nat) (A Astar : AddMap) : AddMap :=
  AddMap.comp Astar (AddMap.leakageMap T h A)

/-- Operator-theoretic defect-energy form under an explicit energy-adjoint
hypothesis for the leakage map. -/
theorem defectEnergy_operator_form
    (T : HorizonTower) (h : Nat) (A Astar : AddMap) (x : State)
    (hadj : HasEnergyAdjoint (AddMap.leakageMap T h A) Astar) :
    defectEnergy T h A x =
      State.pair x (defectEnergyOperator T h A Astar x) := by
  unfold defectEnergy defectEnergyOperator
  change State.energy (AddMap.leakageMap T h A x) =
    State.pair x (Astar (AddMap.leakageMap T h A x))
  rw [← hadj x (AddMap.leakageMap T h A x)]
  exact State.pair_self (AddMap.leakageMap T h A x)

end CoherenceCalculus
