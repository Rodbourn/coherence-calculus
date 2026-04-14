import CoherenceCalculus.Foundation.TowerCalculusCore

/-!
# Foundation.HolographicDefectCore

Cross-block commutator defect language on the rebuilt additive operator spine.

This module rebuilds the manuscript's observable/shadow commutator terminology
without reintroducing the archived `LinOp` layer.
-/

namespace CoherenceCalculus

/-- Abstract pairing and ordering operators on the rebuilt state space. -/
structure PairingOrdering where
  pairing : AddMap
  ordering : AddMap

/-- The commutator of the pairing and ordering operators. -/
def commutator (ops : PairingOrdering) : AddMap :=
  AddMap.sub
    (AddMap.comp ops.pairing ops.ordering)
    (AddMap.comp ops.ordering ops.pairing)

/-- The observed commutator at a horizon cut. -/
def observedCommutator (T : HorizonTower) (h : Nat) (ops : PairingOrdering) : AddMap :=
  AddMap.observedMap T h (commutator ops)

/-- The coherence defect of the commutator at a horizon cut. -/
def commutatorCoherenceDefect
    (T : HorizonTower) (h : Nat) (ops : PairingOrdering) (x : State) : State :=
  coherenceDefect T h (commutator ops) x

/-- A state is coherently stable when the observed commutator vanishes on it. -/
def isCoherentlyStable
    (T : HorizonTower) (h : Nat) (ops : PairingOrdering) (x : State) : Prop :=
  observedCommutator T h ops x = State.zero

/-- On an observable state, coherent stability is exactly the vanishing of the
projected commutator. -/
theorem coherent_stability_observable
    (T : HorizonTower) (h : Nat) (ops : PairingOrdering) (x : State)
    (hx : (T.π h).toFun x = x) :
    isCoherentlyStable T h ops x ↔
      (T.π h).toFun (commutator ops x) = State.zero := by
  unfold isCoherentlyStable observedCommutator AddMap.observedMap observedOp
  change (T.π h).toFun (commutator ops ((T.π h).toFun x)) = State.zero ↔
    (T.π h).toFun (commutator ops x) = State.zero
  rw [hx]

/-- The commutator decomposes into observable, cross-block, and shadow pieces
under any horizon split. -/
theorem crossBlockCommutatorDefect
    (T : HorizonTower) (h : Nat) (ops : PairingOrdering) (x : State) :
    commutator ops x =
      State.add
        (observedCommutator T h ops x)
        (State.add
          (blockPQ (T.π h) (commutator ops) x)
          (State.add
            (blockQP (T.π h) (commutator ops) x)
            (blockQQ (T.π h) (commutator ops) x))) := by
  exact blockDecomposition (T.π h) (commutator ops) x

end CoherenceCalculus
