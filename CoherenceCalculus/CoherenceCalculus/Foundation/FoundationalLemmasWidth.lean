import CoherenceCalculus.Foundation.HFT2Core

/-!
# Foundation.FoundationalLemmasWidth

Draft-facing foundational proof patterns rebuilt on the clean active spine.

This module exposes the manuscript-level lemma names for:
- resolution of identity
- block splitting under a horizon cut
- three-level telescoping
- Pythagorean splitting and defect energy
-/

namespace CoherenceCalculus

/-- Observable return of the shadow image of an observed input under a second
operator. This is the cross term in product compression. -/
def leakageCorrectionTerm
    (T : HorizonTower) (h : Nat) (A B : AddMap) (x : State) : State :=
  (T.π h).toFun (A (shadowProj T h (B ((T.π h).toFun x))))

/-- Defect energy as the energy of the leakage component. -/
def defectEnergy (T : HorizonTower) (h : Nat) (A : AddMap) (x : State) : Nat :=
  State.energy (leakageOp T h A.toFun x)

/-- Resolution of identity at a horizon split. -/
theorem resolution_of_identity (T : HorizonTower) (h : Nat) (x : State) :
    x = State.add ((T.π h).toFun x) (shadowProj T h x) := by
  exact (resolution_of_identity_state T h x).symm

/-- Product compression splits into observed composition plus the cross-shadow
correction term. -/
theorem block_splitting
    (T : HorizonTower) (h : Nat) (A B : AddMap) (x : State) :
    observedOp T h (fun y => A (B y)) x =
      State.add
        (observedOp T h A (observedOp T h B x))
        (leakageCorrectionTerm T h A B x) := by
  unfold observedOp leakageCorrectionTerm
  calc
    (T.π h).toFun (A (B ((T.π h).toFun x)))
        = (T.π h).toFun
            (A (State.add
                  ((T.π h).toFun (B ((T.π h).toFun x)))
                  (shadowProj T h (B ((T.π h).toFun x))))) := by
              rw [resolution_of_identity_state T h (B ((T.π h).toFun x))]
    _ = (T.π h).toFun
          (State.add (A ((T.π h).toFun (B ((T.π h).toFun x))))
                     (A (shadowProj T h (B ((T.π h).toFun x))))) := by
            rw [A.map_add]
    _ = State.add
          ((T.π h).toFun (A ((T.π h).toFun (B ((T.π h).toFun x)))))
          ((T.π h).toFun (A (shadowProj T h (B ((T.π h).toFun x))))) := by
            rw [(T.π h).map_add]
    _ = State.add
          (observedOp T h A (observedOp T h B x))
          (leakageCorrectionTerm T h A B x) := by
            unfold observedOp
            rw [(T.π h).idem (B ((T.π h).toFun x))]
            unfold leakageCorrectionTerm
            rfl

/-- Three-level telescoping for nested horizons. -/
theorem telescope_3_terms
    (T : HorizonTower) (h₀ h₁ h₂ : Nat) (x : State)
    :
    State.add
      (incrementBetween T h₀ h₁ x)
      (State.add (incrementBetween T h₁ h₂ x) (shadowProj T h₂ x)) =
      shadowProj T h₀ x := by
  exact three_level_telescope T h₀ h₁ h₂ x

/-- Horizon Pythagorean splitting into observable and shadow energy. -/
theorem pythagorean_splitting
    (T : EnergyHorizonTower) (h : Nat) (x : State) :
    State.energy x =
      State.energy ((T.π h).toFun x) +
      State.energy (shadowProj T.toHorizonTower h x) :=
  T.pythagorean_split h x

/-- Operator-action Pythagorean splitting on an observable input. -/
theorem pythagorean_splitting_observed
    (T : EnergyHorizonTower) (h : Nat) (A : AddMap) (x : State)
    (hx : (T.π h).toFun x = x) :
    State.energy (A x) =
      State.energy (observedOp T.toHorizonTower h A.toFun x) +
      defectEnergy T.toHorizonTower h A x := by
  have hsplit := pythagorean_splitting T h (A x)
  unfold defectEnergy
  rw [show observedOp T.toHorizonTower h A.toFun x = (T.π h).toFun (A x) by
        unfold observedOp
        rw [hx]]
  rw [show leakageOp T.toHorizonTower h A.toFun x = shadowProj T.toHorizonTower h (A x) by
        unfold leakageOp
        rw [hx]]
  exact hsplit

end CoherenceCalculus
