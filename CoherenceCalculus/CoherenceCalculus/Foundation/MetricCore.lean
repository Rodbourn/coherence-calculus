import CoherenceCalculus.Foundation.TelescopingCore

/-!
# Foundation.MetricCore

Minimal metric layer for the rebuilt horizon calculus.

This module does not introduce a full inner-product theory. Instead it defines a
concrete state energy and records exactly the orthogonal-splitting property
needed for the norm-squared form of HFT-2.
-/

namespace CoherenceCalculus

namespace SignedCount

/-- Squared magnitude of a signed count. Since normalized signed counts have at
most one nonzero side, this is the square of the visible tally. -/
def energy (z : SignedCount) : Nat :=
  z.pos * z.pos + z.neg * z.neg

end SignedCount

namespace State

/-- State energy as the sum of squared coordinate magnitudes. -/
def energy (x : State) : Nat :=
  SignedCount.energy x.c0 + SignedCount.energy x.c1 +
  SignedCount.energy x.c2 + SignedCount.energy x.c3

end State

/-- A horizon tower is energy-orthogonal if every horizon split satisfies an
exact Pythagorean energy decomposition. -/
structure EnergyHorizonTower extends HorizonTower where
  pythagorean_split : ∀ h x,
    State.energy x =
      State.energy ((π h).toFun x) + State.energy (shadowProj toHorizonTower h x)

/-- For nested horizons, projecting the earlier shadow to the later horizon
extracts exactly the increment between the two levels. -/
theorem projection_shadow_eq_increment
    (T : HorizonTower) (h₀ h₁ : Nat) (hle : h₀ ≤ h₁) (x : State) :
    (T.π h₁).toFun (shadowProj T h₀ x) = incrementBetween T h₀ h₁ x := by
  unfold shadowProj incrementBetween
  rw [State.sub_eq_add_negate, (T.π h₁).map_add]
  change
      State.add ((T.π h₁).toFun x) ((T.π h₁).toFun (State.negate ((T.π h₀).toFun x))) =
        State.sub ((T.π h₁).toFun x) ((T.π h₀).toFun x)
  have hneg : (T.π h₁).toFun (State.negate ((T.π h₀).toFun x)) =
      State.negate ((T.π h₁).toFun ((T.π h₀).toFun x)) := by
    simpa using AddMap.map_negate (AddMap.ofProjection (T.π h₁)) ((T.π h₀).toFun x)
  rw [hneg]
  rw [nested_proj_comp_ge T h₁ h₀ hle x]
  rw [State.sub_eq_add_negate]

/-- For nested horizons, taking the later shadow of the earlier shadow gives the
later shadow directly. -/
theorem shadow_of_shadow_eq_shadow
    (T : HorizonTower) (h₀ h₁ : Nat) (hle : h₀ ≤ h₁) (x : State) :
    shadowProj T h₁ (shadowProj T h₀ x) = shadowProj T h₁ x := by
  unfold shadowProj
  have hz :
      (T.π h₁).toFun (x.sub ((T.π h₀).toFun x)) = incrementBetween T h₀ h₁ x := by
    simpa [shadowProj] using projection_shadow_eq_increment T h₀ h₁ hle x
  rw [hz]
  exact State.sub_eq_right_of_add_left (pair_telescope T h₀ h₁ x)

/-- Energy version of the two-level telescoping step. -/
theorem pair_telescope_energy
    (T : EnergyHorizonTower) (h₀ h₁ : Nat) (hle : h₀ ≤ h₁) (x : State) :
    State.energy (shadowProj T.toHorizonTower h₀ x) =
      State.energy (incrementBetween T.toHorizonTower h₀ h₁ x) +
      State.energy (shadowProj T.toHorizonTower h₁ x) := by
  have hsplit := T.pythagorean_split h₁ (shadowProj T.toHorizonTower h₀ x)
  rw [projection_shadow_eq_increment T.toHorizonTower h₀ h₁ hle,
      shadow_of_shadow_eq_shadow T.toHorizonTower h₀ h₁ hle] at hsplit
  exact hsplit

end CoherenceCalculus
