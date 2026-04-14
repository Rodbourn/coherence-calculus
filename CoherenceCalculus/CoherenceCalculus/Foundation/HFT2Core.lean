import CoherenceCalculus.Foundation.MetricCore

/-!
# Foundation.HFT2Core

Finite horizon telescoping in energy form.

This is the rebuilt norm-squared half of HFT-2. The faithful infinite-limit
statement is left for a later analytic layer.
-/

namespace CoherenceCalculus

/-- Monotone refinement list starting from an initial horizon. -/
def HorizonChain : Nat → List Nat → Prop
  | _, [] => True
  | h₀, h₁ :: hs => h₀ ≤ h₁ ∧ HorizonChain h₁ hs

/-- Energy along a finite telescoping chain. -/
def telescopingEnergyChain (T : EnergyHorizonTower) (x : State) : Nat → List Nat → Nat
  | h₀, [] => State.energy (shadowProj T.toHorizonTower h₀ x)
  | h₀, h₁ :: hs =>
      State.energy (incrementBetween T.toHorizonTower h₀ h₁ x) +
      telescopingEnergyChain T x h₁ hs

/-- Finite energy telescope: the initial shadow energy decomposes into the sum
of increment energies plus the terminal shadow energy. -/
theorem HFT2_finite_energy
    (T : EnergyHorizonTower) (x : State) (h₀ : Nat) (hs : List Nat)
    (hmono : HorizonChain h₀ hs) :
    State.energy (shadowProj T.toHorizonTower h₀ x) =
      telescopingEnergyChain T x h₀ hs := by
  induction hs generalizing h₀ with
  | nil =>
      rfl
  | cons h₁ hs ih =>
      rcases hmono with ⟨hle, hrest⟩
      dsimp [telescopingEnergyChain]
      rw [pair_telescope_energy T h₀ h₁ hle, ih h₁ hrest]

/-- Three-level finite HFT-2 as a concrete corollary. -/
theorem HFT2_three_level_energy
    (T : EnergyHorizonTower) (x : State) (h₀ h₁ h₂ : Nat)
    (h01 : h₀ ≤ h₁) (h12 : h₁ ≤ h₂) :
    State.energy (shadowProj T.toHorizonTower h₀ x) =
      State.energy (incrementBetween T.toHorizonTower h₀ h₁ x) +
      (State.energy (incrementBetween T.toHorizonTower h₁ h₂ x) +
       State.energy (shadowProj T.toHorizonTower h₂ x)) := by
  simpa [telescopingEnergyChain, HorizonChain] using
    HFT2_finite_energy T x h₀ [h₁, h₂] ⟨h01, ⟨h12, trivial⟩⟩

end CoherenceCalculus
