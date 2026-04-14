import CoherenceCalculus.Foundation.HFTCore

/-!
# Foundation.TelescopingCore

Algebraic telescoping along horizon towers.

This module proves the increment telescoping identities that underlie HFT-2.
At this stage the statements are purely additive: the norm/Pythagorean form of
HFT-2 requires a later metric layer built above this algebraic core.
-/

namespace CoherenceCalculus

/-- Increment between two horizon levels. -/
def incrementBetween (T : HorizonTower) (h₀ h₁ : Nat) : State → State :=
  fun x => State.sub ((T.π h₁).toFun x) ((T.π h₀).toFun x)

/-- Adding the increment from `h₀` to `h₁` back to the `h₀`-projection recovers
the `h₁`-projection. -/
theorem increment_between_resolution (T : HorizonTower) (h₀ h₁ : Nat) (x : State) :
    State.add ((T.π h₀).toFun x) (incrementBetween T h₀ h₁ x) = (T.π h₁).toFun x := by
  unfold incrementBetween
  exact State.add_sub_cancel_left ((T.π h₁).toFun x) ((T.π h₀).toFun x)

/-- Two-level telescoping identity for horizon shadows. -/
theorem pair_telescope (T : HorizonTower) (h₀ h₁ : Nat) (x : State) :
    State.add (incrementBetween T h₀ h₁ x) (shadowProj T h₁ x) = shadowProj T h₀ x := by
  have hs :
      State.add ((T.π h₀).toFun x) (State.add (incrementBetween T h₀ h₁ x) (shadowProj T h₁ x))
        =
      State.add ((T.π h₀).toFun x) (shadowProj T h₀ x) := by
    calc
      State.add ((T.π h₀).toFun x) (State.add (incrementBetween T h₀ h₁ x) (shadowProj T h₁ x))
          = State.add (State.add ((T.π h₀).toFun x) (incrementBetween T h₀ h₁ x)) (shadowProj T h₁ x) := by
              rw [← State.add_assoc]
      _ = State.add ((T.π h₁).toFun x) (shadowProj T h₁ x) := by
            rw [increment_between_resolution]
      _ = x := by
            rw [resolution_of_identity_state]
      _ = State.add ((T.π h₀).toFun x) (shadowProj T h₀ x) := by
            rw [resolution_of_identity_state]
  exact State.add_left_cancel hs

/-- Recursive algebraic telescope from an initial horizon through a finite list
of refinements. -/
def telescopingChain (T : HorizonTower) (x : State) : Nat → List Nat → State
  | h₀, [] => shadowProj T h₀ x
  | h₀, h₁ :: hs => State.add (incrementBetween T h₀ h₁ x) (telescopingChain T x h₁ hs)

/-- Finite telescoping chain collapses to the initial shadow component. -/
theorem telescopingChain_eq_shadow (T : HorizonTower) (x : State) (h₀ : Nat) (hs : List Nat) :
    telescopingChain T x h₀ hs = shadowProj T h₀ x := by
  induction hs generalizing h₀ with
  | nil =>
      rfl
  | cons h₁ hs ih =>
      dsimp [telescopingChain]
      rw [ih]
      exact pair_telescope T h₀ h₁ x

/-- Three-level telescoping identity as a concrete corollary. -/
theorem three_level_telescope (T : HorizonTower) (h₀ h₁ h₂ : Nat) (x : State) :
    State.add
      (incrementBetween T h₀ h₁ x)
      (State.add (incrementBetween T h₁ h₂ x) (shadowProj T h₂ x))
      =
    shadowProj T h₀ x := by
  simpa [telescopingChain] using telescopingChain_eq_shadow T x h₀ [h₁, h₂]

end CoherenceCalculus
