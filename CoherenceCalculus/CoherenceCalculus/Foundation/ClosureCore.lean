/-
# Foundation.ClosureCore

Closure arithmetic stated entirely in the rebuilt counting foundation.

This layer defines the basic counting functions used by the draft and expresses
the holographic imbalance as a derived signed count rather than an imported
integer.
-/

import CoherenceCalculus.Foundation.SignedCount

namespace CoherenceCalculus

/-- Factorial counting function. -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-- Binomial coefficient `C(n,k)` via factorial counting. -/
def choose (n k : Nat) : Nat :=
  if k > n then 0
  else factorial n / (factorial k * factorial (n - k))

/-- Bulk pairings at dimension `D`, counted recursively by adjoining one new
characteristic at a time. Each new characteristic pairs with all previously
visible ones. -/
def pairings : Nat → Nat
  | 0 => 0
  | n + 1 => pairings n + n

/-- Boundary orderings at dimension `D`. -/
def orderings (D : Nat) : Nat := factorial (D - 1)

/-- Holographic imbalance as a derived signed count. -/
def holographicImbalance (D : Nat) : SignedCount :=
  SignedCount.subCount (SignedCount.ofNat (pairings D)) (SignedCount.ofNat (orderings D))

/-- Stability means exact bulk-boundary cancellation in signed counts. -/
def isStable (D : Nat) : Prop :=
  holographicImbalance D = SignedCount.zero

/-- At dimension 0, the imbalance is -1 in signed-count form. -/
theorem imbalance_D0 :
    holographicImbalance 0 = SignedCount.negOfNat 1 := by
  unfold holographicImbalance pairings orderings
  apply SignedCount.ext <;> rfl

/-- At dimension 1, the imbalance is -1 in signed-count form. -/
theorem imbalance_D1 :
    holographicImbalance 1 = SignedCount.negOfNat 1 := by
  unfold holographicImbalance pairings orderings
  apply SignedCount.ext <;> rfl

/-- At dimension 2, bulk and boundary counts cancel exactly. -/
theorem stable_D2 : isStable 2 := by
  unfold isStable holographicImbalance pairings orderings
  apply SignedCount.ext <;> rfl

/-- At dimension 3, the imbalance is +1 in signed-count form. -/
theorem barrier_D3 :
    holographicImbalance 3 = SignedCount.ofNat 1 := by
  unfold holographicImbalance pairings orderings
  apply SignedCount.ext <;> rfl

/-- At dimension 4, bulk and boundary counts cancel exactly. -/
theorem stable_D4 : isStable 4 := by
  unfold isStable holographicImbalance pairings orderings
  apply SignedCount.ext <;> rfl

/-- At dimension 5, the imbalance is -14 in signed-count form. -/
theorem imbalance_D5 :
    holographicImbalance 5 = SignedCount.negOfNat 14 := by
  unfold holographicImbalance pairings orderings
  apply SignedCount.ext <;> rfl

/-- At dimension 6, the imbalance is -105 in signed-count form. -/
theorem imbalance_D6 :
    holographicImbalance 6 = SignedCount.negOfNat 105 := by
  unfold holographicImbalance pairings orderings
  apply SignedCount.ext <;> rfl

/-- Dimension 0 is not stable. -/
theorem not_stable_D0 : ¬ isStable 0 := by
  intro h
  have himb : holographicImbalance 0 = SignedCount.negOfNat 1 := imbalance_D0
  rw [h] at himb
  exact SignedCount.negOfNat_succ_ne_zero 0 himb.symm

/-- Dimension 1 is not stable. -/
theorem not_stable_D1 : ¬ isStable 1 := by
  intro h
  have himb : holographicImbalance 1 = SignedCount.negOfNat 1 := imbalance_D1
  rw [h] at himb
  exact SignedCount.negOfNat_succ_ne_zero 0 himb.symm

/-- Dimension 3 is not stable. -/
theorem not_stable_D3 : ¬ isStable 3 := by
  intro h
  have himb : holographicImbalance 3 = SignedCount.ofNat 1 := barrier_D3
  rw [h] at himb
  exact SignedCount.ofNat_succ_ne_zero 0 himb.symm

/-- Dimension 5 is not stable. -/
theorem not_stable_D5 : ¬ isStable 5 := by
  intro h
  have himb : holographicImbalance 5 = SignedCount.negOfNat 14 := imbalance_D5
  rw [h] at himb
  have hne : SignedCount.negOfNat 14 ≠ SignedCount.zero :=
    SignedCount.negOfNat_succ_ne_zero 13
  exact hne himb.symm

/-- Dimension 6 is not stable. -/
theorem not_stable_D6 : ¬ isStable 6 := by
  intro h
  have himb : holographicImbalance 6 = SignedCount.negOfNat 105 := imbalance_D6
  rw [h] at himb
  have hne : SignedCount.negOfNat 105 ≠ SignedCount.zero :=
    SignedCount.negOfNat_succ_ne_zero 104
  exact hne himb.symm

end CoherenceCalculus
