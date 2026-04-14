import CoherenceCalculus.Foundation.DyadicPointCore

/-!
# Foundation.DyadicRefinementCore

Iterated dyadic refinement for digit-induced interval threads.

This module lifts one-step dyadic nestedness to arbitrary depth for the
interval thread determined by an explicit infinite binary sequence. It provides
the clean common-mesh inclusion property needed for later continuum and
completion arguments, without importing reals, quotients, or field structure.
-/

namespace CoherenceCalculus

theorem intervalsOfDigits_nested_scaled_iter_left (digits : Nat → BinaryDigit) (n k : Nat) :
    powTwo k * (intervalsOfDigits digits n).leftIndex
      ≤ (intervalsOfDigits digits (n + k)).leftIndex := by
  induction k with
  | zero =>
      simp [powTwo]
  | succ k ih =>
      have hstep := intervalsOfDigits_nested_scaled digits (n + k)
      calc
        powTwo (k + 1) * (intervalsOfDigits digits n).leftIndex
            = 2 * (powTwo k * (intervalsOfDigits digits n).leftIndex) := by
                rw [powTwo_step, Nat.mul_assoc]
        _ ≤ 2 * (intervalsOfDigits digits (n + k)).leftIndex := by
              exact Nat.mul_le_mul_left 2 ih
        _ ≤ (intervalsOfDigits digits (n + (k + 1))).leftIndex := by
              simpa [Nat.add_assoc] using hstep.1

/-- Upper-bound inclusion for the interval thread induced by a binary
sequence. -/
theorem intervalsOfDigits_nested_scaled_iter_right (digits : Nat → BinaryDigit) (n k : Nat) :
    (intervalsOfDigits digits (n + k)).rightIndex
      ≤ powTwo k * (intervalsOfDigits digits n).rightIndex := by
  induction k with
  | zero =>
      simp [powTwo]
  | succ k ih =>
      have hstep := intervalsOfDigits_nested_scaled digits (n + k)
      calc
        (intervalsOfDigits digits (n + (k + 1))).rightIndex
            ≤ 2 * (intervalsOfDigits digits (n + k)).rightIndex := by
              simpa [Nat.add_assoc] using hstep.2
        _ ≤ 2 * (powTwo k * (intervalsOfDigits digits n).rightIndex) := by
              exact Nat.mul_le_mul_left 2 ih
        _ = powTwo (k + 1) * (intervalsOfDigits digits n).rightIndex := by
              rw [powTwo_step, Nat.mul_assoc]

end CoherenceCalculus
