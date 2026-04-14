import CoherenceCalculus.Foundation.NatCore

/-!
# Foundation.CancellationCore

Minimal natural-number cancellation and subtraction lemmas for the rebuilt
foundation.

This module exists to support later signed-count normalization and cancellation
proofs without forcing those arguments to depend on ad hoc arithmetic inside
higher layers.
-/

namespace CoherenceCalculus

/-- Adding zero on the right does nothing. -/
theorem add_zero_counting (a : Nat) : a + 0 = a := rfl

/-- Adding zero on the left does nothing. -/
theorem zero_add_counting (a : Nat) : 0 + a = a := by
  induction a with
  | zero => rfl
  | succ a ih =>
      change Nat.succ (0 + a) = Nat.succ a
      rw [ih]

/-- Successor on the right distributes through addition definitionally. -/
theorem add_succ_counting (a b : Nat) : a + Nat.succ b = Nat.succ (a + b) := rfl

/-- Successor on the left can be pulled through addition. -/
theorem succ_add_counting (a b : Nat) : Nat.succ a + b = Nat.succ (a + b) := by
  induction b with
  | zero => rfl
  | succ b ih =>
      change Nat.succ (Nat.succ a + b) = Nat.succ (Nat.succ (a + b))
      rw [ih]

/-- Associativity of natural-number addition, rebuilt from the counting core. -/
theorem add_assoc_counting (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction a with
  | zero =>
      calc
        (0 + b) + c = b + c := by rw [zero_add_counting]
        _ = 0 + (b + c) := by rw [zero_add_counting]
  | succ a ih =>
      calc
        (Nat.succ a + b) + c = Nat.succ (a + b) + c := by rw [succ_add_counting]
        _ = Nat.succ ((a + b) + c) := by rw [succ_add_counting]
        _ = Nat.succ (a + (b + c)) := by rw [ih]
        _ = Nat.succ a + (b + c) := by rw [succ_add_counting]

/-- Commutativity of natural-number addition, rebuilt from the counting core. -/
theorem add_comm_counting (a b : Nat) : a + b = b + a := by
  induction b with
  | zero =>
      rw [add_zero_counting, zero_add_counting]
  | succ b ih =>
      rw [add_succ_counting, succ_add_counting, ih]

/-- Regroup a four-term sum by pairing the outer and inner terms. -/
theorem add_pair_swap_counting (a b c d : Nat) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  calc
    (a + b) + (c + d) = a + (b + (c + d)) := by
      rw [add_assoc_counting a b (c + d)]
    _ = a + ((b + c) + d) := by
      rw [← add_assoc_counting b c d]
    _ = a + ((c + b) + d) := by
      rw [add_comm_counting b c]
    _ = a + (c + (b + d)) := by
      rw [add_assoc_counting c b d]
    _ = (a + c) + (b + d) := by
      rw [← add_assoc_counting a c (b + d)]

/-- If a sum of naturals is zero, the left summand is zero. -/
theorem add_eq_zero_left_counting {a b : Nat} (h : a + b = 0) : a = 0 := by
  cases a with
  | zero => rfl
  | succ n =>
      rw [succ_add_counting] at h
      exact False.elim (succ_not_zero_counting (n + b) h)

/-- If a sum of naturals is zero, the right summand is zero. -/
theorem add_eq_zero_right_counting {a b : Nat} (h : a + b = 0) : b = 0 := by
  have h' : b + a = 0 := by
    rw [add_comm_counting] at h
    exact h
  exact add_eq_zero_left_counting h'

/-- Right cancellation for natural-number addition. -/
theorem add_right_cancel_counting {a b c : Nat} (h : a + c = b + c) : a = b := by
  induction c with
  | zero =>
      rw [add_zero_counting, add_zero_counting] at h
      exact h
  | succ c ih =>
      rw [add_succ_counting, add_succ_counting] at h
      exact ih (succ_injective_counting _ _ h)

/-- Left cancellation for natural-number addition. -/
theorem add_left_cancel_counting {a b c : Nat} (h : c + a = c + b) : a = b := by
  rw [add_comm_counting c a, add_comm_counting c b] at h
  exact add_right_cancel_counting h

/-- If `b ≤ a`, then subtracting and adding back recovers `a`. -/
theorem sub_add_cancel_counting {a b : Nat} (h : b ≤ a) : a - b + b = a := by
  induction b generalizing a with
  | zero =>
      rw [Nat.sub_zero, add_zero_counting]
  | succ b ih =>
      cases a with
      | zero =>
          cases h
      | succ a =>
          have h' : b ≤ a := Nat.le_of_succ_le_succ h
          rw [Nat.succ_sub_succ_eq_sub]
          rw [add_succ_counting]
          show Nat.succ (a - b + b) = Nat.succ a
          exact congrArg Nat.succ (ih h')

/-- If `b ≤ a`, then subtracting the difference recovers `b`. -/
theorem add_sub_cancel_counting {a b : Nat} (h : b ≤ a) : a - (a - b) = b := by
  have h1 : a - (a - b) + (a - b) = a := sub_add_cancel_counting (Nat.sub_le a b)
  have h2 : b + (a - b) = a := by
    rw [add_comm_counting b (a - b)]
    exact sub_add_cancel_counting h
  exact add_right_cancel_counting (h1.trans h2.symm)

/-- Failure of `b ≤ a` means `a < b`. -/
theorem lt_of_not_ge_counting {a b : Nat} (h : ¬ b ≤ a) : a < b := by
  exact Nat.lt_of_not_ge h

/-- A positive sum cannot be zero. -/
theorem succ_add_ne_zero_counting (a b : Nat) : Nat.succ a + b ≠ 0 := by
  intro h
  rw [succ_add_counting] at h
  exact succ_not_zero_counting (a + b) h

/-- A natural equal to its successor-shifted version forces the shift to be
zero. -/
theorem add_succ_ne_self_counting (a b : Nat) : a + Nat.succ b ≠ a := by
  intro h
  have hs : a + Nat.succ b = a + 0 := by
    calc
      a + Nat.succ b = a := h
      _ = a + 0 := by rw [Nat.add_zero]
  have : Nat.succ b = 0 := add_left_cancel_counting hs
  exact succ_not_zero_counting b this

end CoherenceCalculus
