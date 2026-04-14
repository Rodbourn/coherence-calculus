import CoherenceCalculus.Foundation.ClosureCore

/-!
# Foundation.ClosureClassificationCore

Global stability classification for the closure imbalance.

This module strengthens the forcing story by proving that the stable closure
dimensions are exactly `2` and `4`. The realized nontrivial four-grade model is
therefore not only stable in a low-dimensional window; it is the unique
nontrivial stable realization globally.
-/

namespace CoherenceCalculus

theorem five_le_add_five (n : Nat) : 5 ≤ n + 5 := by
  exact Nat.le_add_left 5 n

theorem two_le_add_five (n : Nat) : 2 ≤ n + 5 := by
  exact Nat.le_trans (by decide : 2 ≤ 5) (five_le_add_five n)

theorem three_le_add_five (n : Nat) : 3 ≤ n + 5 := by
  exact Nat.le_trans (by decide : 3 ≤ 5) (five_le_add_five n)

/-- From dimension `3` onward, the pairing count dominates the dimension itself. -/
theorem pairings_ge_shifted_three (n : Nat) : n + 3 ≤ pairings (n + 3) := by
  induction n with
  | zero =>
      decide
  | succ n ih =>
      have hsucc : n + 4 ≤ pairings (n + 3) + 1 := by
        change Nat.succ (n + 3) ≤ Nat.succ (pairings (n + 3))
        exact Nat.succ_le_succ ih
      have hone : 1 ≤ n + 3 := by
        change Nat.succ 0 ≤ Nat.succ (n + 2)
        exact Nat.succ_le_succ (Nat.zero_le (n + 2))
      calc
        n + 4 ≤ pairings (n + 3) + 1 := hsucc
        _ ≤ pairings (n + 3) + (n + 3) := by
              exact Nat.add_le_add_left hone (pairings (n + 3))
        _ = pairings (n + 4) := by
              rfl

/-- From dimension `3` onward, the pairing count dominates the dimension itself. -/
theorem pairings_ge_self_of_three_le {D : Nat} (hD : 3 ≤ D) : D ≤ pairings D := by
  cases D with
  | zero =>
      cases hD
  | succ D =>
      cases D with
      | zero =>
          exfalso
          exact (by decide : ¬ 3 ≤ 1) hD
      | succ D =>
          cases D with
          | zero =>
              exfalso
              exact (by decide : ¬ 3 ≤ 2) hD
          | succ n =>
              change n + 3 ≤ pairings (n + 3)
              exact pairings_ge_shifted_three n

/-- The boundary ordering count advances by multiplying by the next visible
dimension. -/
theorem orderings_step {D : Nat} (hD : 1 ≤ D) :
    orderings (D + 1) = D * orderings D := by
  cases D with
  | zero =>
      cases hD
  | succ n =>
      rfl

/-- Doubling a natural quantity is bounded above by multiplication by any factor
at least `2`. -/
theorem double_le_mul_of_two_le {a d : Nat} (hd : 2 ≤ d) :
    a + a ≤ d * a := by
  calc
    a + a = 2 * a := by
      rw [Nat.two_mul]
    _ ≤ d * a := by
      exact Nat.mul_le_mul_right a hd

/-- Adding the same natural number on the right preserves strict inequality. -/
theorem add_lt_add_right_counting {a b : Nat} (hab : a < b) (c : Nat) :
    a + c < b + c := by
  change Nat.succ (a + c) ≤ b + c
  rw [← succ_add_counting]
  exact Nat.add_le_add_right hab c

/-- Adding the same natural number on the left preserves strict inequality. -/
theorem add_lt_add_left_counting {a b : Nat} (hab : a < b) (c : Nat) :
    c + a < c + b := by
  rw [add_comm_counting c a, add_comm_counting c b]
  exact add_lt_add_right_counting hab c

/-- Strict inequality is transitive in the counting naturals. -/
theorem lt_trans_counting {a b c : Nat} (hab : a < b) (hbc : b < c) : a < c := by
  exact Nat.lt_trans hab hbc

/-- If `a < b` and `b ≤ c`, then `a < c`. -/
theorem lt_of_lt_of_le_counting {a b c : Nat} (hab : a < b) (hbc : b ≤ c) : a < c := by
  exact Nat.le_trans hab hbc

/-- A strict inequality rules out the reverse weak inequality. -/
theorem not_le_of_lt_counting {a b : Nat} (hab : a < b) : ¬ b ≤ a := by
  intro hba
  exact (Nat.lt_irrefl a) (lt_of_lt_of_le_counting hab hba)

/-- If `a < b`, then the positive difference `b - a` cannot vanish. -/
theorem sub_ne_zero_of_lt_counting {a b : Nat} (hab : a < b) : b - a ≠ 0 := by
  intro hzero
  have hrec : b - a + a = b := sub_add_cancel_counting (Nat.le_of_lt hab)
  rw [hzero, zero_add_counting] at hrec
  rw [hrec] at hab
  exact (Nat.lt_irrefl b) hab

/-- From dimension `5` onward, boundary orderings strictly dominate bulk
pairings. -/
theorem pairings_lt_orderings_five : pairings 5 < orderings 5 := by
  decide

/-- From dimension `5` onward, boundary orderings strictly dominate bulk
pairings. -/
theorem pairings_lt_orderings_from_five (n : Nat) :
    pairings (n + 5) < orderings (n + 5) := by
  induction n with
  | zero =>
      exact pairings_lt_orderings_five
  | succ n ih =>
      have hpair : n + 5 ≤ pairings (n + 5) := by
        exact pairings_ge_self_of_three_le (three_le_add_five n)
      have hdouble_lt :
          pairings (n + 5) + pairings (n + 5) <
            orderings (n + 5) + orderings (n + 5) := by
        have hleft :
            pairings (n + 5) + pairings (n + 5) <
              orderings (n + 5) + pairings (n + 5) := by
          exact add_lt_add_right_counting ih (pairings (n + 5))
        have hright :
            orderings (n + 5) + pairings (n + 5) <
              orderings (n + 5) + orderings (n + 5) := by
          exact add_lt_add_left_counting ih (orderings (n + 5))
        exact lt_trans_counting hleft hright
      have hdouble_le :
          orderings (n + 5) + orderings (n + 5) ≤
            (n + 5) * orderings (n + 5) := by
        exact double_le_mul_of_two_le (two_le_add_five n)
      have hstep :
          orderings (n + 6) = (n + 5) * orderings (n + 5) := by
        have hone : 1 ≤ n + 5 := by
          exact Nat.le_trans (by decide : 1 ≤ 5) (five_le_add_five n)
        change orderings ((n + 5) + 1) = (n + 5) * orderings (n + 5)
        exact orderings_step hone
      have hmid : pairings (n + 5) + pairings (n + 5) < orderings (n + 6) := by
        rw [hstep]
        exact lt_of_lt_of_le_counting hdouble_lt hdouble_le
      calc
        pairings (n + 6) = pairings (n + 5) + (n + 5) := by
          rfl
        _ ≤ pairings (n + 5) + pairings (n + 5) := by
          exact Nat.add_le_add_left hpair (pairings (n + 5))
        _ < orderings (n + 6) := hmid

/-- Global boundary dominance from dimension `5` onward. -/
theorem pairings_lt_orderings_ge_five {D : Nat} (hD : 5 ≤ D) :
    pairings D < orderings D := by
  cases D with
  | zero =>
      cases hD
  | succ D =>
      cases D with
      | zero =>
          exfalso
          exact (by decide : ¬ 5 ≤ 1) hD
      | succ D =>
          cases D with
          | zero =>
              exfalso
              exact (by decide : ¬ 5 ≤ 2) hD
          | succ D =>
              cases D with
              | zero =>
                  exfalso
                  exact (by decide : ¬ 5 ≤ 3) hD
              | succ D =>
                  cases D with
                  | zero =>
                      exfalso
                      exact (by decide : ¬ 5 ≤ 4) hD
                  | succ n =>
                      change pairings (n + 5) < orderings (n + 5)
                      exact pairings_lt_orderings_from_five n

/-- From dimension `5` onward, the holographic imbalance is the negative gap
between boundary orderings and bulk pairings. -/
theorem imbalance_gap_negative_ge_five {D : Nat} (hD : 5 ≤ D) :
    holographicImbalance D =
      SignedCount.negOfNat (orderings D - pairings D) := by
  have hlt : pairings D < orderings D := pairings_lt_orderings_ge_five hD
  unfold holographicImbalance SignedCount.subCount SignedCount.addCount SignedCount.ofNat SignedCount.negate
  dsimp
  rw [zero_add_counting]
  change
    SignedCount.normalize ⟨pairings D, orderings D⟩ =
      SignedCount.negOfNat (orderings D - pairings D)
  exact SignedCount.normalize_neg_dom _ _ (not_le_of_lt_counting hlt)

/-- From dimension `5` onward, the negative gap in the holographic imbalance is
nonzero. -/
theorem negative_gap_ne_zero_ge_five {D : Nat} (hD : 5 ≤ D) :
    SignedCount.negOfNat (orderings D - pairings D) ≠ SignedCount.zero := by
  have hlt : pairings D < orderings D := pairings_lt_orderings_ge_five hD
  cases hdiff : orderings D - pairings D with
  | zero =>
      exact False.elim (sub_ne_zero_of_lt_counting hlt hdiff)
  | succ k =>
      exact SignedCount.negOfNat_succ_ne_zero k

/-- No dimension from `5` onward is closure-stable. -/
theorem not_stable_ge_five {D : Nat} (hD : 5 ≤ D) : ¬ isStable D := by
  intro hstable
  have himb := imbalance_gap_negative_ge_five hD
  have hne := negative_gap_ne_zero_ge_five hD
  exact hne (himb.symm.trans hstable)

/-- Global classification of closure-stable dimensions. -/
theorem stable_dimension_classification {D : Nat} :
    isStable D ↔ D = 2 ∨ D = 4 := by
  constructor
  · intro hstable
    cases D with
    | zero =>
        exfalso
        exact not_stable_D0 hstable
    | succ D =>
        cases D with
        | zero =>
            exfalso
            exact not_stable_D1 hstable
        | succ D =>
            cases D with
            | zero =>
                exact Or.inl rfl
            | succ D =>
                cases D with
                | zero =>
                    exfalso
                    exact not_stable_D3 hstable
                | succ D =>
                    cases D with
                    | zero =>
                        exact Or.inr rfl
                    | succ n =>
                        exfalso
                        exact not_stable_ge_five (five_le_add_five n) hstable
  · intro hstable
    rcases hstable with rfl | rfl
    · exact stable_D2
    · exact stable_D4

end CoherenceCalculus
