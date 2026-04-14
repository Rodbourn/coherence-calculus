import CoherenceCalculus.Foundation.DyadicPointCore

/-!
# Foundation.DyadicNormalizationCore

Canonical normalization of ambiguous dyadic threads.

The only binary ambiguity on the unit dyadic line comes from a left step
followed by an all-right tail. This module defines the corresponding carry
operation and proves that the carried sequence is canonical while preserving the
same limiting boundary point.
-/

namespace CoherenceCalculus

/-- A carry site is a left digit followed only by right digits. -/
def CarrySite (digits : Nat → BinaryDigit) (N : Nat) : Prop :=
  digits N = BinaryDigit.left ∧ ∀ m, N < m → digits m = BinaryDigit.right

/-- A binary digit sequence is normalized when it has no carry site. -/
def DigitSequenceNormalized (digits : Nat → BinaryDigit) : Prop :=
  ∀ N, ¬ CarrySite digits N

/-- Carry a left-followed-by-right-tail sequence into its canonical form. -/
def carrySequence (digits : Nat → BinaryDigit) (N : Nat) : Nat → BinaryDigit :=
  fun m =>
    if _ : m < N then
      digits m
    else if _ : m = N then
      BinaryDigit.right
    else
      BinaryDigit.left

/-- Before the carry site, the carried sequence agrees with the original. -/
theorem carrySequence_before (digits : Nat → BinaryDigit) (N m : Nat)
    (h : m < N) :
    carrySequence digits N m = digits m := by
  unfold carrySequence
  rw [dif_pos h]

/-- At the carry site, the carried sequence flips to the right digit. -/
theorem carrySequence_at (digits : Nat → BinaryDigit) (N : Nat) :
    carrySequence digits N N = BinaryDigit.right := by
  unfold carrySequence
  rw [dif_neg (Nat.lt_irrefl N)]
  rw [dif_pos rfl]

/-- After the carry site, the carried sequence stays on the left branch. -/
theorem carrySequence_after (digits : Nat → BinaryDigit) (N m : Nat)
    (h : N < m) :
    carrySequence digits N m = BinaryDigit.left := by
  unfold carrySequence
  rw [dif_neg (Nat.not_lt_of_ge (Nat.le_of_lt h))]
  have hne : m ≠ N := by
    intro hm
    have : N < N := by
      rw [hm] at h
      exact h
    exact Nat.lt_irrefl N this
  rw [dif_neg hne]

/-- The sibling dyadic children of one interval share a boundary point. -/
theorem sibling_children_share_boundary (I : DyadicInterval n) :
    (leftChildInterval I).rightIndex = (rightChildInterval I).leftIndex := by
  rfl

/-- A right child of the left interval and a left child of the right interval
continue to share the same boundary point. -/
theorem carried_children_share_boundary {I J : DyadicInterval n}
    (h : I.rightIndex = J.leftIndex) :
    (rightChildInterval I).rightIndex = (leftChildInterval J).leftIndex := by
  dsimp [rightChildInterval, leftChildInterval]
  rw [h]

/-- Up to the carry site, the carried interval thread has the same left
endpoint index as the original. -/
theorem carrySequence_prefix_leftIndex_eq (digits : Nat → BinaryDigit) (N m : Nat)
    (h : m ≤ N) :
    (intervalsOfDigits (carrySequence digits N) m).leftIndex =
      (intervalsOfDigits digits m).leftIndex := by
  induction m with
  | zero =>
      rfl
  | succ m ih =>
      have hmN : m < N := Nat.lt_of_succ_le h
      have hprev : m ≤ N := Nat.le_trans (Nat.le_succ m) h
      have hdigit : carrySequence digits N m = digits m := carrySequence_before digits N m hmN
      rw [intervalsOfDigits_leftIndex_step (carrySequence digits N) m]
      rw [intervalsOfDigits_leftIndex_step digits m]
      rw [hdigit]
      cases hdm : digits m with
      | left =>
          simp [hdm, ih hprev]
      | right =>
          simp [hdm, ih hprev]

/-- The carry operation removes the ambiguous all-right tail. -/
theorem carrySequence_normalized (digits : Nat → BinaryDigit) (N : Nat) :
    DigitSequenceNormalized (carrySequence digits N) := by
  intro M
  intro hM
  rcases hM with ⟨hleft, htail⟩
  by_cases hMN : M < N
  · have hbad := htail (N + 1) (Nat.lt_trans hMN (Nat.lt_succ_self N))
    have hleftTail : carrySequence digits N (N + 1) = BinaryDigit.left := by
      exact carrySequence_after digits N (N + 1) (Nat.lt_succ_self N)
    rw [hleftTail] at hbad
    cases hbad
  · by_cases hEq : M = N
    · rw [hEq] at hleft
      rw [carrySequence_at digits N] at hleft
      cases hleft
    · have hNM : N < M := by
        have hge : N ≤ M := Nat.le_of_not_gt hMN
        exact Nat.lt_of_le_of_ne hge (Ne.symm hEq)
      have hnext : M < M + 1 := Nat.lt_succ_self M
      have hbad := htail (M + 1) hnext
      have hleftTail : carrySequence digits N (M + 1) = BinaryDigit.left := by
        exact carrySequence_after digits N (M + 1) (Nat.lt_trans hNM hnext)
      rw [hleftTail] at hbad
      cases hbad

/-- At the first ambiguous stage, the original and carried digit threads share
the same dyadic boundary point. -/
theorem carrySequence_boundary_base (digits : Nat → BinaryDigit) (N : Nat)
    (hsite : CarrySite digits N) :
    (intervalsOfDigits digits (N + 1)).rightIndex =
      (intervalsOfDigits (carrySequence digits N) (N + 1)).leftIndex := by
  rcases hsite with ⟨hleft, _⟩
  have hprefix :
      (intervalsOfDigits (carrySequence digits N) N).leftIndex =
        (intervalsOfDigits digits N).leftIndex := by
    exact carrySequence_prefix_leftIndex_eq digits N N (Nat.le_refl N)
  rw [intervalsOfDigits_rightIndex_step digits N]
  rw [hleft]
  rw [intervalsOfDigits_leftIndex_step (carrySequence digits N) N]
  rw [carrySequence_at digits N]
  rw [hprefix]

/-- If two dyadic threads meet at a boundary point and the next refinement
chooses the right child on one side and the left child on the other, the shared
boundary persists one stage later. -/
theorem boundary_right_to_left_step
    {I J : DyadicInterval n}
    (h : I.rightIndex = J.leftIndex) :
    (rightChildInterval I).rightIndex = (leftChildInterval J).leftIndex := by
  exact carried_children_share_boundary h

/-- The carried thread preserves the same dyadic boundary point at every later
stage. -/
theorem carrySequence_boundary_preserved (digits : Nat → BinaryDigit) (N k : Nat)
    (hsite : CarrySite digits N) :
    (intervalsOfDigits digits (N + 1 + k)).rightIndex =
      (intervalsOfDigits (carrySequence digits N) (N + 1 + k)).leftIndex := by
  induction k with
  | zero =>
      simpa [Nat.add_zero] using carrySequence_boundary_base digits N hsite
  | succ k ih =>
      have horig :
          digits (N + 1 + k) = BinaryDigit.right := by
        have hNk : N < N + 1 + k := by
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self N) (Nat.le_add_right (N + 1) k)
        exact hsite.2 (N + 1 + k) hNk
      have hcarry :
          carrySequence digits N (N + 1 + k) = BinaryDigit.left := by
        have hNk : N < N + 1 + k := by
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self N) (Nat.le_add_right (N + 1) k)
        exact carrySequence_after digits N (N + 1 + k) hNk
      have hprev :
          (intervalsOfDigits digits (N + 1 + k)).rightIndex =
            (intervalsOfDigits (carrySequence digits N) (N + 1 + k)).leftIndex := ih
      have horig' : digits (N + (1 + k)) = BinaryDigit.right := by
        simpa [Nat.add_assoc] using horig
      have hcarry' : carrySequence digits N (N + (1 + k)) = BinaryDigit.left := by
        simpa [Nat.add_assoc] using hcarry
      calc
        (intervalsOfDigits digits (N + 1 + (k + 1))).rightIndex
            = 2 * (intervalsOfDigits digits (N + 1 + k)).rightIndex := by
                have hstep := intervalsOfDigits_rightIndex_step digits (N + (1 + k))
                rw [horig'] at hstep
                simpa [Nat.add_assoc] using hstep
        _ = 2 * (intervalsOfDigits (carrySequence digits N) (N + 1 + k)).leftIndex := by
              rw [hprev]
        _ = (intervalsOfDigits (carrySequence digits N) (N + 1 + (k + 1))).leftIndex := by
              have hstep :=
                intervalsOfDigits_leftIndex_step (carrySequence digits N) (N + (1 + k))
              rw [hcarry'] at hstep
              symm
              simpa [Nat.add_assoc] using hstep

end CoherenceCalculus
