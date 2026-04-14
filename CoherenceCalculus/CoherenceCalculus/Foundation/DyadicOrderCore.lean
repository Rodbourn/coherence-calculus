import CoherenceCalculus.Foundation.DyadicPointCore

/-!
# Foundation.DyadicOrderCore

Local order facts for the clean dyadic scaffold.

This module records only the finite order data that is currently bedrock-clean in
the active root. Prefix-comparison theorems for full binary threads are left to
a later refinement layer once they can be rebuilt without `propext`.
-/

namespace CoherenceCalculus

/-- On a common mesh, one dyadic interval precedes another when its right
endpoint lies at or before the other's left endpoint. -/
def DyadicIntervalPrecedes {n : Nat} (I J : DyadicInterval n) : Prop :=
  I.rightIndex ≤ J.leftIndex

/-- Every dyadic interval has strictly increasing endpoints. -/
theorem dyadicInterval_left_lt_right (I : DyadicInterval n) :
    I.leftIndex < I.rightIndex := by
  rw [I.unit_width]
  exact Nat.lt_succ_self _

/-- Every dyadic interval has left endpoint at or before its right endpoint. -/
theorem dyadicInterval_left_le_right (I : DyadicInterval n) :
    I.leftIndex ≤ I.rightIndex := by
  exact Nat.le_of_lt (dyadicInterval_left_lt_right I)

/-- No dyadic interval precedes itself on a common mesh. -/
theorem dyadicInterval_not_precedes_self (I : DyadicInterval n) :
    ¬ DyadicIntervalPrecedes I I := by
  intro h
  dsimp [DyadicIntervalPrecedes] at h
  have hs : Nat.succ I.leftIndex ≤ I.leftIndex := by
    simpa [Nat.succ_eq_add_one] using (show I.leftIndex + 1 ≤ I.leftIndex by
      simpa [I.unit_width] using h)
  exact Nat.not_succ_le_self _ hs

/-- Dyadic interval precedence is transitive on a common mesh. -/
theorem dyadicInterval_precedes_trans {n : Nat}
    {I J K : DyadicInterval n}
    (hIJ : DyadicIntervalPrecedes I J)
    (hJK : DyadicIntervalPrecedes J K) :
    DyadicIntervalPrecedes I K := by
  dsimp [DyadicIntervalPrecedes] at *
  exact Nat.le_trans hIJ (Nat.le_trans (dyadicInterval_left_le_right J) hJK)

/-- On a common mesh, a dyadic interval is determined by its left endpoint. -/
theorem dyadicInterval_eq_of_leftIndex_eq {n : Nat}
    {I J : DyadicInterval n}
    (h : I.leftIndex = J.leftIndex) :
    I = J := by
  apply DyadicInterval.ext h
  calc
    I.rightIndex = I.leftIndex + 1 := I.unit_width
    _ = J.leftIndex + 1 := by rw [h]
    _ = J.rightIndex := J.unit_width.symm

/-- If the left endpoint of one dyadic interval lies strictly before the left
endpoint of another on the same mesh, then the first interval precedes the
second. -/
theorem dyadicInterval_precedes_of_leftIndex_lt {n : Nat}
    {I J : DyadicInterval n}
    (h : I.leftIndex < J.leftIndex) :
    DyadicIntervalPrecedes I J := by
  change I.rightIndex ≤ J.leftIndex
  calc
    I.rightIndex = I.leftIndex + 1 := I.unit_width
    _ ≤ J.leftIndex := Nat.succ_le_of_lt h

/-- Precedence on a common mesh forces strict left-endpoint order. -/
theorem dyadicInterval_leftIndex_lt_of_precedes {n : Nat}
    {I J : DyadicInterval n}
    (h : DyadicIntervalPrecedes I J) :
    I.leftIndex < J.leftIndex := by
  exact Nat.lt_of_lt_of_le (dyadicInterval_left_lt_right I) h

/-- On a common mesh, two dyadic intervals are either equal or ordered from one
side to the other. -/
theorem dyadicInterval_eq_or_precedes_or_precedes {n : Nat}
    (I J : DyadicInterval n) :
    I = J ∨ DyadicIntervalPrecedes I J ∨ DyadicIntervalPrecedes J I := by
  by_cases hlt : I.leftIndex < J.leftIndex
  · exact Or.inr (Or.inl (dyadicInterval_precedes_of_leftIndex_lt hlt))
  · have hge : J.leftIndex ≤ I.leftIndex := Nat.le_of_not_gt hlt
    by_cases hrev : J.leftIndex < I.leftIndex
    · exact Or.inr (Or.inr (dyadicInterval_precedes_of_leftIndex_lt hrev))
    · have heq : I.leftIndex = J.leftIndex := by
        have hJI : I.leftIndex ≤ J.leftIndex := Nat.le_of_not_gt hrev
        exact Nat.le_antisymm hJI hge
      exact Or.inl (dyadicInterval_eq_of_leftIndex_eq heq)

/-- Distinct dyadic intervals on a common mesh are ordered one way or the other. -/
theorem dyadicInterval_precedes_or_precedes_of_ne {n : Nat}
    {I J : DyadicInterval n}
    (h : I ≠ J) :
    DyadicIntervalPrecedes I J ∨ DyadicIntervalPrecedes J I := by
  rcases dyadicInterval_eq_or_precedes_or_precedes I J with hEq | hOrd
  · exact False.elim (h hEq)
  · exact hOrd

/-- On a common mesh, a dyadic interval is also determined by its right
endpoint. -/
theorem dyadicInterval_eq_of_rightIndex_eq {n : Nat}
    {I J : DyadicInterval n}
    (h : I.rightIndex = J.rightIndex) :
    I = J := by
  rcases dyadicInterval_eq_or_precedes_or_precedes I J with hEq | hOrd
  · exact hEq
  · rcases hOrd with hIJ | hJI
    · have hlt : I.rightIndex < J.rightIndex := by
        exact Nat.lt_of_le_of_lt hIJ (dyadicInterval_left_lt_right J)
      exact False.elim ((Nat.ne_of_lt hlt) h)
    · have hlt : J.rightIndex < I.rightIndex := by
        exact Nat.lt_of_le_of_lt hJI (dyadicInterval_left_lt_right I)
      exact False.elim ((Nat.ne_of_lt hlt) h.symm)

/-- The left and right children of a dyadic interval meet at a shared boundary
point on the finer mesh. -/
theorem child_intervals_share_boundary (I : DyadicInterval n) :
    (leftChildInterval I).rightIndex = (rightChildInterval I).leftIndex := by
  rfl

/-- On the finer mesh, the left child precedes the right child. -/
theorem leftChild_precedes_rightChild (I : DyadicInterval n) :
    DyadicIntervalPrecedes (leftChildInterval I) (rightChildInterval I) := by
  dsimp [DyadicIntervalPrecedes]
  rw [child_intervals_share_boundary]
  exact Nat.le_refl _

/-- Refining both intervals preserves precedence, regardless of the chosen
children. -/
theorem child_intervals_precede_of_precedes {n : Nat}
    {I J : DyadicInterval n}
    (h : DyadicIntervalPrecedes I J)
    (b₁ b₂ : BinaryDigit) :
    DyadicIntervalPrecedes
      (match b₁ with
       | BinaryDigit.left => leftChildInterval I
       | BinaryDigit.right => rightChildInterval I)
      (match b₂ with
       | BinaryDigit.left => leftChildInterval J
       | BinaryDigit.right => rightChildInterval J) := by
  cases b₁ <;> cases b₂
  · dsimp [DyadicIntervalPrecedes]
    exact Nat.le_trans
      (leftChild_nested_scaled I).2
      (Nat.le_trans (Nat.mul_le_mul_left 2 h) (leftChild_nested_scaled J).1)
  · dsimp [DyadicIntervalPrecedes]
    exact Nat.le_trans
      (leftChild_nested_scaled I).2
      (Nat.le_trans (Nat.mul_le_mul_left 2 h) (rightChild_nested_scaled J).1)
  · dsimp [DyadicIntervalPrecedes]
    exact Nat.le_trans
      (rightChild_nested_scaled I).2
      (Nat.le_trans (Nat.mul_le_mul_left 2 h) (leftChild_nested_scaled J).1)
  · dsimp [DyadicIntervalPrecedes]
    exact Nat.le_trans
      (rightChild_nested_scaled I).2
      (Nat.le_trans (Nat.mul_le_mul_left 2 h) (rightChild_nested_scaled J).1)

/-- The left-child construction is injective in the parent interval. -/
theorem leftChildInterval_injective {n : Nat}
    {I J : DyadicInterval n}
    (h : leftChildInterval I = leftChildInterval J) :
    I = J := by
  rcases dyadicInterval_eq_or_precedes_or_precedes I J with hEq | hOrd
  · exact hEq
  · rcases hOrd with hIJ | hJI
    · have hChild :
        DyadicIntervalPrecedes (leftChildInterval I) (leftChildInterval J) :=
          child_intervals_precede_of_precedes hIJ BinaryDigit.left BinaryDigit.left
      rw [h] at hChild
      exact False.elim (dyadicInterval_not_precedes_self (leftChildInterval J) hChild)
    · have hChild :
        DyadicIntervalPrecedes (leftChildInterval J) (leftChildInterval I) :=
          child_intervals_precede_of_precedes hJI BinaryDigit.left BinaryDigit.left
      rw [h] at hChild
      exact False.elim (dyadicInterval_not_precedes_self (leftChildInterval J) hChild)

/-- The right-child construction is injective in the parent interval. -/
theorem rightChildInterval_injective {n : Nat}
    {I J : DyadicInterval n}
    (h : rightChildInterval I = rightChildInterval J) :
    I = J := by
  rcases dyadicInterval_eq_or_precedes_or_precedes I J with hEq | hOrd
  · exact hEq
  · rcases hOrd with hIJ | hJI
    · have hChild :
        DyadicIntervalPrecedes (rightChildInterval I) (rightChildInterval J) :=
          child_intervals_precede_of_precedes hIJ BinaryDigit.right BinaryDigit.right
      rw [h] at hChild
      exact False.elim (dyadicInterval_not_precedes_self (rightChildInterval J) hChild)
    · have hChild :
        DyadicIntervalPrecedes (rightChildInterval J) (rightChildInterval I) :=
          child_intervals_precede_of_precedes hJI BinaryDigit.right BinaryDigit.right
      rw [h] at hChild
      exact False.elim (dyadicInterval_not_precedes_self (rightChildInterval J) hChild)

/-- A left child can never equal a right child on the same finer mesh. -/
theorem leftChildInterval_ne_rightChildInterval {n : Nat}
    {I J : DyadicInterval n} :
    leftChildInterval I ≠ rightChildInterval J := by
  intro h
  rcases dyadicInterval_eq_or_precedes_or_precedes I J with hEq | hOrd
  · cases hEq
    exact child_intervals_distinct I h
  · rcases hOrd with hIJ | hJI
    · have hChild :
        DyadicIntervalPrecedes (leftChildInterval I) (rightChildInterval J) :=
          child_intervals_precede_of_precedes hIJ BinaryDigit.left BinaryDigit.right
      rw [h] at hChild
      exact dyadicInterval_not_precedes_self (rightChildInterval J) hChild
    · have hChild :
        DyadicIntervalPrecedes (rightChildInterval J) (leftChildInterval I) :=
          child_intervals_precede_of_precedes hJI BinaryDigit.right BinaryDigit.left
      rw [h] at hChild
      exact dyadicInterval_not_precedes_self (rightChildInterval J) hChild

/-- Symmetric form of left-child/right-child incompatibility. -/
theorem rightChildInterval_ne_leftChildInterval {n : Nat}
    {I J : DyadicInterval n} :
    rightChildInterval I ≠ leftChildInterval J := by
  intro h
  exact leftChildInterval_ne_rightChildInterval h.symm

/-- Equality of next-stage intervals forces equality of the parent intervals. -/
theorem thread_prev_eq_of_next_eq {T U : DyadicIntervalThread} {n : Nat}
    (h : T.intervals (n + 1) = U.intervals (n + 1)) :
    T.intervals n = U.intervals n := by
  cases hT : T.refine n with
  | inl hTleft =>
      cases hU : U.refine n with
      | inl hUleft =>
          rw [hTleft, hUleft] at h
          exact leftChildInterval_injective h
      | inr hUright =>
          rw [hTleft, hUright] at h
          exact False.elim (leftChildInterval_ne_rightChildInterval h)
  | inr hTright =>
      cases hU : U.refine n with
      | inl hUleft =>
          rw [hTright, hUleft] at h
          exact False.elim (rightChildInterval_ne_leftChildInterval h)
      | inr hUright =>
          rw [hTright, hUright] at h
          exact rightChildInterval_injective h

/-- Equality of interval-thread stages at some later depth forces equality at
every earlier depth. -/
theorem thread_eq_of_eq_later {T U : DyadicIntervalThread} {n : Nat} :
    ∀ k,
      T.intervals (n + k) = U.intervals (n + k) →
        T.intervals n = U.intervals n
  | 0, h => by
      simpa using h
  | k + 1, h => by
      have hprev : T.intervals (n + k) = U.intervals (n + k) := by
        change T.intervals ((n + k) + 1) = U.intervals ((n + k) + 1) at h
        exact thread_prev_eq_of_next_eq h
      exact thread_eq_of_eq_later k hprev

/-- Equality of digit-induced intervals at a later depth forces equality at
every earlier depth. -/
theorem intervalsOfDigits_eq_of_eq_later
    {digits₁ digits₂ : Nat → BinaryDigit} {n : Nat}
    (k : Nat)
    (h : intervalsOfDigits digits₁ (n + k) = intervalsOfDigits digits₂ (n + k)) :
    intervalsOfDigits digits₁ n = intervalsOfDigits digits₂ n := by
  exact thread_eq_of_eq_later
    (T := intervalThreadOfDigits digits₁)
    (U := intervalThreadOfDigits digits₂)
    (n := n) k h

/-- If two digit-induced interval threads agree at stages `n` and `n + 1`, then
they choose the same digit at stage `n`. -/
theorem digits_eq_of_intervals_eq_step
    {digits₁ digits₂ : Nat → BinaryDigit} {n : Nat}
    (hEq : intervalsOfDigits digits₁ n = intervalsOfDigits digits₂ n)
    (hNext : intervalsOfDigits digits₁ (n + 1) = intervalsOfDigits digits₂ (n + 1)) :
    digits₁ n = digits₂ n := by
  cases h₁ : digits₁ n with
  | left =>
      cases h₂ : digits₂ n with
      | left =>
          rfl
      | right =>
          rw [intervalsOfDigits, h₁, intervalsOfDigits, h₂, hEq] at hNext
          exact False.elim (leftChildInterval_ne_rightChildInterval hNext)
  | right =>
      cases h₂ : digits₂ n with
      | left =>
          rw [intervalsOfDigits, h₁, intervalsOfDigits, h₂, hEq] at hNext
          exact False.elim (rightChildInterval_ne_leftChildInterval hNext)
      | right =>
          rfl

/-- Exact equality of digit-induced interval threads determines the digit at
every stage. -/
theorem digits_eq_of_intervals_eq_all
    {digits₁ digits₂ : Nat → BinaryDigit}
    (h : ∀ n, intervalsOfDigits digits₁ n = intervalsOfDigits digits₂ n)
    (n : Nat) :
    digits₁ n = digits₂ n := by
  exact digits_eq_of_intervals_eq_step (h n) (h (n + 1))

/-- If two interval threads share the same stage-`n` interval and both refine to
the left child, then their next intervals agree. -/
theorem thread_step_eq_of_refine_left {T U : DyadicIntervalThread} {n : Nat}
    (hEq : T.intervals n = U.intervals n)
    (hT : T.intervals (n + 1) = leftChildInterval (T.intervals n))
    (hU : U.intervals (n + 1) = leftChildInterval (U.intervals n)) :
    T.intervals (n + 1) = U.intervals (n + 1) := by
  rw [hT, hU, hEq]

/-- If two interval threads share the same stage-`n` interval and both refine
to the right child, then their next intervals agree. -/
theorem thread_step_eq_of_refine_right {T U : DyadicIntervalThread} {n : Nat}
    (hEq : T.intervals n = U.intervals n)
    (hT : T.intervals (n + 1) = rightChildInterval (T.intervals n))
    (hU : U.intervals (n + 1) = rightChildInterval (U.intervals n)) :
    T.intervals (n + 1) = U.intervals (n + 1) := by
  rw [hT, hU, hEq]

/-- If two interval threads share the same stage-`n` interval and then choose
different children, the left-refining thread precedes the right-refining thread
at stage `n + 1`. -/
theorem thread_step_precedes_of_refine_left_right
    {T U : DyadicIntervalThread} {n : Nat}
    (hEq : T.intervals n = U.intervals n)
    (hT : T.intervals (n + 1) = leftChildInterval (T.intervals n))
    (hU : U.intervals (n + 1) = rightChildInterval (U.intervals n)) :
    DyadicIntervalPrecedes (T.intervals (n + 1)) (U.intervals (n + 1)) := by
  rw [hT, hU, hEq]
  exact leftChild_precedes_rightChild (U.intervals n)

/-- If two interval threads share the same stage-`n` interval and then choose
different children, the resulting stage-`n + 1` intervals are distinct. -/
theorem thread_step_distinct_of_refine_left_right
    {T U : DyadicIntervalThread} {n : Nat}
    (hEq : T.intervals n = U.intervals n)
    (hT : T.intervals (n + 1) = leftChildInterval (T.intervals n))
    (hU : U.intervals (n + 1) = rightChildInterval (U.intervals n)) :
    T.intervals (n + 1) ≠ U.intervals (n + 1) := by
  rw [hT, hU, hEq]
  exact child_intervals_distinct (U.intervals n)

/-- If two digit-induced interval threads agree at stage `n` and both choose the
left digit at stage `n`, then their stage-`n + 1` intervals agree. -/
theorem intervalsOfDigits_step_eq_of_eq_left
    {digits₁ digits₂ : Nat → BinaryDigit} {n : Nat}
    (hEq : intervalsOfDigits digits₁ n = intervalsOfDigits digits₂ n)
    (h₁ : digits₁ n = BinaryDigit.left)
    (h₂ : digits₂ n = BinaryDigit.left) :
    intervalsOfDigits digits₁ (n + 1) = intervalsOfDigits digits₂ (n + 1) := by
  rw [intervalsOfDigits, h₁, intervalsOfDigits, h₂, hEq]

/-- If two digit-induced interval threads agree at stage `n` and both choose the
right digit at stage `n`, then their stage-`n + 1` intervals agree. -/
theorem intervalsOfDigits_step_eq_of_eq_right
    {digits₁ digits₂ : Nat → BinaryDigit} {n : Nat}
    (hEq : intervalsOfDigits digits₁ n = intervalsOfDigits digits₂ n)
    (h₁ : digits₁ n = BinaryDigit.right)
    (h₂ : digits₂ n = BinaryDigit.right) :
    intervalsOfDigits digits₁ (n + 1) = intervalsOfDigits digits₂ (n + 1) := by
  rw [intervalsOfDigits, h₁, intervalsOfDigits, h₂, hEq]

/-- If two digit-induced interval threads agree at stage `n` and then choose
left versus right, the left-choosing thread precedes the right-choosing thread
at stage `n + 1`. -/
theorem intervalsOfDigits_step_precedes_of_eq_left_right
    {digits₁ digits₂ : Nat → BinaryDigit} {n : Nat}
    (hEq : intervalsOfDigits digits₁ n = intervalsOfDigits digits₂ n)
    (h₁ : digits₁ n = BinaryDigit.left)
    (h₂ : digits₂ n = BinaryDigit.right) :
    DyadicIntervalPrecedes
      (intervalsOfDigits digits₁ (n + 1))
      (intervalsOfDigits digits₂ (n + 1)) := by
  rw [intervalsOfDigits, h₁, intervalsOfDigits, h₂, hEq]
  exact leftChild_precedes_rightChild (intervalsOfDigits digits₂ n)

/-- If two digit-induced interval threads agree at stage `n` and then choose
left versus right, their stage-`n + 1` intervals are distinct. -/
theorem intervalsOfDigits_step_distinct_of_eq_left_right
    {digits₁ digits₂ : Nat → BinaryDigit} {n : Nat}
    (hEq : intervalsOfDigits digits₁ n = intervalsOfDigits digits₂ n)
    (h₁ : digits₁ n = BinaryDigit.left)
    (h₂ : digits₂ n = BinaryDigit.right) :
    intervalsOfDigits digits₁ (n + 1) ≠ intervalsOfDigits digits₂ (n + 1) := by
  rw [intervalsOfDigits, h₁, intervalsOfDigits, h₂, hEq]
  exact child_intervals_distinct (intervalsOfDigits digits₂ n)

/-- Precedence on a common mesh forces interval inequality. -/
theorem dyadicInterval_ne_of_precedes {n : Nat}
    {I J : DyadicInterval n}
    (h : DyadicIntervalPrecedes I J) :
    I ≠ J := by
  intro hEq
  cases hEq
  exact dyadicInterval_not_precedes_self I h

/-- Once two interval threads are ordered at some stage, that order persists at
every later stage. -/
theorem thread_precedes_iter {T U : DyadicIntervalThread} {n : Nat}
    (h : DyadicIntervalPrecedes (T.intervals n) (U.intervals n))
    (k : Nat) :
    DyadicIntervalPrecedes (T.intervals (n + k)) (U.intervals (n + k)) := by
  induction k with
  | zero =>
      exact h
  | succ k ih =>
      change DyadicIntervalPrecedes (T.intervals ((n + k) + 1))
        (U.intervals ((n + k) + 1))
      cases hT : T.refine (n + k) with
      | inl hTleft =>
          cases hU : U.refine (n + k) with
          | inl hUleft =>
              rw [hTleft, hUleft]
              exact child_intervals_precede_of_precedes ih BinaryDigit.left BinaryDigit.left
          | inr hUright =>
              rw [hTleft, hUright]
              exact child_intervals_precede_of_precedes ih BinaryDigit.left BinaryDigit.right
      | inr hTright =>
          cases hU : U.refine (n + k) with
          | inl hUleft =>
              rw [hTright, hUleft]
              exact child_intervals_precede_of_precedes ih BinaryDigit.right BinaryDigit.left
          | inr hUright =>
              rw [hTright, hUright]
              exact child_intervals_precede_of_precedes ih BinaryDigit.right BinaryDigit.right

/-- Once two interval threads are ordered at some stage, they remain distinct
at every later stage. -/
theorem thread_distinct_iter_of_precedes {T U : DyadicIntervalThread} {n : Nat}
    (h : DyadicIntervalPrecedes (T.intervals n) (U.intervals n))
    (k : Nat) :
    T.intervals (n + k) ≠ U.intervals (n + k) := by
  exact dyadicInterval_ne_of_precedes (thread_precedes_iter h k)

/-- If two interval threads first diverge by choosing left versus right at stage
`n`, then all later stages remain ordered the same way. -/
theorem thread_step_precedes_iter_of_refine_left_right
    {T U : DyadicIntervalThread} {n : Nat}
    (hEq : T.intervals n = U.intervals n)
    (hT : T.intervals (n + 1) = leftChildInterval (T.intervals n))
    (hU : U.intervals (n + 1) = rightChildInterval (U.intervals n))
    (k : Nat) :
    DyadicIntervalPrecedes (T.intervals ((n + 1) + k))
      (U.intervals ((n + 1) + k)) := by
  exact thread_precedes_iter
    (n := n + 1)
    (thread_step_precedes_of_refine_left_right hEq hT hU) k

/-- If two interval threads first diverge by choosing left versus right at stage
`n`, then all later stages remain distinct. -/
theorem thread_step_distinct_iter_of_refine_left_right
    {T U : DyadicIntervalThread} {n : Nat}
    (hEq : T.intervals n = U.intervals n)
    (hT : T.intervals (n + 1) = leftChildInterval (T.intervals n))
    (hU : U.intervals (n + 1) = rightChildInterval (U.intervals n))
    (k : Nat) :
    T.intervals ((n + 1) + k) ≠ U.intervals ((n + 1) + k) := by
  exact thread_distinct_iter_of_precedes
    (n := n + 1)
    (thread_step_precedes_of_refine_left_right hEq hT hU) k

/-- Once two digit-induced interval threads are ordered at some stage, that
order persists at every later stage. -/
theorem intervalsOfDigits_precedes_iter
    {digits₁ digits₂ : Nat → BinaryDigit} {n : Nat}
    (h : DyadicIntervalPrecedes (intervalsOfDigits digits₁ n) (intervalsOfDigits digits₂ n))
    (k : Nat) :
    DyadicIntervalPrecedes (intervalsOfDigits digits₁ (n + k))
      (intervalsOfDigits digits₂ (n + k)) := by
  exact thread_precedes_iter
    (T := intervalThreadOfDigits digits₁)
    (U := intervalThreadOfDigits digits₂)
    (n := n) h k

/-- If two digit-induced interval threads first diverge by choosing left versus
right at stage `n`, then all later stages remain ordered the same way. -/
theorem intervalsOfDigits_step_precedes_iter_of_eq_left_right
    {digits₁ digits₂ : Nat → BinaryDigit} {n : Nat}
    (hEq : intervalsOfDigits digits₁ n = intervalsOfDigits digits₂ n)
    (h₁ : digits₁ n = BinaryDigit.left)
    (h₂ : digits₂ n = BinaryDigit.right)
    (k : Nat) :
    DyadicIntervalPrecedes (intervalsOfDigits digits₁ ((n + 1) + k))
      (intervalsOfDigits digits₂ ((n + 1) + k)) := by
  exact thread_precedes_iter
    (T := intervalThreadOfDigits digits₁)
    (U := intervalThreadOfDigits digits₂)
    (n := n + 1)
    (intervalsOfDigits_step_precedes_of_eq_left_right hEq h₁ h₂) k

/-- If two digit-induced interval threads first diverge by choosing left versus
right at stage `n`, then all later stages remain distinct. -/
theorem intervalsOfDigits_step_distinct_iter_of_eq_left_right
    {digits₁ digits₂ : Nat → BinaryDigit} {n : Nat}
    (hEq : intervalsOfDigits digits₁ n = intervalsOfDigits digits₂ n)
    (h₁ : digits₁ n = BinaryDigit.left)
    (h₂ : digits₂ n = BinaryDigit.right)
    (k : Nat) :
    intervalsOfDigits digits₁ ((n + 1) + k) ≠
      intervalsOfDigits digits₂ ((n + 1) + k) := by
  exact thread_distinct_iter_of_precedes
    (T := intervalThreadOfDigits digits₁)
    (U := intervalThreadOfDigits digits₂)
    (n := n + 1)
    (intervalsOfDigits_step_precedes_of_eq_left_right hEq h₁ h₂) k

/-- Explicit finite witness that two digit-induced interval threads split by a
left-versus-right choice at a given stage. This does not assert minimality; it
packages a concrete witnessed stage of divergence on the interval side. -/
structure DyadicLeftRightWitness (digits₁ digits₂ : Nat → BinaryDigit) where
  stage : Nat
  common_interval :
    intervalsOfDigits digits₁ stage = intervalsOfDigits digits₂ stage
  left_digit : digits₁ stage = BinaryDigit.left
  right_digit : digits₂ stage = BinaryDigit.right

namespace DyadicLeftRightWitness

/-- A left-right split witness yields immediate precedence at the next stage. -/
theorem precedes_step {digits₁ digits₂ : Nat → BinaryDigit}
    (w : DyadicLeftRightWitness digits₁ digits₂) :
    DyadicIntervalPrecedes
      (intervalsOfDigits digits₁ (w.stage + 1))
      (intervalsOfDigits digits₂ (w.stage + 1)) := by
  exact intervalsOfDigits_step_precedes_of_eq_left_right
    w.common_interval w.left_digit w.right_digit

/-- A left-right split witness yields distinct next-stage intervals. -/
theorem distinct_step {digits₁ digits₂ : Nat → BinaryDigit}
    (w : DyadicLeftRightWitness digits₁ digits₂) :
    intervalsOfDigits digits₁ (w.stage + 1) ≠
      intervalsOfDigits digits₂ (w.stage + 1) := by
  exact intervalsOfDigits_step_distinct_of_eq_left_right
    w.common_interval w.left_digit w.right_digit

/-- A left-right split witness propagates precedence through every later stage. -/
theorem precedes_later {digits₁ digits₂ : Nat → BinaryDigit}
    (w : DyadicLeftRightWitness digits₁ digits₂) (k : Nat) :
    DyadicIntervalPrecedes
      (intervalsOfDigits digits₁ ((w.stage + 1) + k))
      (intervalsOfDigits digits₂ ((w.stage + 1) + k)) := by
  exact intervalsOfDigits_step_precedes_iter_of_eq_left_right
    w.common_interval w.left_digit w.right_digit k

/-- A left-right split witness propagates distinctness through every later stage. -/
theorem distinct_later {digits₁ digits₂ : Nat → BinaryDigit}
    (w : DyadicLeftRightWitness digits₁ digits₂) (k : Nat) :
    intervalsOfDigits digits₁ ((w.stage + 1) + k) ≠
      intervalsOfDigits digits₂ ((w.stage + 1) + k) := by
  exact intervalsOfDigits_step_distinct_iter_of_eq_left_right
    w.common_interval w.left_digit w.right_digit k

end DyadicLeftRightWitness

end CoherenceCalculus
