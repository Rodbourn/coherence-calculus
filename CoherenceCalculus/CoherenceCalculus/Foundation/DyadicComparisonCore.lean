import CoherenceCalculus.Foundation.DyadicIdentificationCore

/-!
# Foundation.DyadicComparisonCore

Strict dyadic separation and quotient-free comparison data.

This layer complements the ambiguous-boundary identification layer with explicit
finite strict-gap witnesses. A strict gap at some finite stage persists through
later refinements and is incompatible with boundary identification.
-/

namespace CoherenceCalculus

/-- Strict precedence of dyadic intervals on a common mesh means a genuine gap
between the right endpoint of the left interval and the left endpoint of the
right interval. -/
def DyadicIntervalStrictPrecedes {n : Nat} (I J : DyadicInterval n) : Prop :=
  I.rightIndex < J.leftIndex

/-- No dyadic interval strictly precedes itself. -/
theorem dyadicIntervalStrictPrecedes_irrefl (I : DyadicInterval n) :
    ¬ DyadicIntervalStrictPrecedes I I := by
  intro h
  exact Nat.not_lt_of_ge (dyadicInterval_left_le_right I) h

/-- Strict precedence implies weak precedence. -/
theorem dyadicIntervalStrictPrecedes_to_precedes {n : Nat}
    {I J : DyadicInterval n}
    (h : DyadicIntervalStrictPrecedes I J) :
    DyadicIntervalPrecedes I J := by
  exact Nat.le_of_lt h

/-- A genuine strict gap from `I` to `J` rules out reverse precedence. -/
theorem dyadicIntervalStrictPrecedes_not_precedes_reverse {n : Nat}
    {I J : DyadicInterval n}
    (h : DyadicIntervalStrictPrecedes I J) :
    ¬ DyadicIntervalPrecedes J I := by
  intro hrev
  have hlt : J.rightIndex < J.leftIndex := by
    exact Nat.lt_of_le_of_lt hrev (Nat.lt_trans (dyadicInterval_left_lt_right I) h)
  exact Nat.not_lt_of_ge (dyadicInterval_left_le_right J) hlt

/-- Strict precedence followed by weak precedence remains strict. -/
theorem dyadicIntervalStrictPrecedes_of_strict_precedes_of_precedes {n : Nat}
    {I J K : DyadicInterval n}
    (hIJ : DyadicIntervalStrictPrecedes I J)
    (hJK : DyadicIntervalPrecedes J K) :
    DyadicIntervalStrictPrecedes I K := by
  dsimp [DyadicIntervalStrictPrecedes, DyadicIntervalPrecedes] at *
  exact Nat.lt_of_lt_of_le hIJ
    (Nat.le_trans (dyadicInterval_left_le_right J) hJK)

/-- Weak precedence followed by strict precedence remains strict. -/
theorem dyadicIntervalStrictPrecedes_of_precedes_of_strict_precedes {n : Nat}
    {I J K : DyadicInterval n}
    (hIJ : DyadicIntervalPrecedes I J)
    (hJK : DyadicIntervalStrictPrecedes J K) :
    DyadicIntervalStrictPrecedes I K := by
  dsimp [DyadicIntervalStrictPrecedes, DyadicIntervalPrecedes] at *
  exact Nat.lt_of_le_of_lt hIJ
    (Nat.lt_trans (dyadicInterval_left_lt_right J) hJK)

/-- Strict precedence is transitive on a common mesh. -/
theorem dyadicIntervalStrictPrecedes_trans {n : Nat}
    {I J K : DyadicInterval n}
    (hIJ : DyadicIntervalStrictPrecedes I J)
    (hJK : DyadicIntervalStrictPrecedes J K) :
    DyadicIntervalStrictPrecedes I K := by
  exact dyadicIntervalStrictPrecedes_of_strict_precedes_of_precedes hIJ
    (dyadicIntervalStrictPrecedes_to_precedes hJK)

/-- Strict precedence is preserved by refining both intervals, regardless of
the chosen children. -/
theorem child_intervals_strict_precede_of_strict_precedes {n : Nat}
    {I J : DyadicInterval n}
    (h : DyadicIntervalStrictPrecedes I J)
    (b₁ b₂ : BinaryDigit) :
    DyadicIntervalStrictPrecedes
      (match b₁ with
       | BinaryDigit.left => leftChildInterval I
       | BinaryDigit.right => rightChildInterval I)
      (match b₂ with
       | BinaryDigit.left => leftChildInterval J
       | BinaryDigit.right => rightChildInterval J) := by
  let K₁ :=
    match b₁ with
    | BinaryDigit.left => leftChildInterval I
    | BinaryDigit.right => rightChildInterval I
  let K₂ :=
    match b₂ with
    | BinaryDigit.left => leftChildInterval J
    | BinaryDigit.right => rightChildInterval J
  have hK₁ :
      K₁.rightIndex ≤ 2 * I.rightIndex := by
    cases b₁ with
    | left =>
        simpa [K₁] using (leftChild_nested_scaled I).2
    | right =>
        simpa [K₁] using (rightChild_nested_scaled I).2
  have hK₂ :
      2 * J.leftIndex ≤ K₂.leftIndex := by
    cases b₂ with
    | left =>
        simpa [K₂] using (leftChild_nested_scaled J).1
    | right =>
        simpa [K₂] using (rightChild_nested_scaled J).1
  have hscaled : 2 * I.rightIndex < 2 * J.leftIndex := by
    rw [Nat.two_mul, Nat.two_mul]
    exact Nat.add_lt_add h h
  exact Nat.lt_of_le_of_lt hK₁ (Nat.lt_of_lt_of_le hscaled hK₂)

/-- If an interval strictly precedes the upper side of an adjacent pair, then
after one further refinement it strictly precedes the inward right child of the
lower side, regardless of its own next child. -/
theorem child_interval_strict_precedes_ambiguous_lower {n : Nat}
    {I : DyadicInterval n}
    (P : DyadicAdjacentPair n)
    (h : DyadicIntervalStrictPrecedes I P.right)
    (b : BinaryDigit) :
    DyadicIntervalStrictPrecedes
      (match b with
       | BinaryDigit.left => leftChildInterval I
       | BinaryDigit.right => rightChildInterval I)
      (rightChildInterval P.left) := by
  let K :=
    match b with
    | BinaryDigit.left => leftChildInterval I
    | BinaryDigit.right => rightChildInterval I
  have hK :
      K.rightIndex ≤ 2 * I.rightIndex := by
    cases b with
    | left =>
        simpa [K] using (leftChild_nested_scaled I).2
    | right =>
        simpa [K] using (rightChild_nested_scaled I).2
  have hbase : I.rightIndex ≤ P.left.leftIndex := by
    have hlt : I.rightIndex < P.left.leftIndex + 1 := by
      calc
        I.rightIndex < P.right.leftIndex := h
        _ = P.left.rightIndex := P.shared_boundary.symm
        _ = P.left.leftIndex + 1 := P.left.unit_width
    exact Nat.lt_succ_iff.mp hlt
  have hscaled : K.rightIndex ≤ 2 * P.left.leftIndex := by
    exact Nat.le_trans hK (Nat.mul_le_mul_left 2 hbase)
  change K.rightIndex < 2 * P.left.leftIndex + 1
  exact Nat.lt_succ_of_le hscaled

/-- If the lower side of an adjacent pair strictly precedes another interval,
then after one further refinement the inward left child of the upper side still
strictly precedes any chosen child of that interval. -/
theorem ambiguous_upper_strict_precedes_child_interval {n : Nat}
    (P : DyadicAdjacentPair n)
    {J : DyadicInterval n}
    (h : DyadicIntervalStrictPrecedes P.left J)
    (b : BinaryDigit) :
    DyadicIntervalStrictPrecedes
      (leftChildInterval P.right)
      (match b with
       | BinaryDigit.left => leftChildInterval J
       | BinaryDigit.right => rightChildInterval J) := by
  let K :=
    match b with
    | BinaryDigit.left => leftChildInterval J
    | BinaryDigit.right => rightChildInterval J
  have hK :
      2 * J.leftIndex ≤ K.leftIndex := by
    cases b with
    | left =>
        simpa [K] using (leftChild_nested_scaled J).1
    | right =>
        simpa [K] using (rightChild_nested_scaled J).1
  have hbase : P.right.leftIndex < J.leftIndex := by
    calc
      P.right.leftIndex = P.left.rightIndex := P.shared_boundary.symm
      _ < J.leftIndex := h
  have hle : 2 * P.right.leftIndex + 2 ≤ 2 * J.leftIndex := by
    calc
      2 * P.right.leftIndex + 2 = 2 * (P.right.leftIndex + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      _ ≤ 2 * J.leftIndex := Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hbase)
  have hscaled : 2 * P.right.leftIndex + 1 < 2 * J.leftIndex := by
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hle
  change 2 * P.right.leftIndex + 1 < K.leftIndex
  exact Nat.lt_of_lt_of_le hscaled hK

/-- If the upper side of an adjacent pair strictly precedes another interval,
then after one further refinement the inward right child of the lower side
still strictly precedes any chosen child of that interval. -/
theorem ambiguous_lower_strict_precedes_child_interval {n : Nat}
    (P : DyadicAdjacentPair n)
    {J : DyadicInterval n}
    (h : DyadicIntervalStrictPrecedes P.right J)
    (b : BinaryDigit) :
    DyadicIntervalStrictPrecedes
      (rightChildInterval P.left)
      (match b with
       | BinaryDigit.left => leftChildInterval J
       | BinaryDigit.right => rightChildInterval J) := by
  let K :=
    match b with
    | BinaryDigit.left => leftChildInterval J
    | BinaryDigit.right => rightChildInterval J
  have hK :
      2 * J.leftIndex ≤ K.leftIndex := by
    cases b with
    | left =>
        simpa [K] using (leftChild_nested_scaled J).1
    | right =>
        simpa [K] using (rightChild_nested_scaled J).1
  have hbase : P.right.leftIndex < J.leftIndex := by
    exact Nat.lt_trans (dyadicInterval_left_lt_right P.right) h
  have hscaled : 2 * P.right.leftIndex < 2 * J.leftIndex := by
    rw [Nat.two_mul, Nat.two_mul]
    exact Nat.add_lt_add hbase hbase
  change 2 * P.left.rightIndex < K.leftIndex
  rw [P.shared_boundary]
  exact Nat.lt_of_lt_of_le hscaled hK

/-- In an adjacent dyadic pair, left-child/left-child refinement creates a
strict gap. -/
theorem dyadicAdjacentPair_refine_left_left_strict (P : DyadicAdjacentPair n) :
    DyadicIntervalStrictPrecedes (leftChildInterval P.left) (leftChildInterval P.right) := by
  dsimp [DyadicIntervalStrictPrecedes]
  calc
    (leftChildInterval P.left).rightIndex = 2 * P.left.leftIndex + 1 := by
      rfl
    _ < 2 * P.left.leftIndex + 2 := Nat.lt_succ_self _
    _ = 2 * P.right.leftIndex := by
          rw [dyadicAdjacentPair_leftIndex_step P, Nat.mul_add]
    _ = (leftChildInterval P.right).leftIndex := by
          rfl

/-- In an adjacent dyadic pair, left-child/right-child refinement creates a
strict gap. -/
theorem dyadicAdjacentPair_refine_left_right_strict (P : DyadicAdjacentPair n) :
    DyadicIntervalStrictPrecedes (leftChildInterval P.left) (rightChildInterval P.right) := by
  dsimp [DyadicIntervalStrictPrecedes]
  calc
    (leftChildInterval P.left).rightIndex = 2 * P.left.leftIndex + 1 := by
      rfl
    _ < 2 * P.left.leftIndex + 2 := Nat.lt_succ_self _
    _ = 2 * P.right.leftIndex := by
          rw [dyadicAdjacentPair_leftIndex_step P, Nat.mul_add]
    _ < 2 * P.right.leftIndex + 1 := Nat.lt_succ_self _
    _ = (rightChildInterval P.right).leftIndex := by
          rfl

/-- In an adjacent dyadic pair, right-child/right-child refinement creates a
strict gap. -/
theorem dyadicAdjacentPair_refine_right_right_strict (P : DyadicAdjacentPair n) :
    DyadicIntervalStrictPrecedes (rightChildInterval P.left) (rightChildInterval P.right) := by
  dsimp [DyadicIntervalStrictPrecedes]
  calc
    (rightChildInterval P.left).rightIndex = 2 * P.left.rightIndex := by
      rfl
    _ = 2 * P.right.leftIndex := by
          rw [P.shared_boundary]
    _ < 2 * P.right.leftIndex + 1 := Nat.lt_succ_self _
    _ = (rightChildInterval P.right).leftIndex := by
          rfl

/-- Explicit strict-separation data for dyadic digit threads. -/
structure DyadicStrictSeparation (digits₁ digits₂ : Nat → BinaryDigit) : Type where
  stage : Nat
  strict : DyadicIntervalStrictPrecedes
    (intervalsOfDigits digits₁ stage)
    (intervalsOfDigits digits₂ stage)

namespace DyadicLeftRightWitness

/-- A left-right split witness gives an adjacent pair at the next stage. -/
def adjacentPairStep {digits₁ digits₂ : Nat → BinaryDigit}
    (w : DyadicLeftRightWitness digits₁ digits₂) : DyadicAdjacentPair (w.stage + 1) where
  left := intervalsOfDigits digits₁ (w.stage + 1)
  right := intervalsOfDigits digits₂ (w.stage + 1)
  shared_boundary := by
    rw [intervalsOfDigits, w.left_digit, intervalsOfDigits, w.right_digit, w.common_interval]
    exact child_intervals_share_boundary (intervalsOfDigits digits₂ w.stage)

/-- If a split witness is followed by left/left refinement, a strict gap
appears two stages after the split. -/
def strict_two_steps_of_next_left_left
    {digits₁ digits₂ : Nat → BinaryDigit}
    (w : DyadicLeftRightWitness digits₁ digits₂)
    (h₁ : digits₁ (w.stage + 1) = BinaryDigit.left)
    (h₂ : digits₂ (w.stage + 1) = BinaryDigit.left) :
    DyadicStrictSeparation digits₁ digits₂ := by
  refine ⟨w.stage + 2, ?_⟩
  simpa [intervalsOfDigits, h₁, h₂] using
    dyadicAdjacentPair_refine_left_left_strict (adjacentPairStep w)

/-- If a split witness is followed by left/right refinement, a strict gap
appears two stages after the split. -/
def strict_two_steps_of_next_left_right
    {digits₁ digits₂ : Nat → BinaryDigit}
    (w : DyadicLeftRightWitness digits₁ digits₂)
    (h₁ : digits₁ (w.stage + 1) = BinaryDigit.left)
    (h₂ : digits₂ (w.stage + 1) = BinaryDigit.right) :
    DyadicStrictSeparation digits₁ digits₂ := by
  refine ⟨w.stage + 2, ?_⟩
  simpa [intervalsOfDigits, h₁, h₂] using
    dyadicAdjacentPair_refine_left_right_strict (adjacentPairStep w)

/-- If a split witness is followed by right/right refinement, a strict gap
appears two stages after the split. -/
def strict_two_steps_of_next_right_right
    {digits₁ digits₂ : Nat → BinaryDigit}
    (w : DyadicLeftRightWitness digits₁ digits₂)
    (h₁ : digits₁ (w.stage + 1) = BinaryDigit.right)
    (h₂ : digits₂ (w.stage + 1) = BinaryDigit.right) :
    DyadicStrictSeparation digits₁ digits₂ := by
  refine ⟨w.stage + 2, ?_⟩
  simpa [intervalsOfDigits, h₁, h₂] using
    dyadicAdjacentPair_refine_right_right_strict (adjacentPairStep w)

end DyadicLeftRightWitness

namespace DyadicAmbiguousWitness

/-- At every later stage, an ambiguous witness presents an explicit adjacent
pair with the same shared boundary. -/
def adjacentPair_later
    {digits₁ digits₂ : Nat → BinaryDigit}
    (w : DyadicAmbiguousWitness digits₁ digits₂) (k : Nat) :
    DyadicAdjacentPair ((w.split.stage + 1) + k) where
  left := intervalsOfDigits digits₁ ((w.split.stage + 1) + k)
  right := intervalsOfDigits digits₂ ((w.split.stage + 1) + k)
  shared_boundary := w.shared_boundary_later k

end DyadicAmbiguousWitness

namespace DyadicStrictSeparation

/-- A strict gap gives weak precedence at the same stage. -/
theorem precedes {digits₁ digits₂ : Nat → BinaryDigit}
    (s : DyadicStrictSeparation digits₁ digits₂) :
    DyadicIntervalPrecedes
      (intervalsOfDigits digits₁ s.stage)
      (intervalsOfDigits digits₂ s.stage) := by
  exact dyadicIntervalStrictPrecedes_to_precedes s.strict

/-- A strict gap persists through every later refinement stage. -/
theorem later {digits₁ digits₂ : Nat → BinaryDigit}
    (s : DyadicStrictSeparation digits₁ digits₂) (k : Nat) :
    DyadicIntervalStrictPrecedes
      (intervalsOfDigits digits₁ (s.stage + k))
      (intervalsOfDigits digits₂ (s.stage + k)) := by
  induction k with
  | zero =>
      simpa using s.strict
  | succ k ih =>
      change DyadicIntervalStrictPrecedes
        (intervalsOfDigits digits₁ ((s.stage + k) + 1))
        (intervalsOfDigits digits₂ ((s.stage + k) + 1))
      cases h₁ : digits₁ (s.stage + k) <;> cases h₂ : digits₂ (s.stage + k)
      · rw [intervalsOfDigits, h₁, intervalsOfDigits, h₂]
        exact child_intervals_strict_precede_of_strict_precedes ih BinaryDigit.left BinaryDigit.left
      · rw [intervalsOfDigits, h₁, intervalsOfDigits, h₂]
        exact child_intervals_strict_precede_of_strict_precedes ih BinaryDigit.left BinaryDigit.right
      · rw [intervalsOfDigits, h₁, intervalsOfDigits, h₂]
        exact child_intervals_strict_precede_of_strict_precedes ih BinaryDigit.right BinaryDigit.left
      · rw [intervalsOfDigits, h₁, intervalsOfDigits, h₂]
        exact child_intervals_strict_precede_of_strict_precedes ih BinaryDigit.right BinaryDigit.right

/-- A strict gap persists as weak precedence at every later stage. -/
theorem precedes_later {digits₁ digits₂ : Nat → BinaryDigit}
    (s : DyadicStrictSeparation digits₁ digits₂) (k : Nat) :
    DyadicIntervalPrecedes
      (intervalsOfDigits digits₁ (s.stage + k))
      (intervalsOfDigits digits₂ (s.stage + k)) := by
  exact dyadicIntervalStrictPrecedes_to_precedes (s.later k)

/-- Exact interval-thread agreement transports strict separation on the left. -/
def of_exact_left
    {digits₁ digits₂ digits₃ : Nat → BinaryDigit}
    (hExact : ∀ n, intervalsOfDigits digits₁ n = intervalsOfDigits digits₂ n)
    (s : DyadicStrictSeparation digits₂ digits₃) :
    DyadicStrictSeparation digits₁ digits₃ where
  stage := s.stage
  strict := by
    rw [hExact s.stage]
    exact s.strict

/-- Exact interval-thread agreement transports strict separation on the right. -/
def of_exact_right
    {digits₁ digits₂ digits₃ : Nat → BinaryDigit}
    (s : DyadicStrictSeparation digits₁ digits₂)
    (hExact : ∀ n, intervalsOfDigits digits₂ n = intervalsOfDigits digits₃ n) :
    DyadicStrictSeparation digits₁ digits₃ where
  stage := s.stage
  strict := by
    rw [← hExact s.stage]
    exact s.strict

/-- Strict separation is transitive. -/
def trans
    {digits₁ digits₂ digits₃ : Nat → BinaryDigit}
    (s₁ : DyadicStrictSeparation digits₁ digits₂)
    (s₂ : DyadicStrictSeparation digits₂ digits₃) :
    DyadicStrictSeparation digits₁ digits₃ := by
  let N := s₁.stage + s₂.stage
  refine ⟨N, ?_⟩
  have h₁ :
      DyadicIntervalStrictPrecedes
        (intervalsOfDigits digits₁ N)
        (intervalsOfDigits digits₂ N) := by
    dsimp [N]
    exact s₁.later s₂.stage
  have h₂raw := s₂.later s₁.stage
  have h₂ :
      DyadicIntervalStrictPrecedes
        (intervalsOfDigits digits₂ N)
        (intervalsOfDigits digits₃ N) := by
    dsimp [N]
    rw [Nat.add_comm s₂.stage s₁.stage] at h₂raw
    exact h₂raw
  exact dyadicIntervalStrictPrecedes_trans h₁ h₂

/-- Strict separation transports across an ambiguous identification on the
right when the identified thread is the lower representative. -/
def of_ambiguous_right_lower_upper
    {digits₁ digits₂ digits₃ : Nat → BinaryDigit}
    (s : DyadicStrictSeparation digits₁ digits₂)
    (w : DyadicAmbiguousWitness digits₂ digits₃) :
    DyadicStrictSeparation digits₁ digits₃ := by
  let N := s.stage + (w.split.stage + 1)
  refine ⟨N, ?_⟩
  have hs :
      DyadicIntervalStrictPrecedes
        (intervalsOfDigits digits₁ N)
        (intervalsOfDigits digits₂ N) := by
    dsimp [N]
    exact s.later (w.split.stage + 1)
  have hwRaw := w.precedes_later s.stage
  have hw :
      DyadicIntervalPrecedes
        (intervalsOfDigits digits₂ N)
        (intervalsOfDigits digits₃ N) := by
    dsimp [N]
    rw [Nat.add_comm (w.split.stage + 1) s.stage] at hwRaw
    exact hwRaw
  exact dyadicIntervalStrictPrecedes_of_strict_precedes_of_precedes hs hw

/-- Strict separation transports across an ambiguous identification on the
right when the identified thread is the upper representative, by stepping once
more into the inward ambiguous refinement. -/
def of_ambiguous_right_upper_lower
    {digits₁ digits₂ digits₃ : Nat → BinaryDigit}
    (s : DyadicStrictSeparation digits₁ digits₂)
    (w : DyadicAmbiguousWitness digits₃ digits₂) :
    DyadicStrictSeparation digits₁ digits₃ := by
  let N := (w.split.stage + 1) + s.stage
  refine ⟨N + 1, ?_⟩
  have hsRaw := s.later (w.split.stage + 1)
  have hs :
      DyadicIntervalStrictPrecedes
        (intervalsOfDigits digits₁ N)
        (intervalsOfDigits digits₂ N) := by
    dsimp [N]
    rw [Nat.add_comm s.stage (w.split.stage + 1)] at hsRaw
    exact hsRaw
  let P := w.adjacentPair_later s.stage
  have hLower : digits₃ N = BinaryDigit.right := by
    dsimp [N]
    exact w.inward_left s.stage
  cases hDigit : digits₁ N with
  | left =>
      dsimp [N]
      rw [intervalsOfDigits, hDigit, intervalsOfDigits, hLower]
      exact child_interval_strict_precedes_ambiguous_lower P hs BinaryDigit.left
  | right =>
      dsimp [N]
      rw [intervalsOfDigits, hDigit, intervalsOfDigits, hLower]
      exact child_interval_strict_precedes_ambiguous_lower P hs BinaryDigit.right

/-- Strict separation transports across an ambiguous identification on the
left when the identified thread is the lower representative. -/
def of_ambiguous_left_lower_upper
    {digits₁ digits₂ digits₃ : Nat → BinaryDigit}
    (w : DyadicAmbiguousWitness digits₁ digits₂)
    (s : DyadicStrictSeparation digits₁ digits₃) :
    DyadicStrictSeparation digits₂ digits₃ := by
  let N := (w.split.stage + 1) + s.stage
  refine ⟨N + 1, ?_⟩
  have hsRaw := s.later (w.split.stage + 1)
  have hs :
      DyadicIntervalStrictPrecedes
        (intervalsOfDigits digits₁ N)
        (intervalsOfDigits digits₃ N) := by
    dsimp [N]
    rw [Nat.add_comm s.stage (w.split.stage + 1)] at hsRaw
    exact hsRaw
  let P := w.adjacentPair_later s.stage
  have hUpper : digits₂ N = BinaryDigit.left := by
    dsimp [N]
    exact w.inward_right s.stage
  cases hDigit : digits₃ N with
  | left =>
      dsimp [N]
      rw [intervalsOfDigits, hUpper, intervalsOfDigits, hDigit]
      exact ambiguous_upper_strict_precedes_child_interval P hs BinaryDigit.left
  | right =>
      dsimp [N]
      rw [intervalsOfDigits, hUpper, intervalsOfDigits, hDigit]
      exact ambiguous_upper_strict_precedes_child_interval P hs BinaryDigit.right

/-- Strict separation transports across an ambiguous identification on the
left when the identified thread is the upper representative, by stepping once
more into the inward ambiguous refinement. -/
def of_ambiguous_left_upper_lower
    {digits₁ digits₂ digits₃ : Nat → BinaryDigit}
    (w : DyadicAmbiguousWitness digits₁ digits₂)
    (s : DyadicStrictSeparation digits₂ digits₃) :
    DyadicStrictSeparation digits₁ digits₃ := by
  let N := (w.split.stage + 1) + s.stage
  refine ⟨N + 1, ?_⟩
  have hsRaw := s.later (w.split.stage + 1)
  have hs :
      DyadicIntervalStrictPrecedes
        (intervalsOfDigits digits₂ N)
        (intervalsOfDigits digits₃ N) := by
    dsimp [N]
    rw [Nat.add_comm s.stage (w.split.stage + 1)] at hsRaw
    exact hsRaw
  let P := w.adjacentPair_later s.stage
  have hLower : digits₁ N = BinaryDigit.right := by
    dsimp [N]
    exact w.inward_left s.stage
  cases hDigit : digits₃ N with
  | left =>
      dsimp [N]
      rw [intervalsOfDigits, hLower, intervalsOfDigits, hDigit]
      exact ambiguous_lower_strict_precedes_child_interval P hs BinaryDigit.left
  | right =>
      dsimp [N]
      rw [intervalsOfDigits, hLower, intervalsOfDigits, hDigit]
      exact ambiguous_lower_strict_precedes_child_interval P hs BinaryDigit.right

/-- Strict separation transports across quotient-free boundary identification on
the right. -/
def of_identified_right
    {digits₁ digits₂ digits₃ : Nat → BinaryDigit}
    (s : DyadicStrictSeparation digits₁ digits₂) :
    DyadicBoundaryIdentification digits₂ digits₃ →
      DyadicStrictSeparation digits₁ digits₃
  | .exact hExact => of_exact_right s hExact
  | .ambiguousLeftRight w => of_ambiguous_right_lower_upper s w
  | .ambiguousRightLeft w => of_ambiguous_right_upper_lower s w

/-- Strict separation transports across quotient-free boundary identification on
the left. -/
def of_identified_left
    {digits₁ digits₂ digits₃ : Nat → BinaryDigit}
    (h : DyadicBoundaryIdentification digits₁ digits₂)
    (s : DyadicStrictSeparation digits₂ digits₃) :
    DyadicStrictSeparation digits₁ digits₃ := by
  cases h with
  | exact hExact =>
      exact of_exact_left hExact s
  | ambiguousLeftRight w =>
      exact of_ambiguous_left_upper_lower w s
  | ambiguousRightLeft w =>
      exact of_ambiguous_left_lower_upper w s

/-- A strict gap is incompatible with exact interval-thread agreement. -/
theorem not_exact
    {digits₁ digits₂ : Nat → BinaryDigit}
    (s : DyadicStrictSeparation digits₁ digits₂)
    (hExact : ∀ n, intervalsOfDigits digits₁ n = intervalsOfDigits digits₂ n) :
    False := by
  have hStrict := s.strict
  rw [hExact s.stage] at hStrict
  exact dyadicIntervalStrictPrecedes_irrefl _ hStrict

/-- A strict gap is incompatible with an ambiguous-tail identification in the
same left-to-right orientation. -/
theorem not_ambiguousLeftRight
    {digits₁ digits₂ : Nat → BinaryDigit}
    (s : DyadicStrictSeparation digits₁ digits₂)
    (w : DyadicAmbiguousWitness digits₁ digits₂) :
    False := by
  have hStrict := s.later (w.split.stage + 1)
  have hShared :
      (intervalsOfDigits digits₁ (s.stage + (w.split.stage + 1))).rightIndex =
        (intervalsOfDigits digits₂ (s.stage + (w.split.stage + 1))).leftIndex := by
    have hSharedRaw := w.shared_boundary_later s.stage
    rw [Nat.add_comm (w.split.stage + 1) s.stage] at hSharedRaw
    exact hSharedRaw
  dsimp [DyadicIntervalStrictPrecedes] at hStrict
  rw [hShared] at hStrict
  exact Nat.lt_irrefl _ hStrict

/-- A strict gap is incompatible with an ambiguous-tail identification in the
reverse orientation. -/
theorem not_ambiguousRightLeft
    {digits₁ digits₂ : Nat → BinaryDigit}
    (s : DyadicStrictSeparation digits₁ digits₂)
    (w : DyadicAmbiguousWitness digits₂ digits₁) :
    False := by
  have hStrict := s.later (w.split.stage + 1)
  have hReverse :
      DyadicIntervalPrecedes
        (intervalsOfDigits digits₂ (s.stage + (w.split.stage + 1)))
        (intervalsOfDigits digits₁ (s.stage + (w.split.stage + 1))) := by
    have hReverseRaw := w.precedes_later s.stage
    rw [Nat.add_comm (w.split.stage + 1) s.stage] at hReverseRaw
    exact hReverseRaw
  exact (dyadicIntervalStrictPrecedes_not_precedes_reverse hStrict) hReverse

/-- A strict gap is incompatible with quotient-free boundary identification. -/
theorem not_identified
    {digits₁ digits₂ : Nat → BinaryDigit}
    (s : DyadicStrictSeparation digits₁ digits₂) :
    DyadicBoundaryIdentification digits₁ digits₂ → False
  | .exact hExact => s.not_exact hExact
  | .ambiguousLeftRight w => s.not_ambiguousLeftRight w
  | .ambiguousRightLeft w => s.not_ambiguousRightLeft w

/-- Two opposite strict separations are incompatible. -/
theorem false_of_reverse
    {digits₁ digits₂ : Nat → BinaryDigit}
    (s₁₂ : DyadicStrictSeparation digits₁ digits₂)
    (s₂₁ : DyadicStrictSeparation digits₂ digits₁) :
    False := by
  let N := s₁₂.stage + s₂₁.stage
  have hLeft :
      DyadicIntervalStrictPrecedes
        (intervalsOfDigits digits₁ N)
        (intervalsOfDigits digits₂ N) := by
    dsimp [N]
    exact s₁₂.later s₂₁.stage
  have hRightRaw := s₂₁.precedes_later s₁₂.stage
  have hRight :
      DyadicIntervalPrecedes
        (intervalsOfDigits digits₂ N)
        (intervalsOfDigits digits₁ N) := by
    dsimp [N]
    rw [Nat.add_comm s₂₁.stage s₁₂.stage] at hRightRaw
    exact hRightRaw
  exact (dyadicIntervalStrictPrecedes_not_precedes_reverse hLeft) hRight

end DyadicStrictSeparation

/-- Quotient-free comparison data for dyadic digit threads. -/
inductive DyadicBoundaryComparison
    (digits₁ digits₂ : Nat → BinaryDigit) : Type where
  | identified :
      DyadicBoundaryIdentification digits₁ digits₂ →
      DyadicBoundaryComparison digits₁ digits₂
  | strictLeft :
      DyadicStrictSeparation digits₁ digits₂ →
      DyadicBoundaryComparison digits₁ digits₂
  | strictRight :
      DyadicStrictSeparation digits₂ digits₁ →
      DyadicBoundaryComparison digits₁ digits₂

namespace DyadicBoundaryComparison

/-- Quotient-free boundary comparison is symmetric by construction. -/
def symm {digits₁ digits₂ : Nat → BinaryDigit} :
    DyadicBoundaryComparison digits₁ digits₂ →
      DyadicBoundaryComparison digits₂ digits₁
  | .identified h => .identified h.symm
  | .strictLeft s => .strictRight s
  | .strictRight s => .strictLeft s

/-- Comparison data transports across quotient-free boundary identification on
the right. -/
def trans_identified_right
    {digits₁ digits₂ digits₃ : Nat → BinaryDigit} :
    DyadicBoundaryComparison digits₁ digits₂ →
      DyadicBoundaryIdentification digits₂ digits₃ →
      DyadicBoundaryComparison digits₁ digits₃
  | .identified h₁₂, h₂₃ =>
      .identified (h₁₂.trans h₂₃)
  | .strictLeft s, h₂₃ =>
      .strictLeft (s.of_identified_right h₂₃)
  | .strictRight s, h₂₃ =>
      .strictRight (DyadicStrictSeparation.of_identified_left h₂₃.symm s)

/-- Comparison data transports across quotient-free boundary identification on
the left. -/
def trans_identified_left
    {digits₁ digits₂ digits₃ : Nat → BinaryDigit}
    (h₁₂ : DyadicBoundaryIdentification digits₁ digits₂)
    (c₂₃ : DyadicBoundaryComparison digits₂ digits₃) :
    DyadicBoundaryComparison digits₁ digits₃ :=
  symm (trans_identified_right (symm c₂₃) h₁₂.symm)

/-- Strict-left comparison is transitive. -/
def strictLeft_trans
    {digits₁ digits₂ digits₃ : Nat → BinaryDigit}
    (s₁₂ : DyadicStrictSeparation digits₁ digits₂)
    (s₂₃ : DyadicStrictSeparation digits₂ digits₃) :
    DyadicBoundaryComparison digits₁ digits₃ :=
  .strictLeft (s₁₂.trans s₂₃)

/-- Strict-right comparison is transitive. -/
def strictRight_trans
    {digits₁ digits₂ digits₃ : Nat → BinaryDigit}
    (s₂₁ : DyadicStrictSeparation digits₂ digits₁)
    (s₃₂ : DyadicStrictSeparation digits₃ digits₂) :
    DyadicBoundaryComparison digits₁ digits₃ :=
  .strictRight (s₃₂.trans s₂₁)

/-- Identified and strict-left comparison are incompatible. -/
theorem false_of_identified_and_strictLeft
    {digits₁ digits₂ : Nat → BinaryDigit}
    (h : DyadicBoundaryIdentification digits₁ digits₂)
    (s : DyadicStrictSeparation digits₁ digits₂) :
    False := by
  exact s.not_identified h

/-- Identified and strict-right comparison are incompatible. -/
theorem false_of_identified_and_strictRight
    {digits₁ digits₂ : Nat → BinaryDigit}
    (h : DyadicBoundaryIdentification digits₁ digits₂)
    (s : DyadicStrictSeparation digits₂ digits₁) :
    False := by
  exact s.not_identified h.symm

/-- Strict-left and strict-right comparison are incompatible. -/
theorem false_of_strictLeft_and_strictRight
    {digits₁ digits₂ : Nat → BinaryDigit}
    (sLeft : DyadicStrictSeparation digits₁ digits₂)
    (sRight : DyadicStrictSeparation digits₂ digits₁) :
    False := by
  exact DyadicStrictSeparation.false_of_reverse sLeft sRight

end DyadicBoundaryComparison

end CoherenceCalculus
