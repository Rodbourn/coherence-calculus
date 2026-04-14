import CoherenceCalculus.Foundation.DyadicOrderCore

/-!
# Foundation.DyadicBoundaryPairCore

Adjacent dyadic interval pairs with a persistent interior boundary.

This module isolates the interval-level pattern behind the ambiguous-tail
phenomenon: two adjacent intervals share an interior boundary, and the
right-child/left-child refinement keeps that boundary while tightening the outer
envelope on the finer mesh.
-/

namespace CoherenceCalculus

/-- A pair of adjacent dyadic intervals on a common mesh. -/
structure DyadicAdjacentPair (n : Nat) where
  left : DyadicInterval n
  right : DyadicInterval n
  shared_boundary : left.rightIndex = right.leftIndex

namespace DyadicAdjacentPair

/-- Outer span of an adjacent pair, measured in mesh steps. -/
def outerSpan {n : Nat} (P : DyadicAdjacentPair n) : Nat :=
  P.right.rightIndex - P.left.leftIndex

end DyadicAdjacentPair

/-- Every adjacent dyadic pair is ordered from left to right. -/
theorem dyadicAdjacentPair_precedes (P : DyadicAdjacentPair n) :
    DyadicIntervalPrecedes P.left P.right := by
  dsimp [DyadicIntervalPrecedes]
  rw [P.shared_boundary]
  exact Nat.le_refl _

/-- The ambiguous-tail refinement of an adjacent pair: right child on the left,
left child on the right. -/
def ambiguousRefinementPair (P : DyadicAdjacentPair n) : DyadicAdjacentPair (n + 1) where
  left := rightChildInterval P.left
  right := leftChildInterval P.right
  shared_boundary := by
    dsimp [rightChildInterval, leftChildInterval]
    rw [P.shared_boundary]

/-- Ambiguous-tail refinement preserves the shared interior boundary. -/
theorem ambiguousRefinementPair_shared_boundary (P : DyadicAdjacentPair n) :
    (ambiguousRefinementPair P).left.rightIndex =
      (ambiguousRefinementPair P).right.leftIndex := by
  exact (ambiguousRefinementPair P).shared_boundary

/-- Ambiguous-tail refinement preserves left-to-right order. -/
theorem ambiguousRefinementPair_precedes (P : DyadicAdjacentPair n) :
    DyadicIntervalPrecedes (ambiguousRefinementPair P).left (ambiguousRefinementPair P).right := by
  exact dyadicAdjacentPair_precedes (ambiguousRefinementPair P)

/-- In an adjacent dyadic pair, the right interval starts exactly one mesh step
after the left interval starts. -/
theorem dyadicAdjacentPair_leftIndex_step (P : DyadicAdjacentPair n) :
    P.right.leftIndex = P.left.leftIndex + 1 := by
  calc
    P.right.leftIndex = P.left.rightIndex := P.shared_boundary.symm
    _ = P.left.leftIndex + 1 := P.left.unit_width

/-- In an adjacent dyadic pair, the right-child/left-child refinement preserves
the shared boundary. -/
theorem dyadicAdjacentPair_refine_right_left_shared_boundary (P : DyadicAdjacentPair n) :
    (rightChildInterval P.left).rightIndex = (leftChildInterval P.right).leftIndex := by
  calc
    (rightChildInterval P.left).rightIndex = 2 * P.left.rightIndex := by
      rfl
    _ = 2 * P.right.leftIndex := by
      rw [P.shared_boundary]
    _ = (leftChildInterval P.right).leftIndex := by
      rfl

/-- In an adjacent dyadic pair, left-child/left-child refinement cannot keep a
shared boundary. -/
theorem dyadicAdjacentPair_refine_left_left_not_shared_boundary (P : DyadicAdjacentPair n) :
    (leftChildInterval P.left).rightIndex ≠ (leftChildInterval P.right).leftIndex := by
  intro h
  have hstep : P.right.leftIndex = P.left.leftIndex + 1 := dyadicAdjacentPair_leftIndex_step P
  have hlt : (leftChildInterval P.left).rightIndex < (leftChildInterval P.right).leftIndex := by
    calc
      (leftChildInterval P.left).rightIndex = 2 * P.left.leftIndex + 1 := by
        rfl
      _ < 2 * P.left.leftIndex + 2 := Nat.lt_succ_self _
      _ = 2 * P.right.leftIndex := by
        rw [hstep, Nat.mul_add]
      _ = (leftChildInterval P.right).leftIndex := by
        rfl
  exact (Nat.ne_of_lt hlt) h

/-- In an adjacent dyadic pair, left-child/right-child refinement cannot keep a
shared boundary. -/
theorem dyadicAdjacentPair_refine_left_right_not_shared_boundary (P : DyadicAdjacentPair n) :
    (leftChildInterval P.left).rightIndex ≠ (rightChildInterval P.right).leftIndex := by
  intro h
  have hstep : P.right.leftIndex = P.left.leftIndex + 1 := dyadicAdjacentPair_leftIndex_step P
  have hlt : (leftChildInterval P.left).rightIndex < (rightChildInterval P.right).leftIndex := by
    calc
      (leftChildInterval P.left).rightIndex = 2 * P.left.leftIndex + 1 := by
        rfl
      _ < 2 * P.left.leftIndex + 2 := Nat.lt_succ_self _
      _ = 2 * P.right.leftIndex := by
        rw [hstep, Nat.mul_add]
      _ < 2 * P.right.leftIndex + 1 := Nat.lt_succ_self _
      _ = (rightChildInterval P.right).leftIndex := by
        rfl
  exact (Nat.ne_of_lt hlt) h

/-- In an adjacent dyadic pair, right-child/right-child refinement cannot keep
a shared boundary. -/
theorem dyadicAdjacentPair_refine_right_right_not_shared_boundary (P : DyadicAdjacentPair n) :
    (rightChildInterval P.left).rightIndex ≠ (rightChildInterval P.right).leftIndex := by
  intro h
  have hlt : (rightChildInterval P.left).rightIndex < (rightChildInterval P.right).leftIndex := by
    calc
      (rightChildInterval P.left).rightIndex = 2 * P.left.rightIndex := by
        rfl
      _ = 2 * P.right.leftIndex := by
        rw [P.shared_boundary]
      _ < 2 * P.right.leftIndex + 1 := Nat.lt_succ_self _
      _ = (rightChildInterval P.right).leftIndex := by
        rfl
  exact (Nat.ne_of_lt hlt) h

/-- In an adjacent dyadic pair, a shared boundary at the next stage forces the
right-child/left-child refinement pattern. -/
theorem dyadicAdjacentPair_shared_boundary_next_forces_right_left
    (P : DyadicAdjacentPair n) (bLeft bRight : BinaryDigit)
    (h :
      (match bLeft with
       | BinaryDigit.left => leftChildInterval P.left
       | BinaryDigit.right => rightChildInterval P.left).rightIndex =
      (match bRight with
       | BinaryDigit.left => leftChildInterval P.right
       | BinaryDigit.right => rightChildInterval P.right).leftIndex) :
    bLeft = BinaryDigit.right ∧ bRight = BinaryDigit.left := by
  cases bLeft with
  | left =>
      cases bRight with
      | left =>
          exact False.elim (dyadicAdjacentPair_refine_left_left_not_shared_boundary P h)
      | right =>
          exact False.elim (dyadicAdjacentPair_refine_left_right_not_shared_boundary P h)
  | right =>
      cases bRight with
      | left =>
          exact ⟨rfl, rfl⟩
      | right =>
          exact False.elim (dyadicAdjacentPair_refine_right_right_not_shared_boundary P h)

/-- Canonical adjacent pair at the midpoint of the unit interval. -/
def midpointAdjacentPair : DyadicAdjacentPair 1 where
  left := leftChildInterval rootInterval
  right := rightChildInterval rootInterval
  shared_boundary := child_intervals_share_boundary rootInterval

/-- Canonical tower of ambiguous-tail adjacent pairs converging to the dyadic
midpoint boundary. -/
def midpointAdjacentPairs : (n : Nat) → DyadicAdjacentPair (n + 1)
  | 0 => midpointAdjacentPair
  | n + 1 => ambiguousRefinementPair (midpointAdjacentPairs n)

/-- Left intervals in the canonical midpoint-adjacent tower. -/
def midpointLeftIntervals : (n : Nat) → DyadicInterval (n + 1)
  | 0 => leftChildInterval rootInterval
  | n + 1 => rightChildInterval (midpointLeftIntervals n)

/-- Right intervals in the canonical midpoint-adjacent tower. -/
def midpointRightIntervals : (n : Nat) → DyadicInterval (n + 1)
  | 0 => rightChildInterval rootInterval
  | n + 1 => leftChildInterval (midpointRightIntervals n)

/-- The digit sequence `0.0111...` generating the left side of the canonical
midpoint ambiguity tower. -/
def midpointLowerDigits : Nat → BinaryDigit
  | 0 => BinaryDigit.left
  | _ + 1 => BinaryDigit.right

/-- The digit sequence `0.1000...` generating the right side of the canonical
midpoint ambiguity tower. -/
def midpointUpperDigits : Nat → BinaryDigit
  | 0 => BinaryDigit.right
  | _ + 1 => BinaryDigit.left

/-- Explicit ambiguous-tail witness for digit-induced interval threads: a
left-versus-right split at some finite stage, followed by persistent inward
choices on both sides. -/
structure DyadicAmbiguousWitness (digits₁ digits₂ : Nat → BinaryDigit) where
  split : DyadicLeftRightWitness digits₁ digits₂
  inward_left : ∀ m, digits₁ (split.stage + 1 + m) = BinaryDigit.right
  inward_right : ∀ m, digits₂ (split.stage + 1 + m) = BinaryDigit.left

namespace DyadicAmbiguousWitness

/-- An ambiguous-tail witness gives a shared boundary immediately after the
split. -/
theorem shared_boundary_step {digits₁ digits₂ : Nat → BinaryDigit}
    (w : DyadicAmbiguousWitness digits₁ digits₂) :
    (intervalsOfDigits digits₁ (w.split.stage + 1)).rightIndex =
      (intervalsOfDigits digits₂ (w.split.stage + 1)).leftIndex := by
  rw [intervalsOfDigits, w.split.left_digit, intervalsOfDigits, w.split.right_digit,
    w.split.common_interval]
  exact child_intervals_share_boundary (intervalsOfDigits digits₂ w.split.stage)

/-- An ambiguous-tail witness preserves the shared boundary at every later
finite stage. -/
theorem shared_boundary_later {digits₁ digits₂ : Nat → BinaryDigit}
    (w : DyadicAmbiguousWitness digits₁ digits₂) (k : Nat) :
    (intervalsOfDigits digits₁ (w.split.stage + 1 + k)).rightIndex =
      (intervalsOfDigits digits₂ (w.split.stage + 1 + k)).leftIndex := by
  induction k with
  | zero =>
      rw [Nat.add_zero, Nat.add_zero]
      exact w.shared_boundary_step
  | succ k ih =>
      change (intervalsOfDigits digits₁ ((w.split.stage + 1 + k) + 1)).rightIndex =
          (intervalsOfDigits digits₂ ((w.split.stage + 1 + k) + 1)).leftIndex
      rw [intervalsOfDigits, w.inward_left k, intervalsOfDigits, w.inward_right k]
      calc
        (rightChildInterval (intervalsOfDigits digits₁ (w.split.stage + 1 + k))).rightIndex
            = 2 * (intervalsOfDigits digits₁ (w.split.stage + 1 + k)).rightIndex := by
                rfl
        _ = 2 * (intervalsOfDigits digits₂ (w.split.stage + 1 + k)).leftIndex := by
              rw [ih]
        _ = (leftChildInterval (intervalsOfDigits digits₂ (w.split.stage + 1 + k))).leftIndex := by
              rfl

/-- An ambiguous-tail witness still gives later precedence. -/
theorem precedes_later {digits₁ digits₂ : Nat → BinaryDigit}
    (w : DyadicAmbiguousWitness digits₁ digits₂) (k : Nat) :
    DyadicIntervalPrecedes
      (intervalsOfDigits digits₁ (w.split.stage + 1 + k))
      (intervalsOfDigits digits₂ (w.split.stage + 1 + k)) := by
  exact w.split.precedes_later k

/-- An ambiguous-tail witness still gives later distinctness of the interval
descriptions. -/
theorem distinct_later {digits₁ digits₂ : Nat → BinaryDigit}
    (w : DyadicAmbiguousWitness digits₁ digits₂) (k : Nat) :
    intervalsOfDigits digits₁ (w.split.stage + 1 + k) ≠
      intervalsOfDigits digits₂ (w.split.stage + 1 + k) := by
  exact w.split.distinct_later k

/-- If two digit-induced interval threads share a boundary at stage `s` and
again at stage `s + 1`, then the stage-`s` digits are forced to be
right-versus-left. -/
theorem digits_forced_of_shared_boundary_next
    {digits₁ digits₂ : Nat → BinaryDigit} {s : Nat}
    (hShared :
      (intervalsOfDigits digits₁ s).rightIndex =
        (intervalsOfDigits digits₂ s).leftIndex)
    (hNext :
      (intervalsOfDigits digits₁ (s + 1)).rightIndex =
        (intervalsOfDigits digits₂ (s + 1)).leftIndex) :
    digits₁ s = BinaryDigit.right ∧ digits₂ s = BinaryDigit.left := by
  let P : DyadicAdjacentPair s := {
    left := intervalsOfDigits digits₁ s
    right := intervalsOfDigits digits₂ s
    shared_boundary := hShared
  }
  cases h₁ : digits₁ s with
  | left =>
      cases h₂ : digits₂ s with
      | left =>
          rw [intervalsOfDigits, h₁, intervalsOfDigits, h₂] at hNext
          exact False.elim (dyadicAdjacentPair_refine_left_left_not_shared_boundary P hNext)
      | right =>
          rw [intervalsOfDigits, h₁, intervalsOfDigits, h₂] at hNext
          exact False.elim (dyadicAdjacentPair_refine_left_right_not_shared_boundary P hNext)
  | right =>
      cases h₂ : digits₂ s with
      | left =>
          exact ⟨rfl, rfl⟩
      | right =>
          rw [intervalsOfDigits, h₁, intervalsOfDigits, h₂] at hNext
          exact False.elim (dyadicAdjacentPair_refine_right_right_not_shared_boundary P hNext)

/-- Persistent shared boundary from a base stage forces the ambiguous inward
tail pattern from that stage onward. -/
theorem digits_forced_of_persistent_shared_boundary
    {digits₁ digits₂ : Nat → BinaryDigit} {base : Nat}
    (hShared :
      ∀ k,
        (intervalsOfDigits digits₁ (base + k)).rightIndex =
          (intervalsOfDigits digits₂ (base + k)).leftIndex) :
    ∀ m, digits₁ (base + m) = BinaryDigit.right ∧ digits₂ (base + m) = BinaryDigit.left := by
  intro m
  have hNow := hShared m
  have hNext := hShared (m + 1)
  have hNext' :
      (intervalsOfDigits digits₁ ((base + m) + 1)).rightIndex =
        (intervalsOfDigits digits₂ ((base + m) + 1)).leftIndex := by
    rw [Nat.add_assoc]
    exact hNext
  exact digits_forced_of_shared_boundary_next hNow hNext'

/-- A left-right split witness together with persistent later shared boundary
forces an ambiguous-tail witness. -/
def of_persistent_shared_boundary
    {digits₁ digits₂ : Nat → BinaryDigit}
    (w : DyadicLeftRightWitness digits₁ digits₂)
    (hShared :
      ∀ k,
        (intervalsOfDigits digits₁ ((w.stage + 1) + k)).rightIndex =
          (intervalsOfDigits digits₂ ((w.stage + 1) + k)).leftIndex) :
    DyadicAmbiguousWitness digits₁ digits₂ := by
  have hDigits :
      ∀ m,
        digits₁ ((w.stage + 1) + m) = BinaryDigit.right ∧
          digits₂ ((w.stage + 1) + m) = BinaryDigit.left :=
    digits_forced_of_persistent_shared_boundary hShared
  refine ⟨w, ?_, ?_⟩
  · intro m
    exact (hDigits m).1
  · intro m
    exact (hDigits m).2

/-- For a fixed left-right split witness, persistent later shared boundary is
equivalent to the existence of an ambiguous-tail witness extending that split. -/
theorem exists_iff_persistent_shared_boundary
    {digits₁ digits₂ : Nat → BinaryDigit}
    (w : DyadicLeftRightWitness digits₁ digits₂) :
    (∃ aw : DyadicAmbiguousWitness digits₁ digits₂, aw.split = w) ↔
      (∀ k,
        (intervalsOfDigits digits₁ ((w.stage + 1) + k)).rightIndex =
          (intervalsOfDigits digits₂ ((w.stage + 1) + k)).leftIndex) := by
  constructor
  · intro h k
    rcases h with ⟨aw, hsplit⟩
    cases hsplit
    exact aw.shared_boundary_later k
  · intro hShared
    exact ⟨of_persistent_shared_boundary w hShared, rfl⟩

/-- If two ambiguous witnesses share the same upper thread, then the lower
interval threads agree at every finite stage. -/
theorem intervals_eq_of_common_upper
    {lower₁ lower₂ upper : Nat → BinaryDigit}
    (w₁ : DyadicAmbiguousWitness lower₁ upper)
    (w₂ : DyadicAmbiguousWitness lower₂ upper) :
    ∀ n, intervalsOfDigits lower₁ n = intervalsOfDigits lower₂ n := by
  intro n
  let k := (w₁.split.stage + 1) + (w₂.split.stage + 1)
  have hN₁ :
      (w₁.split.stage + 1) + (n + (w₂.split.stage + 1)) = n + k := by
    change (w₁.split.stage + 1) + (n + (w₂.split.stage + 1)) =
      n + ((w₁.split.stage + 1) + (w₂.split.stage + 1))
    calc
      (w₁.split.stage + 1) + (n + (w₂.split.stage + 1))
          = ((w₁.split.stage + 1) + n) + (w₂.split.stage + 1) := by
              exact (Nat.add_assoc (w₁.split.stage + 1) n (w₂.split.stage + 1)).symm
      _ = (n + (w₁.split.stage + 1)) + (w₂.split.stage + 1) := by
            rw [Nat.add_comm (w₁.split.stage + 1) n]
      _ = n + ((w₁.split.stage + 1) + (w₂.split.stage + 1)) := by
            exact Nat.add_assoc n (w₁.split.stage + 1) (w₂.split.stage + 1)
  have hN₂ :
      (w₂.split.stage + 1) + (n + (w₁.split.stage + 1)) = n + k := by
    change (w₂.split.stage + 1) + (n + (w₁.split.stage + 1)) =
      n + ((w₁.split.stage + 1) + (w₂.split.stage + 1))
    calc
      (w₂.split.stage + 1) + (n + (w₁.split.stage + 1))
          = ((w₂.split.stage + 1) + n) + (w₁.split.stage + 1) := by
              exact (Nat.add_assoc (w₂.split.stage + 1) n (w₁.split.stage + 1)).symm
      _ = (n + (w₂.split.stage + 1)) + (w₁.split.stage + 1) := by
            rw [Nat.add_comm (w₂.split.stage + 1) n]
      _ = n + ((w₂.split.stage + 1) + (w₁.split.stage + 1)) := by
            exact Nat.add_assoc n (w₂.split.stage + 1) (w₁.split.stage + 1)
      _ = n + ((w₁.split.stage + 1) + (w₂.split.stage + 1)) := by
            rw [Nat.add_comm (w₂.split.stage + 1) (w₁.split.stage + 1)]
  have hRight₁ :
      (intervalsOfDigits lower₁ (n + k)).rightIndex =
        (intervalsOfDigits upper (n + k)).leftIndex := by
    rw [← hN₁]
    exact w₁.shared_boundary_later (n + (w₂.split.stage + 1))
  have hRight₂ :
      (intervalsOfDigits lower₂ (n + k)).rightIndex =
        (intervalsOfDigits upper (n + k)).leftIndex := by
    rw [← hN₂]
    exact w₂.shared_boundary_later (n + (w₁.split.stage + 1))
  have hEqLater : intervalsOfDigits lower₁ (n + k) = intervalsOfDigits lower₂ (n + k) := by
    exact dyadicInterval_eq_of_rightIndex_eq (hRight₁.trans hRight₂.symm)
  exact intervalsOfDigits_eq_of_eq_later (n := n) (k := k) hEqLater

/-- If two ambiguous witnesses share the same lower thread, then the upper
interval threads agree at every finite stage. -/
theorem intervals_eq_of_common_lower
    {lower upper₁ upper₂ : Nat → BinaryDigit}
    (w₁ : DyadicAmbiguousWitness lower upper₁)
    (w₂ : DyadicAmbiguousWitness lower upper₂) :
    ∀ n, intervalsOfDigits upper₁ n = intervalsOfDigits upper₂ n := by
  intro n
  let k := (w₁.split.stage + 1) + (w₂.split.stage + 1)
  have hN₁ :
      (w₁.split.stage + 1) + (n + (w₂.split.stage + 1)) = n + k := by
    change (w₁.split.stage + 1) + (n + (w₂.split.stage + 1)) =
      n + ((w₁.split.stage + 1) + (w₂.split.stage + 1))
    calc
      (w₁.split.stage + 1) + (n + (w₂.split.stage + 1))
          = ((w₁.split.stage + 1) + n) + (w₂.split.stage + 1) := by
              exact (Nat.add_assoc (w₁.split.stage + 1) n (w₂.split.stage + 1)).symm
      _ = (n + (w₁.split.stage + 1)) + (w₂.split.stage + 1) := by
            rw [Nat.add_comm (w₁.split.stage + 1) n]
      _ = n + ((w₁.split.stage + 1) + (w₂.split.stage + 1)) := by
            exact Nat.add_assoc n (w₁.split.stage + 1) (w₂.split.stage + 1)
  have hN₂ :
      (w₂.split.stage + 1) + (n + (w₁.split.stage + 1)) = n + k := by
    change (w₂.split.stage + 1) + (n + (w₁.split.stage + 1)) =
      n + ((w₁.split.stage + 1) + (w₂.split.stage + 1))
    calc
      (w₂.split.stage + 1) + (n + (w₁.split.stage + 1))
          = ((w₂.split.stage + 1) + n) + (w₁.split.stage + 1) := by
              exact (Nat.add_assoc (w₂.split.stage + 1) n (w₁.split.stage + 1)).symm
      _ = (n + (w₂.split.stage + 1)) + (w₁.split.stage + 1) := by
            rw [Nat.add_comm (w₂.split.stage + 1) n]
      _ = n + ((w₂.split.stage + 1) + (w₁.split.stage + 1)) := by
            exact Nat.add_assoc n (w₂.split.stage + 1) (w₁.split.stage + 1)
      _ = n + ((w₁.split.stage + 1) + (w₂.split.stage + 1)) := by
            rw [Nat.add_comm (w₂.split.stage + 1) (w₁.split.stage + 1)]
  have hLeft₁ :
      (intervalsOfDigits upper₁ (n + k)).leftIndex =
        (intervalsOfDigits lower (n + k)).rightIndex := by
    rw [← hN₁]
    exact (w₁.shared_boundary_later (n + (w₂.split.stage + 1))).symm
  have hLeft₂ :
      (intervalsOfDigits upper₂ (n + k)).leftIndex =
        (intervalsOfDigits lower (n + k)).rightIndex := by
    rw [← hN₂]
    exact (w₂.shared_boundary_later (n + (w₁.split.stage + 1))).symm
  have hEqLater : intervalsOfDigits upper₁ (n + k) = intervalsOfDigits upper₂ (n + k) := by
    exact dyadicInterval_eq_of_leftIndex_eq (hLeft₁.trans hLeft₂.symm)
  exact intervalsOfDigits_eq_of_eq_later (n := n) (k := k) hEqLater

/-- A thread cannot serve as the upper side of one ambiguous witness and the
lower side of another. -/
theorem false_of_upper_then_lower
    {lower middle upper : Nat → BinaryDigit}
    (w₁ : DyadicAmbiguousWitness lower middle)
    (w₂ : DyadicAmbiguousWitness middle upper) :
    False := by
  let N := (w₁.split.stage + 1) + (w₂.split.stage + 1)
  have hLeft : middle N = BinaryDigit.left := by
    dsimp [N]
    simpa [Nat.add_assoc] using w₁.inward_right (w₂.split.stage + 1)
  have hRight : middle N = BinaryDigit.right := by
    have h := w₂.inward_left (w₁.split.stage + 1)
    simpa [N, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
  rw [hLeft] at hRight
  cases hRight

end DyadicAmbiguousWitness

/-- The canonical midpoint tower refines the left interval by taking the right
child at each stage. -/
theorem midpointLeftIntervals_succ (n : Nat) :
    midpointLeftIntervals (n + 1) = rightChildInterval (midpointLeftIntervals n) := by
  rfl

/-- The canonical midpoint tower refines the right interval by taking the left
child at each stage. -/
theorem midpointRightIntervals_succ (n : Nat) :
    midpointRightIntervals (n + 1) = leftChildInterval (midpointRightIntervals n) := by
  rfl

/-- Every stage of the canonical midpoint-adjacent tower keeps the shared
interior boundary. -/
theorem midpointBoundary_shared_boundary (n : Nat) :
    (midpointLeftIntervals n).rightIndex =
      (midpointRightIntervals n).leftIndex := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change (rightChildInterval (midpointLeftIntervals n)).rightIndex =
          (leftChildInterval (midpointRightIntervals n)).leftIndex
      calc
        (rightChildInterval (midpointLeftIntervals n)).rightIndex
            = 2 * (midpointLeftIntervals n).rightIndex := by
                rfl
        _ = 2 * (midpointRightIntervals n).leftIndex := by
              rw [ih]
        _ = (leftChildInterval (midpointRightIntervals n)).leftIndex := by
              rfl

/-- Successive stages of the canonical midpoint-adjacent tower live on strictly
finer meshes. -/
theorem midpointBoundary_mesh_strict (n : Nat) :
    powTwo (n + 1) < powTwo (n + 2) := by
  exact powTwo_lt_step (n + 1)

/-- The shared boundary index in the canonical midpoint tower doubles at each
stage. -/
theorem midpointBoundary_rightIndex_step (n : Nat) :
    (midpointLeftIntervals (n + 1)).rightIndex =
      2 * (midpointLeftIntervals n).rightIndex := by
  change (rightChildInterval (midpointLeftIntervals n)).rightIndex =
      2 * (midpointLeftIntervals n).rightIndex
  rfl

/-- At stage `n`, the shared midpoint boundary sits at index `powTwo n` on the
mesh `powTwo (n + 1)`. -/
theorem midpointBoundary_rightIndex_eq_powTwo (n : Nat) :
    (midpointLeftIntervals n).rightIndex = powTwo n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [midpointBoundary_rightIndex_step, ih, powTwo_step]

/-- The right interval in the canonical midpoint tower meets the same midpoint
boundary index. -/
theorem midpointBoundary_leftIndex_eq_powTwo (n : Nat) :
    (midpointRightIntervals n).leftIndex = powTwo n := by
  rw [← midpointBoundary_shared_boundary]
  exact midpointBoundary_rightIndex_eq_powTwo n

/-- The right interval in the canonical midpoint tower extends exactly one mesh
step past the midpoint boundary. -/
theorem midpointRightIntervals_rightIndex_eq_powTwo_succ (n : Nat) :
    (midpointRightIntervals n).rightIndex = powTwo n + 1 := by
  calc
    (midpointRightIntervals n).rightIndex = (midpointRightIntervals n).leftIndex + 1 := by
      exact (midpointRightIntervals n).unit_width
    _ = powTwo n + 1 := by
      rw [midpointBoundary_leftIndex_eq_powTwo]

/-- The left interval in the canonical midpoint tower ends exactly at the mesh
midpoint. -/
theorem midpointLeftIntervals_unit_width_at_powTwo (n : Nat) :
    (midpointLeftIntervals n).leftIndex + 1 = powTwo n := by
  rw [← (midpointLeftIntervals n).unit_width]
  exact midpointBoundary_rightIndex_eq_powTwo n

/-- The left midpoint ambiguity tower is exactly the interval thread induced by
`0.0111...`, shifted by one stage. -/
theorem midpointLeftIntervals_eq_intervalsOfDigits (n : Nat) :
    midpointLeftIntervals n = intervalsOfDigits midpointLowerDigits (n + 1) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        midpointLeftIntervals (n + 1)
            = rightChildInterval (midpointLeftIntervals n) := midpointLeftIntervals_succ n
        _ = rightChildInterval (intervalsOfDigits midpointLowerDigits (n + 1)) := by
              rw [ih]
        _ = intervalsOfDigits midpointLowerDigits ((n + 1) + 1) := by
              rw [intervalsOfDigits]
              rfl

/-- The right midpoint ambiguity tower is exactly the interval thread induced by
`0.1000...`, shifted by one stage. -/
theorem midpointRightIntervals_eq_intervalsOfDigits (n : Nat) :
    midpointRightIntervals n = intervalsOfDigits midpointUpperDigits (n + 1) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        midpointRightIntervals (n + 1)
            = leftChildInterval (midpointRightIntervals n) := midpointRightIntervals_succ n
        _ = leftChildInterval (intervalsOfDigits midpointUpperDigits (n + 1)) := by
              rw [ih]
        _ = intervalsOfDigits midpointUpperDigits ((n + 1) + 1) := by
              rw [intervalsOfDigits]
              rfl

/-- Stage-zero left-right split witness for the canonical midpoint ambiguity
digits. -/
def midpointDigits_witness : DyadicLeftRightWitness midpointLowerDigits midpointUpperDigits where
  stage := 0
  common_interval := rfl
  left_digit := rfl
  right_digit := rfl

/-- The canonical midpoint ambiguity digits form an explicit ambiguous-tail
witness. -/
def midpointDigits_ambiguousWitness :
    DyadicAmbiguousWitness midpointLowerDigits midpointUpperDigits where
  split := midpointDigits_witness
  inward_left := by
    intro m
    cases m <;> rfl
  inward_right := by
    intro m
    cases m <;> rfl

/-- The canonical midpoint ambiguity digits remain ordered at every later
finite stage. -/
theorem midpointDigits_precedes_later (k : Nat) :
    DyadicIntervalPrecedes
      (intervalsOfDigits midpointLowerDigits (1 + k))
      (intervalsOfDigits midpointUpperDigits (1 + k)) := by
  exact midpointDigits_witness.precedes_later k

/-- The canonical midpoint ambiguity digits remain distinct at every later
finite stage. -/
theorem midpointDigits_distinct_later (k : Nat) :
    intervalsOfDigits midpointLowerDigits (1 + k) ≠
      intervalsOfDigits midpointUpperDigits (1 + k) := by
  exact midpointDigits_witness.distinct_later k

/-- The canonical midpoint ambiguity digits realize the same shared boundary as
the explicit midpoint interval tower. -/
theorem midpointDigits_shared_boundary (n : Nat) :
    (intervalsOfDigits midpointLowerDigits (n + 1)).rightIndex =
      (intervalsOfDigits midpointUpperDigits (n + 1)).leftIndex := by
  have h := midpointDigits_ambiguousWitness.shared_boundary_later n
  rw [show midpointDigits_ambiguousWitness.split.stage = 0 by rfl] at h
  rw [Nat.zero_add, Nat.add_comm 1 n] at h
  exact h

end CoherenceCalculus
