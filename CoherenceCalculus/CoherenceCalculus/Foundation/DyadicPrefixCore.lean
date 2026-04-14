import CoherenceCalculus.Foundation.DyadicComparisonCore

/-!
# Foundation.DyadicPrefixCore

Common-prefix transport for dyadic digit threads.

This module makes the self-similarity of the clean dyadic scaffold explicit.
Prepending the same binary digit to two digit threads embeds their interval
threads into the left or right half of the next mesh, preserving exact
agreement, ambiguous-tail identification, and strict separation.
-/

namespace CoherenceCalculus

/-- Prepend one binary digit to an infinite digit thread. -/
def prependDigitDigits (b : BinaryDigit) (digits : Nat → BinaryDigit) : Nat → BinaryDigit
  | 0 => b
  | n + 1 => digits n

/-- Left-half embedding of a dyadic interval onto the next finer mesh. -/
def leftEmbedInterval {n : Nat} (I : DyadicInterval n) : DyadicInterval (n + 1) where
  leftIndex := I.leftIndex
  rightIndex := I.rightIndex
  unit_width := I.unit_width
  right_bound := Nat.le_trans I.right_bound (Nat.le_of_lt (powTwo_lt_step n))

/-- Right-half embedding of a dyadic interval onto the next finer mesh. -/
def rightEmbedInterval {n : Nat} (I : DyadicInterval n) : DyadicInterval (n + 1) where
  leftIndex := powTwo n + I.leftIndex
  rightIndex := powTwo n + I.rightIndex
  unit_width := by
    calc
      powTwo n + I.rightIndex = powTwo n + (I.leftIndex + 1) := by
        rw [I.unit_width]
      _ = (powTwo n + I.leftIndex) + 1 := by
        rw [Nat.add_assoc]
  right_bound := by
    calc
      powTwo n + I.rightIndex ≤ powTwo n + powTwo n :=
        Nat.add_le_add_left I.right_bound _
      _ = powTwo (n + 1) := by
        rw [powTwo_step, Nat.two_mul]

/-- The left embedding of the root interval is the left child of the root. -/
theorem leftEmbedInterval_root :
    leftEmbedInterval rootInterval = leftChildInterval rootInterval := by
  apply DyadicInterval.ext <;> rfl

/-- The right embedding of the root interval is the right child of the root. -/
theorem rightEmbedInterval_root :
    rightEmbedInterval rootInterval = rightChildInterval rootInterval := by
  apply DyadicInterval.ext <;> rfl

/-- Left embedding commutes with taking the left child. -/
theorem leftChildInterval_leftEmbed {n : Nat} (I : DyadicInterval n) :
    leftChildInterval (leftEmbedInterval I) =
      leftEmbedInterval (leftChildInterval I) := by
  apply DyadicInterval.ext <;> rfl

/-- Left embedding commutes with taking the right child. -/
theorem rightChildInterval_leftEmbed {n : Nat} (I : DyadicInterval n) :
    rightChildInterval (leftEmbedInterval I) =
      leftEmbedInterval (rightChildInterval I) := by
  apply DyadicInterval.ext <;> rfl

/-- Right embedding commutes with taking the left child. -/
theorem leftChildInterval_rightEmbed {n : Nat} (I : DyadicInterval n) :
    leftChildInterval (rightEmbedInterval I) =
      rightEmbedInterval (leftChildInterval I) := by
  apply DyadicInterval.ext
  · calc
      (leftChildInterval (rightEmbedInterval I)).leftIndex
          = 2 * (powTwo n + I.leftIndex) := by
              rfl
      _ = 2 * powTwo n + 2 * I.leftIndex := by
            rw [Nat.mul_add]
      _ = powTwo (n + 1) + 2 * I.leftIndex := by
            rw [powTwo_step]
      _ = (rightEmbedInterval (leftChildInterval I)).leftIndex := by
            rfl
  · calc
      (leftChildInterval (rightEmbedInterval I)).rightIndex
          = 2 * (powTwo n + I.leftIndex) + 1 := by
              rfl
      _ = (2 * powTwo n + 2 * I.leftIndex) + 1 := by
            rw [Nat.mul_add]
      _ = 2 * powTwo n + (2 * I.leftIndex + 1) := by
            rw [Nat.add_assoc]
      _ = powTwo (n + 1) + (2 * I.leftIndex + 1) := by
            rw [powTwo_step]
      _ = (rightEmbedInterval (leftChildInterval I)).rightIndex := by
            rfl

/-- Right embedding commutes with taking the right child. -/
theorem rightChildInterval_rightEmbed {n : Nat} (I : DyadicInterval n) :
    rightChildInterval (rightEmbedInterval I) =
      rightEmbedInterval (rightChildInterval I) := by
  apply DyadicInterval.ext
  · calc
      (rightChildInterval (rightEmbedInterval I)).leftIndex
          = 2 * (powTwo n + I.leftIndex) + 1 := by
              rfl
      _ = (2 * powTwo n + 2 * I.leftIndex) + 1 := by
            rw [Nat.mul_add]
      _ = 2 * powTwo n + (2 * I.leftIndex + 1) := by
            rw [Nat.add_assoc]
      _ = powTwo (n + 1) + (2 * I.leftIndex + 1) := by
            rw [powTwo_step]
      _ = (rightEmbedInterval (rightChildInterval I)).leftIndex := by
            rfl
  · calc
      (rightChildInterval (rightEmbedInterval I)).rightIndex
          = 2 * (powTwo n + I.rightIndex) := by
              rfl
      _ = 2 * powTwo n + 2 * I.rightIndex := by
            rw [Nat.mul_add]
      _ = powTwo (n + 1) + 2 * I.rightIndex := by
            rw [powTwo_step]
      _ = (rightEmbedInterval (rightChildInterval I)).rightIndex := by
            rfl

/-- Prepending `left` embeds a digit thread into the left half of the next mesh. -/
theorem intervalsOfDigits_prependLeft (digits : Nat → BinaryDigit) :
    ∀ n,
      intervalsOfDigits (prependDigitDigits BinaryDigit.left digits) (n + 1) =
        leftEmbedInterval (intervalsOfDigits digits n)
  | 0 => leftEmbedInterval_root
  | n + 1 => by
      cases h : digits n with
      | left =>
          calc
            intervalsOfDigits (prependDigitDigits BinaryDigit.left digits) ((n + 1) + 1)
                = leftChildInterval
                    (intervalsOfDigits (prependDigitDigits BinaryDigit.left digits) (n + 1)) := by
                      change
                        (match digits n with
                        | BinaryDigit.left =>
                            leftChildInterval
                              (intervalsOfDigits (prependDigitDigits BinaryDigit.left digits) (n + 1))
                        | BinaryDigit.right =>
                            rightChildInterval
                              (intervalsOfDigits (prependDigitDigits BinaryDigit.left digits) (n + 1))) =
                          leftChildInterval
                            (intervalsOfDigits (prependDigitDigits BinaryDigit.left digits) (n + 1))
                      rw [h]
            _ = leftChildInterval (leftEmbedInterval (intervalsOfDigits digits n)) := by
                  rw [intervalsOfDigits_prependLeft digits n]
            _ = leftEmbedInterval (leftChildInterval (intervalsOfDigits digits n)) := by
                  rw [leftChildInterval_leftEmbed]
            _ = leftEmbedInterval (intervalsOfDigits digits (n + 1)) := by
                  rw [intervalsOfDigits, h]
      | right =>
          calc
            intervalsOfDigits (prependDigitDigits BinaryDigit.left digits) ((n + 1) + 1)
                = rightChildInterval
                    (intervalsOfDigits (prependDigitDigits BinaryDigit.left digits) (n + 1)) := by
                      change
                        (match digits n with
                        | BinaryDigit.left =>
                            leftChildInterval
                              (intervalsOfDigits (prependDigitDigits BinaryDigit.left digits) (n + 1))
                        | BinaryDigit.right =>
                            rightChildInterval
                              (intervalsOfDigits (prependDigitDigits BinaryDigit.left digits) (n + 1))) =
                          rightChildInterval
                            (intervalsOfDigits (prependDigitDigits BinaryDigit.left digits) (n + 1))
                      rw [h]
            _ = rightChildInterval (leftEmbedInterval (intervalsOfDigits digits n)) := by
                  rw [intervalsOfDigits_prependLeft digits n]
            _ = leftEmbedInterval (rightChildInterval (intervalsOfDigits digits n)) := by
                  rw [rightChildInterval_leftEmbed]
            _ = leftEmbedInterval (intervalsOfDigits digits (n + 1)) := by
                  rw [intervalsOfDigits, h]

/-- Prepending `right` embeds a digit thread into the right half of the next mesh. -/
theorem intervalsOfDigits_prependRight (digits : Nat → BinaryDigit) :
    ∀ n,
      intervalsOfDigits (prependDigitDigits BinaryDigit.right digits) (n + 1) =
        rightEmbedInterval (intervalsOfDigits digits n)
  | 0 => rightEmbedInterval_root
  | n + 1 => by
      cases h : digits n with
      | left =>
          calc
            intervalsOfDigits (prependDigitDigits BinaryDigit.right digits) ((n + 1) + 1)
                = leftChildInterval
                    (intervalsOfDigits (prependDigitDigits BinaryDigit.right digits) (n + 1)) := by
                      change
                        (match digits n with
                        | BinaryDigit.left =>
                            leftChildInterval
                              (intervalsOfDigits (prependDigitDigits BinaryDigit.right digits) (n + 1))
                        | BinaryDigit.right =>
                            rightChildInterval
                              (intervalsOfDigits (prependDigitDigits BinaryDigit.right digits) (n + 1))) =
                          leftChildInterval
                            (intervalsOfDigits (prependDigitDigits BinaryDigit.right digits) (n + 1))
                      rw [h]
            _ = leftChildInterval (rightEmbedInterval (intervalsOfDigits digits n)) := by
                  rw [intervalsOfDigits_prependRight digits n]
            _ = rightEmbedInterval (leftChildInterval (intervalsOfDigits digits n)) := by
                  rw [leftChildInterval_rightEmbed]
            _ = rightEmbedInterval (intervalsOfDigits digits (n + 1)) := by
                  rw [intervalsOfDigits, h]
      | right =>
          calc
            intervalsOfDigits (prependDigitDigits BinaryDigit.right digits) ((n + 1) + 1)
                = rightChildInterval
                    (intervalsOfDigits (prependDigitDigits BinaryDigit.right digits) (n + 1)) := by
                      change
                        (match digits n with
                        | BinaryDigit.left =>
                            leftChildInterval
                              (intervalsOfDigits (prependDigitDigits BinaryDigit.right digits) (n + 1))
                        | BinaryDigit.right =>
                            rightChildInterval
                              (intervalsOfDigits (prependDigitDigits BinaryDigit.right digits) (n + 1))) =
                          rightChildInterval
                            (intervalsOfDigits (prependDigitDigits BinaryDigit.right digits) (n + 1))
                      rw [h]
            _ = rightChildInterval (rightEmbedInterval (intervalsOfDigits digits n)) := by
                  rw [intervalsOfDigits_prependRight digits n]
            _ = rightEmbedInterval (rightChildInterval (intervalsOfDigits digits n)) := by
                  rw [rightChildInterval_rightEmbed]
            _ = rightEmbedInterval (intervalsOfDigits digits (n + 1)) := by
                  rw [intervalsOfDigits, h]

/-- Left embedding preserves weak precedence. -/
theorem dyadicIntervalPrecedes_leftEmbed {n : Nat}
    {I J : DyadicInterval n}
    (h : DyadicIntervalPrecedes I J) :
    DyadicIntervalPrecedes (leftEmbedInterval I) (leftEmbedInterval J) := by
  dsimp [DyadicIntervalPrecedes, leftEmbedInterval] at *
  exact h

/-- Right embedding preserves weak precedence. -/
theorem dyadicIntervalPrecedes_rightEmbed {n : Nat}
    {I J : DyadicInterval n}
    (h : DyadicIntervalPrecedes I J) :
    DyadicIntervalPrecedes (rightEmbedInterval I) (rightEmbedInterval J) := by
  dsimp [DyadicIntervalPrecedes, rightEmbedInterval] at *
  exact Nat.add_le_add_left h _

/-- Left embedding preserves strict precedence. -/
theorem dyadicIntervalStrictPrecedes_leftEmbed {n : Nat}
    {I J : DyadicInterval n}
    (h : DyadicIntervalStrictPrecedes I J) :
    DyadicIntervalStrictPrecedes (leftEmbedInterval I) (leftEmbedInterval J) := by
  dsimp [DyadicIntervalStrictPrecedes, leftEmbedInterval] at *
  exact h

/-- Right embedding preserves strict precedence. -/
theorem dyadicIntervalStrictPrecedes_rightEmbed {n : Nat}
    {I J : DyadicInterval n}
    (h : DyadicIntervalStrictPrecedes I J) :
    DyadicIntervalStrictPrecedes (rightEmbedInterval I) (rightEmbedInterval J) := by
  dsimp [DyadicIntervalStrictPrecedes, rightEmbedInterval] at *
  exact Nat.add_lt_add_left h _

namespace DyadicAmbiguousWitness

/-- Prepending `left` preserves an ambiguous-tail witness. -/
def prependLeft
    {digits₁ digits₂ : Nat → BinaryDigit}
    (w : DyadicAmbiguousWitness digits₁ digits₂) :
    DyadicAmbiguousWitness
      (prependDigitDigits BinaryDigit.left digits₁)
      (prependDigitDigits BinaryDigit.left digits₂) where
  split := {
    stage := w.split.stage + 1
    common_interval := by
      rw [intervalsOfDigits_prependLeft, intervalsOfDigits_prependLeft, w.split.common_interval]
    left_digit := by
      change digits₁ w.split.stage = BinaryDigit.left
      exact w.split.left_digit
    right_digit := by
      change digits₂ w.split.stage = BinaryDigit.right
      exact w.split.right_digit
  }
  inward_left := by
    intro m
    simpa [prependDigitDigits, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      w.inward_left m
  inward_right := by
    intro m
    simpa [prependDigitDigits, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      w.inward_right m

/-- Prepending `right` preserves an ambiguous-tail witness. -/
def prependRight
    {digits₁ digits₂ : Nat → BinaryDigit}
    (w : DyadicAmbiguousWitness digits₁ digits₂) :
    DyadicAmbiguousWitness
      (prependDigitDigits BinaryDigit.right digits₁)
      (prependDigitDigits BinaryDigit.right digits₂) where
  split := {
    stage := w.split.stage + 1
    common_interval := by
      rw [intervalsOfDigits_prependRight, intervalsOfDigits_prependRight, w.split.common_interval]
    left_digit := by
      change digits₁ w.split.stage = BinaryDigit.left
      exact w.split.left_digit
    right_digit := by
      change digits₂ w.split.stage = BinaryDigit.right
      exact w.split.right_digit
  }
  inward_left := by
    intro m
    simpa [prependDigitDigits, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      w.inward_left m
  inward_right := by
    intro m
    simpa [prependDigitDigits, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      w.inward_right m

end DyadicAmbiguousWitness

namespace DyadicBoundaryIdentification

/-- Prepending `left` preserves quotient-free boundary identification. -/
def prependLeft
    {digits₁ digits₂ : Nat → BinaryDigit} :
    DyadicBoundaryIdentification digits₁ digits₂ →
      DyadicBoundaryIdentification
        (prependDigitDigits BinaryDigit.left digits₁)
        (prependDigitDigits BinaryDigit.left digits₂)
  | .exact hExact =>
      .exact (fun
        | 0 => rfl
        | n + 1 => by
            rw [intervalsOfDigits_prependLeft, intervalsOfDigits_prependLeft, hExact n])
  | .ambiguousLeftRight w =>
      .ambiguousLeftRight w.prependLeft
  | .ambiguousRightLeft w =>
      .ambiguousRightLeft w.prependLeft

/-- Prepending `right` preserves quotient-free boundary identification. -/
def prependRight
    {digits₁ digits₂ : Nat → BinaryDigit} :
    DyadicBoundaryIdentification digits₁ digits₂ →
      DyadicBoundaryIdentification
        (prependDigitDigits BinaryDigit.right digits₁)
        (prependDigitDigits BinaryDigit.right digits₂)
  | .exact hExact =>
      .exact (fun
        | 0 => rfl
        | n + 1 => by
            rw [intervalsOfDigits_prependRight, intervalsOfDigits_prependRight, hExact n])
  | .ambiguousLeftRight w =>
      .ambiguousLeftRight w.prependRight
  | .ambiguousRightLeft w =>
      .ambiguousRightLeft w.prependRight

end DyadicBoundaryIdentification

namespace DyadicStrictSeparation

/-- Prepending `left` preserves strict separation. -/
def prependLeft
    {digits₁ digits₂ : Nat → BinaryDigit}
    (s : DyadicStrictSeparation digits₁ digits₂) :
    DyadicStrictSeparation
      (prependDigitDigits BinaryDigit.left digits₁)
      (prependDigitDigits BinaryDigit.left digits₂) where
  stage := s.stage + 1
  strict := by
    rw [intervalsOfDigits_prependLeft, intervalsOfDigits_prependLeft]
    exact dyadicIntervalStrictPrecedes_leftEmbed s.strict

/-- Prepending `right` preserves strict separation. -/
def prependRight
    {digits₁ digits₂ : Nat → BinaryDigit}
    (s : DyadicStrictSeparation digits₁ digits₂) :
    DyadicStrictSeparation
      (prependDigitDigits BinaryDigit.right digits₁)
      (prependDigitDigits BinaryDigit.right digits₂) where
  stage := s.stage + 1
  strict := by
    rw [intervalsOfDigits_prependRight, intervalsOfDigits_prependRight]
    exact dyadicIntervalStrictPrecedes_rightEmbed s.strict

end DyadicStrictSeparation

namespace DyadicBoundaryComparison

/-- Prepending `left` preserves quotient-free boundary comparison. -/
def prependLeft
    {digits₁ digits₂ : Nat → BinaryDigit} :
    DyadicBoundaryComparison digits₁ digits₂ →
      DyadicBoundaryComparison
        (prependDigitDigits BinaryDigit.left digits₁)
        (prependDigitDigits BinaryDigit.left digits₂)
  | .identified h => .identified h.prependLeft
  | .strictLeft s => .strictLeft s.prependLeft
  | .strictRight s => .strictRight s.prependLeft

/-- Prepending `right` preserves quotient-free boundary comparison. -/
def prependRight
    {digits₁ digits₂ : Nat → BinaryDigit} :
    DyadicBoundaryComparison digits₁ digits₂ →
      DyadicBoundaryComparison
        (prependDigitDigits BinaryDigit.right digits₁)
        (prependDigitDigits BinaryDigit.right digits₂)
  | .identified h => .identified h.prependRight
  | .strictLeft s => .strictLeft s.prependRight
  | .strictRight s => .strictRight s.prependRight

end DyadicBoundaryComparison

end CoherenceCalculus
