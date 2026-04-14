import CoherenceCalculus.Foundation.DyadicBoundaryPairCore

/-!
# Foundation.DyadicIdentificationCore

Quotient-free identification data for dyadic digit threads.

This module does not identify threads by quotient. Instead it records explicit
data witnessing why two digit threads should be regarded as presenting the same
boundary point candidate:

- either their interval threads agree at every finite stage, or
- they differ by a classified ambiguous-tail witness, in one orientation or the
  other.
-/

namespace CoherenceCalculus

/-- Explicit quotient-free identification data for dyadic digit threads. -/
inductive DyadicBoundaryIdentification
    (digits₁ digits₂ : Nat → BinaryDigit) : Type where
  | exact :
      (∀ n, intervalsOfDigits digits₁ n = intervalsOfDigits digits₂ n) →
      DyadicBoundaryIdentification digits₁ digits₂
  | ambiguousLeftRight :
      DyadicAmbiguousWitness digits₁ digits₂ →
      DyadicBoundaryIdentification digits₁ digits₂
  | ambiguousRightLeft :
      DyadicAmbiguousWitness digits₂ digits₁ →
      DyadicBoundaryIdentification digits₁ digits₂

namespace DyadicBoundaryIdentification

/-- Exact interval-thread agreement transports an ambiguous witness on the left
side. -/
def ambiguous_of_exact_left
    {digits₁ digits₂ digits₃ : Nat → BinaryDigit}
    (hExact : ∀ n, intervalsOfDigits digits₁ n = intervalsOfDigits digits₂ n)
    (w : DyadicAmbiguousWitness digits₂ digits₃) :
    DyadicAmbiguousWitness digits₁ digits₃ where
  split := {
    stage := w.split.stage
    common_interval := by
      calc
        intervalsOfDigits digits₁ w.split.stage =
            intervalsOfDigits digits₂ w.split.stage := hExact w.split.stage
        _ = intervalsOfDigits digits₃ w.split.stage := w.split.common_interval
    left_digit := by
      calc
        digits₁ w.split.stage = digits₂ w.split.stage :=
          digits_eq_of_intervals_eq_all hExact w.split.stage
        _ = BinaryDigit.left := w.split.left_digit
    right_digit := w.split.right_digit
  }
  inward_left := by
    intro m
    calc
      digits₁ (w.split.stage + 1 + m) = digits₂ (w.split.stage + 1 + m) :=
        digits_eq_of_intervals_eq_all hExact (w.split.stage + 1 + m)
      _ = BinaryDigit.right := w.inward_left m
  inward_right := w.inward_right

/-- Exact interval-thread agreement transports an ambiguous witness on the right
side. -/
def ambiguous_of_exact_right
    {digits₁ digits₂ digits₃ : Nat → BinaryDigit}
    (w : DyadicAmbiguousWitness digits₁ digits₂)
    (hExact : ∀ n, intervalsOfDigits digits₂ n = intervalsOfDigits digits₃ n) :
    DyadicAmbiguousWitness digits₁ digits₃ where
  split := {
    stage := w.split.stage
    common_interval := by
      calc
        intervalsOfDigits digits₁ w.split.stage =
            intervalsOfDigits digits₂ w.split.stage := w.split.common_interval
        _ = intervalsOfDigits digits₃ w.split.stage := hExact w.split.stage
    left_digit := w.split.left_digit
    right_digit := by
      calc
        digits₃ w.split.stage = digits₂ w.split.stage := by
          exact (digits_eq_of_intervals_eq_all hExact w.split.stage).symm
        _ = BinaryDigit.right := w.split.right_digit
  }
  inward_left := w.inward_left
  inward_right := by
    intro m
    calc
      digits₃ (w.split.stage + 1 + m) = digits₂ (w.split.stage + 1 + m) := by
        exact (digits_eq_of_intervals_eq_all hExact (w.split.stage + 1 + m)).symm
      _ = BinaryDigit.left := w.inward_right m

/-- Every digit thread is boundary-identified with itself. -/
def refl (digits : Nat → BinaryDigit) : DyadicBoundaryIdentification digits digits :=
  .exact (fun _ => rfl)

/-- Boundary-identification data is symmetric by construction. -/
def symm {digits₁ digits₂ : Nat → BinaryDigit} :
    DyadicBoundaryIdentification digits₁ digits₂ →
      DyadicBoundaryIdentification digits₂ digits₁
  | .exact h => .exact (fun n => (h n).symm)
  | .ambiguousLeftRight w => .ambiguousRightLeft w
  | .ambiguousRightLeft w => .ambiguousLeftRight w

/-- A persistent shared-boundary split witness yields quotient-free boundary
identification. -/
def of_persistent_shared_boundary
    {digits₁ digits₂ : Nat → BinaryDigit}
    (w : DyadicLeftRightWitness digits₁ digits₂)
    (hShared :
      ∀ k,
        (intervalsOfDigits digits₁ ((w.stage + 1) + k)).rightIndex =
          (intervalsOfDigits digits₂ ((w.stage + 1) + k)).leftIndex) :
    DyadicBoundaryIdentification digits₁ digits₂ :=
  .ambiguousLeftRight (DyadicAmbiguousWitness.of_persistent_shared_boundary w hShared)

/-- The canonical midpoint ambiguity digits are quotient-free boundary
identified. -/
def midpoint : DyadicBoundaryIdentification midpointLowerDigits midpointUpperDigits :=
  .ambiguousLeftRight midpointDigits_ambiguousWitness

/-- The canonical midpoint ambiguity digits are also identified in the reverse
orientation. -/
def midpoint_symm :
    DyadicBoundaryIdentification midpointUpperDigits midpointLowerDigits :=
  symm midpoint

/-- Boundary-identification data is transitive. -/
def trans {digits₁ digits₂ digits₃ : Nat → BinaryDigit} :
    DyadicBoundaryIdentification digits₁ digits₂ →
      DyadicBoundaryIdentification digits₂ digits₃ →
      DyadicBoundaryIdentification digits₁ digits₃
  | .exact h₁₂, .exact h₂₃ =>
      .exact (fun n => (h₁₂ n).trans (h₂₃ n))
  | .exact h₁₂, .ambiguousLeftRight w₂₃ =>
      .ambiguousLeftRight (ambiguous_of_exact_left h₁₂ w₂₃)
  | .exact h₁₂, .ambiguousRightLeft w₃₂ =>
      .ambiguousRightLeft (ambiguous_of_exact_right w₃₂ (fun n => (h₁₂ n).symm))
  | .ambiguousLeftRight w₁₂, .exact h₂₃ =>
      .ambiguousLeftRight (ambiguous_of_exact_right w₁₂ h₂₃)
  | .ambiguousRightLeft w₂₁, .exact h₂₃ =>
      .ambiguousRightLeft (ambiguous_of_exact_left (fun n => (h₂₃ n).symm) w₂₁)
  | .ambiguousLeftRight w₁₂, .ambiguousLeftRight w₂₃ =>
      False.elim (DyadicAmbiguousWitness.false_of_upper_then_lower w₁₂ w₂₃)
  | .ambiguousLeftRight w₁₂, .ambiguousRightLeft w₃₂ =>
      .exact (DyadicAmbiguousWitness.intervals_eq_of_common_upper w₁₂ w₃₂)
  | .ambiguousRightLeft w₂₁, .ambiguousLeftRight w₂₃ =>
      .exact (DyadicAmbiguousWitness.intervals_eq_of_common_lower w₂₁ w₂₃)
  | .ambiguousRightLeft w₂₁, .ambiguousRightLeft w₃₂ =>
      False.elim (DyadicAmbiguousWitness.false_of_upper_then_lower w₃₂ w₂₁)

end DyadicBoundaryIdentification

end CoherenceCalculus
