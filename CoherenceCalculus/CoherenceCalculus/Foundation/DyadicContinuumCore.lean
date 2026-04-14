import CoherenceCalculus.Foundation.PartialChoiceCore

/-!
# Foundation.DyadicContinuumCore

Minimal continuum scaffold derived from explicit binary refinement.

This does not import reals, quotients, or field structure. It builds the unit
dyadic continuum as coherent infinite refinement threads through binary cells.
The mesh refines by powers of two, giving the first honest continuous-looking
object above the discrete bedrock.
-/

namespace CoherenceCalculus

/-- Binary refinement digit. -/
inductive BinaryDigit where
  | left
  | right
  deriving DecidableEq, Repr

/-- Explicit two-point family at each natural stage. -/
def binaryFamily : ExplicitFiniteFamily where
  Carrier := fun _ => BinaryDigit
  fiberSize := fun _ => 1
  fiberElem := by
    intro _ i
    cases i with
    | mk val isLt =>
        cases val with
        | zero => exact BinaryDigit.left
        | succ val =>
            cases val with
            | zero => exact BinaryDigit.right
            | succ k =>
                have h1 : Nat.succ k < 1 := Nat.lt_of_succ_lt_succ isLt
                have h0 : k < 0 := Nat.lt_of_succ_lt_succ h1
                exact False.elim (Nat.not_lt_zero _ h0)

/-- Dyadic cell at stage `n`, represented by a binary word of length `n`. -/
abbrev DyadicCell (n : Nat) : Type := PartialChoice binaryFamily n

/-- Stage-zero dyadic cell. -/
def rootDyadicCell : DyadicCell 0 := PartialChoice.nil

/-- Extend a dyadic cell by one binary refinement digit. -/
def refineDyadicCell {n : Nat} (c : DyadicCell n) (b : BinaryDigit) : DyadicCell (n + 1) :=
  PartialChoice.snoc c b

/-- Drop the last digit of a dyadic cell. -/
def parentDyadicCell {n : Nat} : DyadicCell (n + 1) → DyadicCell n :=
  partialChoiceTruncate binaryFamily

/-- Read the last refinement digit of a non-root dyadic cell. -/
def lastDyadicDigit {n : Nat} : DyadicCell (n + 1) → BinaryDigit :=
  partialChoiceLast binaryFamily

/-- Refinement is injective in the parent cell. -/
theorem refineDyadicCell_injective_left {n : Nat}
    {c d : DyadicCell n} {b₁ b₂ : BinaryDigit}
    (h : refineDyadicCell c b₁ = refineDyadicCell d b₂) :
    c = d := by
  exact partialChoice_snoc_injective_left binaryFamily h

/-- Refinement is injective in the last digit. -/
theorem refineDyadicCell_injective_right {n : Nat}
    {c d : DyadicCell n} {b₁ b₂ : BinaryDigit}
    (h : refineDyadicCell c b₁ = refineDyadicCell d b₂) :
    b₁ = b₂ := by
  exact partialChoice_snoc_injective_right binaryFamily h

/-- Equality of refined dyadic cells is exactly equality of the parent cell and
the refining digit. -/
theorem refineDyadicCell_eq_iff {n : Nat}
    {c d : DyadicCell n} {b₁ b₂ : BinaryDigit} :
    refineDyadicCell c b₁ = refineDyadicCell d b₂ ↔ c = d ∧ b₁ = b₂ := by
  exact partialChoice_snoc_eq_iff binaryFamily

/-- Denominator scale of the stage-`n` dyadic mesh. -/
def powTwo : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * powTwo n

/-- The dyadic mesh doubles at each refinement stage. -/
theorem powTwo_step (n : Nat) : powTwo (n + 1) = 2 * powTwo n := by
  rfl

/-- Every dyadic cell has exactly two explicit children. -/
theorem dyadicCell_two_children {n : Nat} (c : DyadicCell n) :
    refineDyadicCell c BinaryDigit.left ≠ refineDyadicCell c BinaryDigit.right := by
  intro h
  cases h

/-- A coherent dyadic thread is an infinite nested sequence of dyadic cells. -/
structure DyadicThread where
  cells : (n : Nat) → DyadicCell n
  root : cells 0 = rootDyadicCell
  coherent : ∀ n, parentDyadicCell (cells (n + 1)) = cells n

/-- The canonical all-left dyadic refinement thread. -/
def leftDyadicCells : (n : Nat) → DyadicCell n
  | 0 => rootDyadicCell
  | n + 1 => refineDyadicCell (leftDyadicCells n) BinaryDigit.left

/-- The canonical all-left dyadic thread. -/
def leftDyadicThread : DyadicThread where
  cells := leftDyadicCells
  root := rfl
  coherent := by
    intro n
    rfl

/-- The binary family also yields an infinite binary digit sequence. -/
theorem binarySequence_exists :
    Nonempty (Nat → BinaryDigit) := by
  exact ⟨fun _ => BinaryDigit.left⟩

end CoherenceCalculus
