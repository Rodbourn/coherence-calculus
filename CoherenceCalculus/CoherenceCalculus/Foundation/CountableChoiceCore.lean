import CoherenceCalculus.Foundation.StructuredChoiceCore

/-!
# Foundation.CountableChoiceCore

Countable structured choice for explicit finite partial-choice systems.

This module specializes `StructuredChoiceCore` to the case where stage `n`
consists of compatible partial choices on the first `n` coordinates of a
countable family of explicitly finite, nonempty fibers.
-/

namespace CoherenceCalculus

/-- Explicit countable family with a nonempty finite enumeration at every
coordinate. -/
structure ExplicitFiniteFamily where
  Carrier : Nat → Type
  fiberSize : Nat → Nat
  fiberElem : ∀ n, Fin (Nat.succ (fiberSize n)) → Carrier n

/-- Partial choices on the first `n` coordinates. -/
inductive PartialChoice (F : ExplicitFiniteFamily) : Nat → Type where
  | nil : PartialChoice F 0
  | snoc : PartialChoice F n → F.Carrier n → PartialChoice F (n + 1)

/-- Drop the last coordinate from a partial choice. -/
def partialChoiceTruncate (F : ExplicitFiniteFamily) {n : Nat} :
    PartialChoice F (n + 1) → PartialChoice F n
  | .snoc p _ => p

/-- Read the last chosen coordinate from a partial choice. -/
def partialChoiceLast (F : ExplicitFiniteFamily) {n : Nat} :
    PartialChoice F (n + 1) → F.Carrier n
  | .snoc _ x => x

/-- Canonical coherent thread of partial choices obtained by taking the first
available coordinate at each stage. -/
def canonicalPartialChoiceThread (F : ExplicitFiniteFamily) :
    (n : Nat) → PartialChoice F n
  | 0 => PartialChoice.nil
  | n + 1 => PartialChoice.snoc (canonicalPartialChoiceThread F n)
      (F.fiberElem n ⟨0, Nat.succ_pos _⟩)

/-- Countable structured choice for explicit finite partial-choice systems. -/
theorem countable_structured_choice (F : ExplicitFiniteFamily) :
    ∃ c : (n : Nat) → F.Carrier n,
      ∃ s : (n : Nat) → PartialChoice F n,
        s 0 = PartialChoice.nil ∧
        (∀ n, s (n + 1) = PartialChoice.snoc (s n) (c n)) := by
  refine ⟨fun n => F.fiberElem n ⟨0, Nat.succ_pos _⟩,
    canonicalPartialChoiceThread F, rfl, ?_⟩
  intro n
  rfl

end CoherenceCalculus
