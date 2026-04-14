/-
# Foundation.NatCore

Counting-facing natural-number layer above `AxiomCore`.

This file stays `Int`-free and avoids importing any higher algebraic
infrastructure. It provides the first constructive consequences needed for the
draft's bedrock narrative.
-/

import CoherenceCalculus.Foundation.AxiomCore

namespace CoherenceCalculus

/-- Primitives are distinguishable: for any two primitives, they are equal or
different. -/
theorem primitive_distinction {B : Bedrock} (a b : Primitive B) : a = b ∨ a ≠ b := by
  match (inferInstance : DecidableEq (Primitive B)) a b with
  | isTrue h => exact Or.inl h
  | isFalse h => exact Or.inr h

/-- Every event carries a finite dimension datum by construction. -/
theorem event_finiteness (e : Event) : ∃ n : Nat, e.dimension = n := by
  exact ⟨e.dimension, rfl⟩

/-- The reconstructed natural-number layer uses Lean's natural numbers as the
canonical counting object. -/
abbrev NatFromPrimitive : Type := Nat

/-- Successor is never zero. Stated directly to avoid importing stronger
library wrappers into the active foundation. -/
theorem succ_not_zero_counting (n : NatFromPrimitive) : Nat.succ n ≠ 0 := by
  intro h
  cases h

/-- Successor is injective. -/
theorem succ_injective_counting (n m : NatFromPrimitive)
    (h : Nat.succ n = Nat.succ m) : n = m := by
  exact Nat.succ.inj h

/-- Induction principle for the counting naturals. -/
theorem counting_induction (P : NatFromPrimitive → Prop)
    (h0 : P 0) (hstep : ∀ n, P n → P (Nat.succ n)) :
    ∀ n, P n := by
  intro n
  exact Nat.rec h0 hstep n

/-- Dimension is the count of characteristics meeting at an event. -/
def dimensionOfEvent (e : Event) : Nat := e.dimension

/-- The primitive defines the unit counting scale. -/
def fundamentalScale : Nat := 1

end CoherenceCalculus
