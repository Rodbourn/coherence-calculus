import CoherenceCalculus.Foundation.ClosureCore

/-!
# Foundation.DiophantineWidth

Draft-facing diophantine results that widen the clean bedrock without
reconnecting the archived development.

This module only packages consequences already natural for the rebuilt
foundation:
- constructive finite choice over explicitly enumerated finite families
- bundled Peano consequences for the counting naturals
- manuscript-facing aliases for binomial and holographic operator notation
- low-dimensional closure facts restated at those aliases
-/

namespace CoherenceCalculus

/-- Explicit finite family with an enumeration and a nonempty witness at each
index. This is the constructive data needed to realize finite choice without
any global choice principle. -/
structure FiniteChoiceFamily (n : Nat) where
  Carrier : Fin n → Type
  elems : (i : Fin n) → List (Carrier i)
  nonempty : ∀ i, elems i ≠ []

/-- Pick the first element of a listed nonempty finite family. -/
def chooseFromList {α : Type} (xs : List α) (h : xs ≠ []) : α := by
  cases xs with
  | nil =>
      cases (h rfl)
  | cons x _ =>
      exact x

/-- Constructive finite choice over an explicitly enumerated finite family. -/
def finite_choice {n : Nat} (fam : FiniteChoiceFamily n) :
    (i : Fin n) → fam.Carrier i :=
  fun i => chooseFromList (fam.elems i) (fam.nonempty i)

/-- Bundled Peano consequences for the rebuilt counting naturals. -/
theorem peano_from_counting :
    (∀ n : NatFromPrimitive, Nat.succ n ≠ 0) ∧
    (∀ n m : NatFromPrimitive, Nat.succ n = Nat.succ m → n = m) ∧
    (∀ P : NatFromPrimitive → Prop,
      P 0 → (∀ n, P n → P (Nat.succ n)) → ∀ n, P n) := by
  refine ⟨succ_not_zero_counting, succ_injective_counting, ?_⟩
  intro P h0 hstep
  exact counting_induction P h0 hstep

/-- Draft-facing alias for the binomial coefficient. -/
def binomial (n k : Nat) : Nat := choose n k

/-- Draft-facing name for the holographic counting defect. -/
def holographicOperator (D : Nat) : SignedCount := holographicImbalance D

/-- Closure forces count-balance once the event-level bulk and boundary counts
are identified with the corresponding diophantine counting expressions. -/
theorem completeness_from_closure {B : Bedrock}
    (e : Event)
    (hbulk : bulkCount B e = pairings (dimensionOfEvent e))
    (hboundary : boundaryCount B e = orderings (dimensionOfEvent e)) :
    pairings (dimensionOfEvent e) = orderings (dimensionOfEvent e) := by
  calc
    pairings (dimensionOfEvent e) = bulkCount B e := by
      exact hbulk.symm
    _ = boundaryCount B e := by
      exact closure B e
    _ = orderings (dimensionOfEvent e) := by
      exact hboundary

/-- Low-dimensional barrier fact restated at the draft-facing alias. -/
theorem holographicOperator_D3 :
    holographicOperator 3 = SignedCount.ofNat 1 := by
  exact barrier_D3

/-- Stability at dimension 2 restated at the draft-facing alias. -/
theorem holographicOperator_D2_stable :
    holographicOperator 2 = SignedCount.zero := by
  exact stable_D2

/-- Stability at dimension 4 restated at the draft-facing alias. -/
theorem holographicOperator_D4_stable :
    holographicOperator 4 = SignedCount.zero := by
  exact stable_D4

end CoherenceCalculus
