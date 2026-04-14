import CoherenceCalculus.Foundation.CountableChoiceCore

/-!
# Foundation.PartialChoiceCore

Clean injectivity and equality facts for finite partial choices.

The more ambitious reconstruction/extensionality statements are left out of the
active root until they can be rebuilt without `propext`.
-/

namespace CoherenceCalculus

/-- Adjoining a last coordinate is injective in the parent partial choice. -/
theorem partialChoice_snoc_injective_left
    (F : ExplicitFiniteFamily) {n : Nat}
    {p q : PartialChoice F n} {x y : F.Carrier n}
    (h : PartialChoice.snoc p x = PartialChoice.snoc q y) :
    p = q := by
  cases h
  rfl

/-- Adjoining a last coordinate is injective in the last coordinate. -/
theorem partialChoice_snoc_injective_right
    (F : ExplicitFiniteFamily) {n : Nat}
    {p q : PartialChoice F n} {x y : F.Carrier n}
    (h : PartialChoice.snoc p x = PartialChoice.snoc q y) :
    x = y := by
  cases h
  rfl

/-- Equality of snoc-extended partial choices is exactly equality of the parent
choices together with equality of the adjoined coordinates. -/
theorem partialChoice_snoc_eq_iff
    (F : ExplicitFiniteFamily) {n : Nat}
    {p q : PartialChoice F n} {x y : F.Carrier n} :
    PartialChoice.snoc p x = PartialChoice.snoc q y ↔ p = q ∧ x = y := by
  constructor
  · intro h
    exact ⟨partialChoice_snoc_injective_left F h, partialChoice_snoc_injective_right F h⟩
  · intro h
    rcases h with ⟨hp, hx⟩
    cases hp
    cases hx
    rfl

end CoherenceCalculus
