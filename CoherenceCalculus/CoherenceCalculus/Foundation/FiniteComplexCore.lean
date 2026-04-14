import CoherenceCalculus.Foundation.ProjectionCalculusCore

/-!
# Foundation.FiniteComplexCore

Minimal finite-complex interface rebuilt on the active additive state space.

This module intentionally stays schematic. It records only the exact
finite-dimensional algebra needed for the manuscript's complex/intertwining
surface:

- a two-step finite complex
- projection intertwining across the differential
- vanishing of the projection defect under exact intertwining

No adjoint, Hodge, or Hilbert-space imports are introduced here.
-/

namespace CoherenceCalculus

/-- Minimal finite complex data on the rebuilt state space. -/
structure finiteHilbertComplex where
  D0 : AddMap
  D1 : AddMap
  nilpotent : ∀ x : State, D1 (D0 x) = State.zero

/-- The differential squares to zero on a finite complex. -/
theorem complex_nilpotency (C : finiteHilbertComplex) (x : State) :
    C.D1 (C.D0 x) = State.zero :=
  C.nilpotent x

/-- Compatibility of a projection split with the first differential of the
finite complex. -/
structure IntertwiningProj (C : finiteHilbertComplex) where
  P0 : Projection
  P1 : Projection
  intertwine_0 : ∀ x : State, P1 (C.D0 x) = C.D0 (P0 x)

/-- A projection is boundary-compatible for a restriction map when boundary data
is already determined by the projected component. -/
def isBoundaryCompatible (R : AddMap) (P : Projection) : Prop :=
  ∀ x : State, R (P x) = R x

/-- Projection defect across a candidate intertwining pair. -/
def projectionDefect (P₂ P₁ : Projection) (A : AddMap) : AddMap where
  toFun := fun x => State.sub (P₂ (A x)) (A (P₁ x))
  map_add := by
    intro x y
    rw [A.map_add, P₂.map_add, P₁.map_add, A.map_add]
    exact State.sub_add_distrib (P₂ (A x)) (P₂ (A y)) (A (P₁ x)) (A (P₁ y))
  map_zero := by
    rw [A.map_zero, P₂.map_zero, P₁.map_zero, A.map_zero]
    exact State.sub_self State.zero

/-- Exact intertwining is the vanishing of the projection defect. -/
theorem intertwining_preserves_complex
    (C : finiteHilbertComplex) (IP : IntertwiningProj C) (x : State) :
    IP.P1 (C.D0 x) = C.D0 (IP.P0 x) :=
  IP.intertwine_0 x

/-- Under exact intertwining, the projection defect vanishes. -/
theorem cohomology_splits (C : finiteHilbertComplex) (IP : IntertwiningProj C) (x : State) :
    projectionDefect IP.P1 IP.P0 C.D0 x = State.zero := by
  change State.sub (IP.P1 (C.D0 x)) (C.D0 (IP.P0 x)) = State.zero
  rw [IP.intertwine_0]
  exact State.sub_self (C.D0 (IP.P0 x))

/-- Exact intertwining passes to the complementary shadow components. -/
theorem complement_intertwines (C : finiteHilbertComplex) (IP : IntertwiningProj C) (x : State) :
    projectionShadow IP.P1 (C.D0 x) = C.D0 (projectionShadow IP.P0 x) := by
  unfold projectionShadow
  change State.add (C.D0 x) (State.negate (IP.P1 (C.D0 x))) =
    C.D0 (State.add x (State.negate (IP.P0 x)))
  rw [C.D0.map_add, AddMap.map_negate C.D0, IP.intertwine_0]

/-- The spurious projection defect disappears when the split intertwines with
the differential. -/
theorem spurious_vanishes_when_intertwining
    (C : finiteHilbertComplex) (IP : IntertwiningProj C) (x : State) :
    projectionDefect IP.P1 IP.P0 C.D0 x = State.zero :=
  cohomology_splits C IP x

/-- Restricting the input to the observable part preserves nilpotency. -/
theorem subcomplex_nilpotent (C : finiteHilbertComplex) (IP : IntertwiningProj C) (x : State) :
    C.D1 (C.D0 (IP.P0 x)) = State.zero :=
  C.nilpotent (IP.P0 x)

end CoherenceCalculus
