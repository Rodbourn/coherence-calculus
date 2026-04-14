import CoherenceCalculus.Foundation.FiniteComplexCore

/-!
# Foundation.SolverInterfaceCore

Optional solver-layer interfaces above the rebuilt finite-complex core.

This module does not introduce a full adjoint/Hodge hierarchy. It records the
manuscript-facing solver vocabulary as explicit interface data on the active
additive spine:

- exactness
- Laplacian and Green interfaces
- homotopy identity as an explicit property
- holographic saturation relative to a boundary restriction map

Whenever a theorem here is proved, it is proved purely from the stated local
hypotheses on these interfaces.
-/

namespace CoherenceCalculus

/-- Exactness at the middle degree of the rebuilt two-step complex. -/
def complexExactness (C : finiteHilbertComplex) : Prop :=
  ∀ x : State, C.D1 x = State.zero → ∃ y : State, C.D0 y = x

/-- Laplacian assembled from explicit predecessor/successor differentials and
their chosen adjoints. -/
def hodgeLaplacian
    (dPrev dPrevAdj dNext dNextAdj : AddMap) : AddMap :=
  AddMap.add (AddMap.comp dPrev dPrevAdj) (AddMap.comp dNextAdj dNext)

/-- A Green operator is an explicit two-sided inverse for a chosen Laplacian
interface. -/
structure greenOperator (Δ : AddMap) where
  toAddMap : AddMap
  left_inv : ∀ x : State, toAddMap (Δ x) = x
  right_inv : ∀ x : State, Δ (toAddMap x) = x

/-- Named interface property expressing that the Laplacian commutes with the
differential. -/
def laplacian_intertwines_differential
    (D Δk ΔkSucc : AddMap) : Prop :=
  ∀ x : State, D (Δk x) = ΔkSucc (D x)

/-- Named interface property for the chain homotopy identity. -/
def homotopyIdentity
    (dPrev dNext kPrev kNext : AddMap) : Prop :=
  ∀ x : State, State.add (dPrev (kPrev x)) (kNext (dNext x)) = x

/-- Holographic saturation relative to a boundary restriction map. -/
def holographicSaturation (C : finiteHilbertComplex) (R : AddMap) : Prop :=
  ∀ x : State, R x = State.zero → ∃ y : State, C.D0 y = x

/-- Boundary compatibility and full saturation descend to the projected
subcomplex when the split intertwines with the differential. -/
theorem saturation_preserved
    (C : finiteHilbertComplex) (IP : IntertwiningProj C) (R : AddMap)
    (hcompat : isBoundaryCompatible R IP.P1)
    (hexact_forms : ∀ x : State, R (C.D0 x) = State.zero)
    (hsat : holographicSaturation C R) :
    (∀ x : State, R (C.D0 (IP.P0 x)) = State.zero) ∧
    (∀ x : State, R (IP.P1 x) = State.zero → ∃ y : State, C.D0 (IP.P0 y) = IP.P1 x) := by
  refine ⟨?_, ?_⟩
  · intro x
    calc
      R (C.D0 (IP.P0 x)) = R (IP.P1 (C.D0 x)) := by
          rw [IP.intertwine_0]
      _ = R (C.D0 x) := by
          exact hcompat (C.D0 x)
      _ = State.zero := by
          exact hexact_forms x
  · intro x hx
    have hx_full : R x = State.zero := by
      calc
        R x = R (IP.P1 x) := by
            symm
            exact hcompat x
        _ = State.zero := hx
    rcases hsat x hx_full with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    calc
      C.D0 (IP.P0 y) = IP.P1 (C.D0 y) := by
          symm
          exact IP.intertwine_0 y
      _ = IP.P1 x := by
          rw [hy]

end CoherenceCalculus
