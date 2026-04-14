import CoherenceCalculus.Foundation.HorizonCore

/-!
# Foundation.FieldInducedHorizonCore

Abstract field-cut interface for horizon projections.

This module does not attempt to rebuild spectral theory. Instead it records the
minimal projection-family interface needed to state the manuscript's
field-induced horizon language on the active foundation spine.
-/

namespace CoherenceCalculus

/-- A family of field-selected horizon projections indexed by abstract spectral
windows. The only required structure is the nesting relation between windows
and the corresponding projection nesting laws. -/
structure FieldCutFamily (Field Window : Type) where
  windowLE : Window → Window → Prop
  projection : Field → Window → Projection
  nested : ∀ φ S T, windowLE S T → ∀ x,
    (projection φ S).toFun ((projection φ T).toFun x) = (projection φ S).toFun x
  nested_ge : ∀ φ S T, windowLE S T → ∀ x,
    (projection φ T).toFun ((projection φ S).toFun x) = (projection φ S).toFun x

/-- A field-induced horizon is the projection selected by a field and a window
in a field-cut family. -/
def fieldInducedHorizon
    {Field Window : Type} (cuts : FieldCutFamily Field Window) (φ : Field) (S : Window) :
    Projection :=
  cuts.projection φ S

/-- Nested windows produce nested field-induced horizon projections. -/
theorem fieldInducedHorizon_nesting
    {Field Window : Type} (cuts : FieldCutFamily Field Window) (φ : Field)
    {S T : Window} (hST : cuts.windowLE S T) :
    (∀ x,
      (fieldInducedHorizon cuts φ S).toFun ((fieldInducedHorizon cuts φ T).toFun x) =
        (fieldInducedHorizon cuts φ S).toFun x) ∧
    (∀ x,
      (fieldInducedHorizon cuts φ T).toFun ((fieldInducedHorizon cuts φ S).toFun x) =
        (fieldInducedHorizon cuts φ S).toFun x) := by
  exact ⟨cuts.nested φ S T hST, cuts.nested_ge φ S T hST⟩

/-- Observable compression adapted to an arbitrary projection cut, including a
field-induced horizon. -/
def fieldAdaptedObservable (P : Projection) (A : State → State) : State → State :=
  fun x => P.toFun (A (P.toFun x))

end CoherenceCalculus
