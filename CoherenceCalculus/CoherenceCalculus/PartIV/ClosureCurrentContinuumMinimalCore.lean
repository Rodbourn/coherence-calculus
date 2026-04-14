import CoherenceCalculus.PartIV.ClosureCurrentContinuumQuadraticCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumMinimalCore

Minimality and symmetry of the detached quadratic continuum representative.

`ClosureCurrentContinuumQuadraticCore` identifies the forced four-state
continuum representative as the operator of the selected admissible quadratic
form. The compiler surface already proves more than admissibility, however:

* the selected quadratic form is positive semidefinite;
* it is equivariant for the selected finite symmetry datum;
* it is minimal among positive semidefinite competitors;
* hence it is minimal in particular among positive semidefinite competitors
  that respect the same selected symmetry.

This file records that stronger canonicality surface without introducing any
analytic structure beyond the rebuilt compiler interfaces.
-/

namespace ClosureCurrent

/-- Minimal quadratic continuum representative forced by the no-stage detached
four-state law. The selected quadratic form is recorded together with its
selected symmetry datum and the minimality/equivariance properties already
carried by the compiler derivation step. -/
structure MinimalQuadraticRepresentative (Index Time Carrier Law : Type)
    extends QuadraticRepresentative Index Time Carrier Law where
  symmetry : Compiler.FinGroup
  representation : Compiler.UnitaryRep symmetry
  stateForm_equivariant :
    Compiler.QuadForm.IsGEquivariant' symmetry representation stateForm
  stateForm_minimal_equivariant :
    ∀ Q' : Compiler.QuadForm,
      Compiler.QuadForm.IsGEquivariant' symmetry representation Q' →
      Compiler.QuadForm.IsPSD Q' →
      Q' ≤ stateForm →
      Q'.op = stateForm.op

/-- Surface theorem for the minimal quadratic continuum representative. -/
theorem MinimalQuadraticRepresentative.surface
    {Index Time Carrier Law : Type}
    (data : MinimalQuadraticRepresentative Index Time Carrier Law) :
    Compiler.Admissible data.stateForm ∧
      Compiler.QuadForm.IsPSD data.stateForm ∧
      Compiler.QuadForm.IsGEquivariant' data.symmetry data.representation data.stateForm ∧
      (∀ Q' : Compiler.QuadForm,
        Compiler.QuadForm.IsPSD Q' →
        Q' ≤ data.stateForm →
        Q'.op = data.stateForm.op) ∧
      (∀ Q' : Compiler.QuadForm,
        Compiler.QuadForm.IsGEquivariant' data.symmetry data.representation Q' →
        Compiler.QuadForm.IsPSD Q' →
        Q' ≤ data.stateForm →
        Q'.op = data.stateForm.op) ∧
      data.stateForm = selected_observed_law data.bridge.selectedBridge.observer.selection ∧
      (∀ x : State,
        data.stateForm.op x = data.bridge.generator.toFun x) := by
  exact
    ⟨data.stateForm_admissible,
      data.stateForm_admissible.psd,
      data.stateForm_equivariant,
      data.stateForm_admissible.minimal,
      data.stateForm_minimal_equivariant,
      data.stateForm_isSelectedLaw,
      data.stateOperator_isGenerator⟩

/-- The no-stage detached four-state law already determines its minimal
quadratic continuum representative. -/
def LocalEventFourStateLaw.toMinimalQuadraticRepresentative
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    MinimalQuadraticRepresentative Index Time Carrier Law where
  toQuadraticRepresentative := data.toQuadraticRepresentative
  symmetry := data.framed.object.bridge.selectedBridge.observer.selection.symmetry
  representation :=
    data.framed.object.bridge.selectedBridge.observer.selection.representation
  stateForm_equivariant := by
    let selection := data.framed.object.bridge.selectedBridge.observer.selection
    simpa [LocalEventFourStateLaw.toQuadraticRepresentative, selected_observed_law,
      Compiler.stepDefect]
      using
        selection.derivation_equivariant
  stateForm_minimal_equivariant := by
    intro Q' hQ'eq hQ'psd hQ'le
    let selection := data.framed.object.bridge.selectedBridge.observer.selection
    exact
      Compiler.symmetry_reduction
        selection.symmetry
        selection.representation
        data.toQuadraticRepresentative.stateForm
        data.toQuadraticRepresentative.stateForm_admissible
        (by
          simpa [LocalEventFourStateLaw.toQuadraticRepresentative, selected_observed_law,
            Compiler.stepDefect]
            using
              selection.derivation_equivariant)
        Q' hQ'eq hQ'psd hQ'le

/-- The forced no-stage continuum representative is already canonical in the
compiler sense: its selected quadratic form is PSD, symmetry-compatible, and
minimal among positive semidefinite competitors, hence also among the
equivariant competitors in the selected symmetry class. -/
theorem LocalEventFourStateLaw.minimalQuadraticRepresentativeSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    Compiler.Admissible data.toMinimalQuadraticRepresentative.stateForm ∧
      Compiler.QuadForm.IsPSD data.toMinimalQuadraticRepresentative.stateForm ∧
      Compiler.QuadForm.IsGEquivariant'
        data.toMinimalQuadraticRepresentative.symmetry
        data.toMinimalQuadraticRepresentative.representation
        data.toMinimalQuadraticRepresentative.stateForm ∧
      (∀ Q' : Compiler.QuadForm,
        Compiler.QuadForm.IsPSD Q' →
        Q' ≤ data.toMinimalQuadraticRepresentative.stateForm →
        Q'.op = data.toMinimalQuadraticRepresentative.stateForm.op) ∧
      (∀ Q' : Compiler.QuadForm,
        Compiler.QuadForm.IsGEquivariant'
            data.toMinimalQuadraticRepresentative.symmetry
            data.toMinimalQuadraticRepresentative.representation
            Q' →
        Compiler.QuadForm.IsPSD Q' →
        Q' ≤ data.toMinimalQuadraticRepresentative.stateForm →
        Q'.op = data.toMinimalQuadraticRepresentative.stateForm.op) ∧
      data.toMinimalQuadraticRepresentative.stateForm =
        selected_observed_law
          data.framed.object.bridge.selectedBridge.observer.selection ∧
      (∀ x : State,
        data.toMinimalQuadraticRepresentative.stateForm.op x =
          data.framed.object.bridge.generator.toFun x) := by
  exact data.toMinimalQuadraticRepresentative.surface

end ClosureCurrent

end CoherenceCalculus
