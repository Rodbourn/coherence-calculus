import CoherenceCalculus.PartIV.ClosureCurrentContinuumFormCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumStateObjectCore

One underlying selected state object on the detached selected cut.

The current analytic lane already fixes one common first-order autonomous form
up to differential language. This file isolates the underlying object carried by
that form.

The point is not to add new dynamics. The point is to say plainly that the
current law is already about one concrete state object on the explicit
four-coordinate carrier `State`, and that the familiar public quantities are
derived readouts of that one object:

* selected projection,
* selected generator,
* quadratic density,
* scalar residual,
* common zero set.

So the present unification target is not "one scalar." It is one underlying
state object with multiple derived faces.
-/

namespace ClosureCurrent

/-- One selected state object on the concrete four-coordinate carrier `State`.

The data record one visible projection, one generator, one quadratic density,
one scalar residual, and one zero set. The equations certify that the density
and residual are read directly from the same generator, so these are not
independent primitives. -/
structure SelectedStateObject where
  project : State → State
  generator : State → State
  density : State → Nat
  residual : State → SignedCount
  solution : State → Prop
  project_zero : project State.zero = State.zero
  generator_visible : ∀ x : State, project (generator x) = generator x
  density_eq : ∀ x : State, density x = State.pair x (generator x)
  residual_eq : ∀ x : State, residual x = SignedCount.ofNat (density x)
  solution_eq : ∀ x : State, solution x ↔ residual x = SignedCount.zero

/-- The canonical selected state object already carried by the detached
selected cut. -/
def LocalEventFourStateLaw.selectedStateObject
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedStateObject where
  project := data.selectedFieldLaw.project
  generator := data.selectedFieldLaw.operator
  density := data.selectedQuadraticDensity
  residual := data.selectedFieldLaw.residual
  solution := data.selectedFieldEquation
  project_zero := data.selectedFieldLaw.project_zero
  generator_visible := data.selectedFieldLaw.operator_visible
  density_eq := by
    intro x
    rfl
  residual_eq := by
    have hdensity :
        SelectedScalarDensitySurface data := data.selectedScalarDensitySurface
    intro x
    exact hdensity.2.1 x
  solution_eq := by
    intro x
    rfl

/-- Manuscript-facing theorem surface saying that the detached selected cut
already carries one underlying selected state object, and that every current
flagship readout agrees with that same object. -/
def SelectedStateObjectSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  Nonempty SelectedStateObject ∧
    (∀ x : State,
      data.selectedStateObject.project x = data.selectedFieldLaw.project x) ∧
    (∀ x : State,
      data.selectedStateObject.generator x = data.selectedFieldLaw.operator x) ∧
    (∀ x : State,
      data.selectedStateObject.density x = data.selectedQuadraticDensity x) ∧
    (∀ x : State,
      data.selectedStateObject.residual x = data.selectedFieldLaw.residual x) ∧
    (∀ x : State,
      data.selectedStateObject.residual x =
        data.selectedAutonomousScalarLaw.residual x) ∧
    (∀ x : State,
      data.selectedStateObject.solution x ↔ data.selectedFieldEquation x) ∧
    (∀ x : State,
      data.selectedStateObject.solution x ↔
        data.scalarPDERealization.solution x) ∧
    (∀ x : State,
      data.selectedStateObject.solution x ↔
        data.scalarActionRealization.stationary x) ∧
    (∀ x : State,
      data.selectedStateObject.solution x ↔
        data.selectedEvolutionLaw.solution x) ∧
    (∀ realization : CompositeFlagshipRealization data,
      ∀ x : State,
        realization.flagship.velocity x = data.selectedStateObject.generator x ∧
        realization.flagship.density x = data.selectedStateObject.density x ∧
        realization.flagship.residual x = data.selectedStateObject.residual x ∧
        (realization.flagship.solution x ↔ data.selectedStateObject.solution x))

/-- The detached selected cut already carries one underlying selected state
object on the explicit carrier `State`. The generator, density, residual, and
solution set are all read from that same object, and any later stronger
flagship realization already agrees with it on those public surfaces. -/
theorem LocalEventFourStateLaw.selectedStateObjectSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedStateObjectSurface data := by
  have haut :
      SelectedAutonomousScalarLawSurface data := data.selectedAutonomousScalarLawSurface
  obtain
    ⟨_hforced, _hflow, _hgenerator, _hdensity, _hdensityReal, _hdensityGoal,
      hresidual, _hresidualDensity, hsolutionEq, hpde, haction, hevolution⟩ :=
    haut
  refine ⟨⟨data.selectedStateObject⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    rfl
  · intro x
    rfl
  · intro x
    rfl
  · intro x
    calc
      data.selectedStateObject.residual x = data.selectedFieldLaw.residual x := by
        rfl
      _ = data.selectedAutonomousScalarLaw.residual x := by
        symm
        exact hresidual x
  · intro x
    rfl
  · intro x
    exact (hsolutionEq x).symm.trans (hpde x)
  · intro x
    exact (hsolutionEq x).symm.trans (haction x)
  · intro x
    exact (hsolutionEq x).symm.trans (hevolution x)
  · intro realization x
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact realization.flagship.velocity_iff_selectedGenerator x
    · calc
        realization.flagship.density x = data.selectedAutonomousScalarLaw.density x := by
          exact realization.flagship.density_iff_selectedDensity x
        _ = data.selectedStateObject.density x := by
          rfl
    · calc
        realization.flagship.residual x = data.selectedAutonomousScalarLaw.residual x := by
          exact realization.flagship.residual_iff_selectedResidual x
        _ = data.selectedStateObject.residual x := by
          calc
            data.selectedAutonomousScalarLaw.residual x = data.selectedFieldLaw.residual x := by
              exact hresidual x
            _ = data.selectedStateObject.residual x := by
              rfl
    · exact realization.flagship.exact_selected_solution x

end ClosureCurrent

end CoherenceCalculus
