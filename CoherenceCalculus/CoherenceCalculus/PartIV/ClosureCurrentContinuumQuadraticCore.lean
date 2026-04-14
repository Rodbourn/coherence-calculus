import CoherenceCalculus.PartIV.ClosureCurrentContinuumOperatorCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumQuadraticCore

Quadratic-form strengthening of the detached continuum representative.

`ClosureCurrentContinuumOperatorCore` shows that the no-stage four-state law
already determines an additive operator on the explicit four-state carrier and
an additive operator on its balanced hidden quotient.

The selected four-state operator is not merely additive, however. By
construction it is the operator of the selected compiler quadratic form. This
file records that stronger, still-honest conclusion:

* the canonical four-state representative already comes from an admissible
  quadratic form on `State`;
* the hidden operator is still its balanced quotient;
* this is the closest current formal surface gets to a variational
  representative without claiming a full Lagrangian or Hamiltonian theory.
-/

namespace ClosureCurrent

/-- Quadratic-form continuum representative forced by the no-stage detached
four-state law. The four-state operator is recorded as the operator of an
admissible compiler quadratic form on `State`, while the balanced hidden
quotient and selected observed readout remain unchanged. -/
structure QuadraticRepresentative (Index Time Carrier Law : Type) where
  bridge : BridgeData Index Time Carrier Law
  stateLimitClass : ContinuumLimitClass (State → State)
  hiddenLimitClass : ContinuumLimitClass (BalancedCoordinates → BalancedCoordinates)
  stateForm : Compiler.QuadForm
  hiddenOperator : CoordinateMap
  observedReadout : BalancedCoordinates → State
  stateForm_admissible : Compiler.Admissible stateForm
  stateOperator_forced : ForcedContinuumLaw stateLimitClass stateForm.op.toFun
  hiddenOperator_forced : ForcedContinuumLaw hiddenLimitClass hiddenOperator.toFun
  stateForm_isSelectedLaw :
    stateForm = selected_observed_law bridge.selectedBridge.observer.selection
  stateOperator_isGenerator :
    ∀ x : State,
      stateForm.op x = bridge.generator.toFun x
  hiddenOperator_isQuotient :
    ∀ x : BalancedCoordinates,
      hiddenOperator x =
        BalancedCoordinates.projectState (stateForm.op x.toState)
  observedReadout_isSelectedProjection :
    ∀ x : BalancedCoordinates,
      observedReadout x = selectedProjection bridge x.toState

/-- Surface theorem for the quadratic-form continuum representative. -/
theorem QuadraticRepresentative.surface
    {Index Time Carrier Law : Type}
    (data : QuadraticRepresentative Index Time Carrier Law) :
    Compiler.Admissible data.stateForm ∧
      ForcedContinuumLaw data.stateLimitClass data.stateForm.op.toFun ∧
      ForcedContinuumLaw data.hiddenLimitClass data.hiddenOperator.toFun ∧
      data.stateForm = selected_observed_law data.bridge.selectedBridge.observer.selection ∧
      (∀ x : State,
        data.stateForm.op x = data.bridge.generator.toFun x) ∧
      (∀ x : BalancedCoordinates,
        data.hiddenOperator x =
          BalancedCoordinates.projectState (data.stateForm.op x.toState)) ∧
      (∀ x : BalancedCoordinates,
        data.observedReadout x =
          selectedProjection data.bridge x.toState) := by
  exact
    ⟨data.stateForm_admissible,
      data.stateOperator_forced,
      data.hiddenOperator_forced,
      data.stateForm_isSelectedLaw,
      data.stateOperator_isGenerator,
      data.hiddenOperator_isQuotient,
      data.observedReadout_isSelectedProjection⟩

/-- The no-stage detached four-state law already determines its canonical
quadratic-form continuum representative. -/
def LocalEventFourStateLaw.toQuadraticRepresentative
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    QuadraticRepresentative Index Time Carrier Law where
  bridge := data.framed.object.bridge
  stateLimitClass := data.toOperatorRepresentative.stateLimitClass
  hiddenLimitClass := data.toOperatorRepresentative.hiddenLimitClass
  stateForm := selected_observed_law data.framed.object.bridge.selectedBridge.observer.selection
  hiddenOperator := data.toOperatorRepresentative.hiddenOperator
  observedReadout := data.toOperatorRepresentative.observedReadout
  stateForm_admissible :=
    data.framed.object.bridge.selectedBridge.observer.selection.derivation.admissible
  stateOperator_forced := data.toOperatorRepresentative.stateOperator_forced
  hiddenOperator_forced := data.toOperatorRepresentative.hiddenOperator_forced
  stateForm_isSelectedLaw := rfl
  stateOperator_isGenerator := by
    intro x
    exact data.toOperatorRepresentative.stateOperator_isGenerator x
  hiddenOperator_isQuotient := by
    intro x
    exact data.toOperatorRepresentative.hiddenOperator_isQuotient x
  observedReadout_isSelectedProjection := by
    intro x
    exact data.toOperatorRepresentative.observedReadout_isSelectedProjection x

/-- The forced no-stage continuum representative is already quadratic-form
driven: the matched selected operator comes from the admissible selected
compiler quadratic form, and the balanced hidden law remains its quotient. -/
theorem LocalEventFourStateLaw.quadraticRepresentativeSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    Compiler.Admissible data.toQuadraticRepresentative.stateForm ∧
      ForcedContinuumLaw
        data.toQuadraticRepresentative.stateLimitClass
        data.toQuadraticRepresentative.stateForm.op.toFun ∧
      ForcedContinuumLaw
        data.toQuadraticRepresentative.hiddenLimitClass
        data.toQuadraticRepresentative.hiddenOperator.toFun ∧
      data.toQuadraticRepresentative.stateForm =
        selected_observed_law data.framed.object.bridge.selectedBridge.observer.selection ∧
      (∀ x : State,
        data.toQuadraticRepresentative.stateForm.op x =
          data.framed.object.bridge.generator.toFun x) ∧
      (∀ x : BalancedCoordinates,
        data.toQuadraticRepresentative.hiddenOperator x =
          BalancedCoordinates.projectState
            (data.toQuadraticRepresentative.stateForm.op x.toState)) ∧
      (∀ x : BalancedCoordinates,
        data.toQuadraticRepresentative.observedReadout x =
          selectedProjection data.framed.object.bridge x.toState) := by
  exact data.toQuadraticRepresentative.surface

end ClosureCurrent

end CoherenceCalculus
