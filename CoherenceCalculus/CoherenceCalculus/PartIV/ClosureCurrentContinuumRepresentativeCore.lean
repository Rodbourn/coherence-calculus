import CoherenceCalculus.PartIV.ClosureCurrentContinuumCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumRepresentativeCore

First canonical continuum representative class of the detached four-state law.

`ClosureCurrentContinuumCore` forces the detached four-state continuum law and
its balanced hidden quotient from the no-stage local-event four-state law. The
next honest question is not yet for a PDE, a Lagrangian, or a carrier-level
analytic model. It is simply:

* what continuum representative class is already forced at the current formal
  surface?

This file records the clean answer. The forced continuum representative is
already first-order:

* the four-state continuum law is the matched selected generator itself;
* the reduced hidden continuum law is the balanced transport quotient of that
  same generator;
* the observed law is the selected projection of the same balanced carrier.

Nothing here claims more than the detached lane currently proves. The point is
to package the first canonical representative class before any later analytic
or variational realization is attempted.
-/

namespace ClosureCurrent

/-- First canonical continuum representative class forced by the no-stage
detached four-state law. The representative is still abstract in the sense that
it is an endomorphism of the explicit four-state carrier, not yet an analytic
PDE or variational model, but it is already rigid enough to identify one
first-order generator, its balanced hidden quotient, and its selected observed
readout. -/
structure ContinuumRepresentative (Index Time Carrier Law : Type) where
  bridge : BridgeData Index Time Carrier Law
  stateLimitClass : ContinuumLimitClass (State → State)
  hiddenLimitClass : ContinuumLimitClass (BalancedCoordinates → BalancedCoordinates)
  stateLaw : State → State
  hiddenLaw : BalancedCoordinates → BalancedCoordinates
  observedReadout : BalancedCoordinates → State
  stateLaw_forced : ForcedContinuumLaw stateLimitClass stateLaw
  hiddenLaw_forced : ForcedContinuumLaw hiddenLimitClass hiddenLaw
  stateLaw_isGenerator :
    ∀ x : State,
      stateLaw x = bridge.generator.toFun x
  hiddenLaw_isTransport :
    ∀ x : BalancedCoordinates,
      hiddenLaw x = BalancedCoordinates.transport bridge.generator.toFun x
  hiddenLaw_isQuotient :
    ∀ x : BalancedCoordinates,
      hiddenLaw x = BalancedCoordinates.projectState (stateLaw x.toState)
  observedReadout_isSelectedProjection :
    ∀ x : BalancedCoordinates,
      observedReadout x = selectedProjection bridge x.toState

/-- Surface theorem for the first canonical continuum representative class. -/
theorem ContinuumRepresentative.surface
    {Index Time Carrier Law : Type}
    (data : ContinuumRepresentative Index Time Carrier Law) :
    ForcedContinuumLaw data.stateLimitClass data.stateLaw ∧
      ForcedContinuumLaw data.hiddenLimitClass data.hiddenLaw ∧
      (∀ x : State,
        data.stateLaw x = data.bridge.generator.toFun x) ∧
      (∀ x : BalancedCoordinates,
        data.hiddenLaw x =
          BalancedCoordinates.transport data.bridge.generator.toFun x) ∧
      (∀ x : BalancedCoordinates,
        data.hiddenLaw x =
          BalancedCoordinates.projectState (data.stateLaw x.toState)) ∧
      (∀ x : BalancedCoordinates,
        data.observedReadout x =
          selectedProjection data.bridge x.toState) := by
  exact
    ⟨data.stateLaw_forced,
      data.hiddenLaw_forced,
      data.stateLaw_isGenerator,
      data.hiddenLaw_isTransport,
      data.hiddenLaw_isQuotient,
      data.observedReadout_isSelectedProjection⟩

/-- The no-stage detached four-state law already determines its first canonical
continuum representative class. -/
def LocalEventFourStateLaw.toContinuumRepresentative
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ContinuumRepresentative Index Time Carrier Law where
  bridge := data.framed.object.bridge
  stateLimitClass := data.stateDynamics.limitClass
  hiddenLimitClass :=
    data.toLocalEventStateBridge.reducedDynamics.hiddenLimitClass
  stateLaw := data.framed.object.bridge.generator.toFun
  hiddenLaw :=
    BalancedCoordinates.transport data.framed.object.bridge.generator.toFun
  observedReadout :=
    fun x => selectedProjection data.framed.object.bridge x.toState
  stateLaw_forced := by
    simpa [LocalEventFourStateLaw.stateDynamics,
      LocalEventStateBridge.stateDynamics,
      StateDynamics.continuumLaw]
      using data.stateContinuumLaw_forced
  hiddenLaw_forced := by
    simpa [LocalEventStateBridge.reducedDynamics,
      AnchoredCurrentObject.reducedObservedSystem,
      ReducedObservedSystem.toDynamics,
      AnchoredCurrentObject.coordinateStep,
      ReducedObservedDynamics.hiddenContinuumLaw]
      using data.reducedContinuumLaw_forced
  stateLaw_isGenerator := by
    intro x
    rfl
  hiddenLaw_isTransport := by
    intro x
    rfl
  hiddenLaw_isQuotient := by
    intro x
    rfl
  observedReadout_isSelectedProjection := by
    intro x
    rfl

/-- The current rigorous representative search therefore already lands on one
forced first-order continuum representative: the matched selected generator on
the explicit four-state carrier, with the balanced hidden law and selected
observed law read as its quotient and projection. -/
theorem LocalEventFourStateLaw.representativeSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ForcedContinuumLaw
      data.toContinuumRepresentative.stateLimitClass
      data.toContinuumRepresentative.stateLaw ∧
      ForcedContinuumLaw
        data.toContinuumRepresentative.hiddenLimitClass
        data.toContinuumRepresentative.hiddenLaw ∧
      (∀ x : State,
        data.toContinuumRepresentative.stateLaw x =
          data.framed.object.bridge.generator.toFun x) ∧
      (∀ x : BalancedCoordinates,
        data.toContinuumRepresentative.hiddenLaw x =
          BalancedCoordinates.transport
            data.framed.object.bridge.generator.toFun x) ∧
      (∀ x : BalancedCoordinates,
        data.toContinuumRepresentative.hiddenLaw x =
          BalancedCoordinates.projectState
            (data.toContinuumRepresentative.stateLaw x.toState)) ∧
      (∀ x : BalancedCoordinates,
        data.toContinuumRepresentative.observedReadout x =
          selectedProjection data.framed.object.bridge x.toState) := by
  exact data.toContinuumRepresentative.surface

end ClosureCurrent

end CoherenceCalculus
