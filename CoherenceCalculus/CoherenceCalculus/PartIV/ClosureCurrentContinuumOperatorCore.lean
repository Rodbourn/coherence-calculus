import CoherenceCalculus.PartIV.ClosureCurrentContinuumRepresentativeCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumOperatorCore

Operator-level strengthening of the detached continuum representative.

`ClosureCurrentContinuumRepresentativeCore` identified the first canonical
continuum representative class of the no-stage four-state law as:

* the matched selected generator on `State`,
* its balanced hidden quotient on `BalancedCoordinates`,
* the selected observed readout.

The next honest strengthening is algebraic rather than analytic. This file
records that the same representative is already additive:

* the forced four-state continuum law is an additive endomap of `State`;
* the forced balanced hidden quotient is an additive endomap of the reduced
  balanced carrier;
* no PDE, variational principle, or extra carrier structure is introduced.
-/

namespace ClosureCurrent

/-- Additive zero-preserving endomaps of the reduced balanced hidden carrier. -/
structure CoordinateMap where
  toFun : BalancedCoordinates → BalancedCoordinates
  map_add :
    ∀ x y : BalancedCoordinates,
      toFun (BalancedCoordinates.add x y) =
        BalancedCoordinates.add (toFun x) (toFun y)
  map_zero :
    toFun BalancedCoordinates.zero = BalancedCoordinates.zero

namespace CoordinateMap

instance : CoeFun CoordinateMap (fun _ => BalancedCoordinates → BalancedCoordinates) := ⟨
  CoordinateMap.toFun⟩

/-- Any additive ambient state operator induces an additive reduced balanced
operator by reconstruction and projection. -/
def ofAddMap (A : AddMap) : CoordinateMap where
  toFun := BalancedCoordinates.transport A.toFun
  map_add := BalancedCoordinates.transport_add A
  map_zero := BalancedCoordinates.transport_zero A

end CoordinateMap

/-- Operator-level continuum representative forced by the no-stage detached
four-state law. The four-state law is now recorded as an additive operator on
`State`, and the balanced hidden quotient is recorded as an additive operator
on `BalancedCoordinates`. -/
structure OperatorRepresentative (Index Time Carrier Law : Type) where
  bridge : BridgeData Index Time Carrier Law
  stateLimitClass : ContinuumLimitClass (State → State)
  hiddenLimitClass : ContinuumLimitClass (BalancedCoordinates → BalancedCoordinates)
  stateOperator : AddMap
  hiddenOperator : CoordinateMap
  observedReadout : BalancedCoordinates → State
  stateOperator_forced : ForcedContinuumLaw stateLimitClass stateOperator.toFun
  hiddenOperator_forced : ForcedContinuumLaw hiddenLimitClass hiddenOperator.toFun
  stateOperator_isSelectedOperator :
    ∀ x : State,
      stateOperator x = selectedOperator bridge x
  stateOperator_isGenerator :
    ∀ x : State,
      stateOperator x = bridge.generator.toFun x
  hiddenOperator_isTransport :
    ∀ x : BalancedCoordinates,
      hiddenOperator x = BalancedCoordinates.transport stateOperator.toFun x
  hiddenOperator_isQuotient :
    ∀ x : BalancedCoordinates,
      hiddenOperator x =
        BalancedCoordinates.projectState (stateOperator x.toState)
  observedReadout_isSelectedProjection :
    ∀ x : BalancedCoordinates,
      observedReadout x = selectedProjection bridge x.toState

/-- Surface theorem for the operator-level continuum representative. -/
theorem OperatorRepresentative.surface
    {Index Time Carrier Law : Type}
    (data : OperatorRepresentative Index Time Carrier Law) :
    ForcedContinuumLaw data.stateLimitClass data.stateOperator.toFun ∧
      ForcedContinuumLaw data.hiddenLimitClass data.hiddenOperator.toFun ∧
      (∀ x y : State,
        data.stateOperator (State.add x y) =
          State.add (data.stateOperator x) (data.stateOperator y)) ∧
      data.stateOperator State.zero = State.zero ∧
      (∀ x y : BalancedCoordinates,
        data.hiddenOperator (BalancedCoordinates.add x y) =
          BalancedCoordinates.add (data.hiddenOperator x) (data.hiddenOperator y)) ∧
      data.hiddenOperator BalancedCoordinates.zero = BalancedCoordinates.zero ∧
      (∀ x : State,
        data.stateOperator x = selectedOperator data.bridge x) ∧
      (∀ x : State,
        data.stateOperator x = data.bridge.generator.toFun x) ∧
      (∀ x : BalancedCoordinates,
        data.hiddenOperator x =
          BalancedCoordinates.transport data.stateOperator.toFun x) ∧
      (∀ x : BalancedCoordinates,
        data.hiddenOperator x =
          BalancedCoordinates.projectState (data.stateOperator x.toState)) ∧
      (∀ x : BalancedCoordinates,
        data.observedReadout x =
          selectedProjection data.bridge x.toState) := by
  exact
    ⟨data.stateOperator_forced,
      data.hiddenOperator_forced,
      data.stateOperator.map_add,
      data.stateOperator.map_zero,
      data.hiddenOperator.map_add,
      data.hiddenOperator.map_zero,
      data.stateOperator_isSelectedOperator,
      data.stateOperator_isGenerator,
      data.hiddenOperator_isTransport,
      data.hiddenOperator_isQuotient,
      data.observedReadout_isSelectedProjection⟩

/-- The no-stage detached four-state law already determines its canonical
operator-level continuum representative. -/
def LocalEventFourStateLaw.toOperatorRepresentative
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    OperatorRepresentative Index Time Carrier Law where
  bridge := data.framed.object.bridge
  stateLimitClass := data.stateDynamics.limitClass
  hiddenLimitClass :=
    data.toLocalEventStateBridge.reducedDynamics.hiddenLimitClass
  stateOperator := selectedOperator data.framed.object.bridge
  hiddenOperator := CoordinateMap.ofAddMap (selectedOperator data.framed.object.bridge)
  observedReadout := fun x => selectedProjection data.framed.object.bridge x.toState
  stateOperator_forced := by
    have hstate :
        data.stateDynamics.continuumLaw =
          (selectedOperator data.framed.object.bridge).toFun := by
      funext x
      change data.framed.object.bridge.generator.toFun x = selectedOperator data.framed.object.bridge x
      exact generator_eq_selectedOperator data.framed.object.bridge x
    simpa [hstate] using data.stateContinuumLaw_forced
  hiddenOperator_forced := by
    have hfun :
        (CoordinateMap.ofAddMap (selectedOperator data.framed.object.bridge)).toFun =
          data.toLocalEventStateBridge.reducedDynamics.hiddenContinuumLaw := by
      funext x
      unfold CoordinateMap.ofAddMap
      dsimp [BalancedCoordinates.transport, selectedOperator]
      change
        BalancedCoordinates.projectState
            (selectedOperator data.framed.object.bridge x.toState) =
          BalancedCoordinates.projectState
            (data.framed.object.bridge.generator.toFun x.toState)
      rw [(generator_eq_selectedOperator data.framed.object.bridge x.toState).symm]
    simpa [hfun] using data.reducedContinuumLaw_forced
  stateOperator_isSelectedOperator := by
    intro x
    rfl
  stateOperator_isGenerator := by
    intro x
    simpa [selectedOperator] using
      (generator_eq_selectedOperator data.framed.object.bridge x).symm
  hiddenOperator_isTransport := by
    intro x
    rfl
  hiddenOperator_isQuotient := by
    intro x
    rfl
  observedReadout_isSelectedProjection := by
    intro x
    rfl

/-- The current forced continuum representative is already operator-level:
the no-stage four-state law determines an additive four-state operator, its
additive balanced hidden quotient, and the selected observed readout from that
same hidden carrier. -/
theorem LocalEventFourStateLaw.operatorRepresentativeSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ForcedContinuumLaw
      data.toOperatorRepresentative.stateLimitClass
      data.toOperatorRepresentative.stateOperator.toFun ∧
      ForcedContinuumLaw
        data.toOperatorRepresentative.hiddenLimitClass
        data.toOperatorRepresentative.hiddenOperator.toFun ∧
      (∀ x y : State,
        data.toOperatorRepresentative.stateOperator (State.add x y) =
          State.add
            (data.toOperatorRepresentative.stateOperator x)
            (data.toOperatorRepresentative.stateOperator y)) ∧
      data.toOperatorRepresentative.stateOperator State.zero = State.zero ∧
      (∀ x y : BalancedCoordinates,
        data.toOperatorRepresentative.hiddenOperator (BalancedCoordinates.add x y) =
          BalancedCoordinates.add
            (data.toOperatorRepresentative.hiddenOperator x)
            (data.toOperatorRepresentative.hiddenOperator y)) ∧
      data.toOperatorRepresentative.hiddenOperator BalancedCoordinates.zero =
        BalancedCoordinates.zero ∧
      (∀ x : State,
        data.toOperatorRepresentative.stateOperator x =
          selectedOperator data.framed.object.bridge x) ∧
      (∀ x : State,
        data.toOperatorRepresentative.stateOperator x =
          data.framed.object.bridge.generator.toFun x) ∧
      (∀ x : BalancedCoordinates,
        data.toOperatorRepresentative.hiddenOperator x =
          BalancedCoordinates.transport
            data.toOperatorRepresentative.stateOperator.toFun x) ∧
      (∀ x : BalancedCoordinates,
        data.toOperatorRepresentative.hiddenOperator x =
          BalancedCoordinates.projectState
            (data.toOperatorRepresentative.stateOperator x.toState)) ∧
      (∀ x : BalancedCoordinates,
        data.toOperatorRepresentative.observedReadout x =
          selectedProjection data.framed.object.bridge x.toState) := by
  exact data.toOperatorRepresentative.surface

end ClosureCurrent

end CoherenceCalculus
