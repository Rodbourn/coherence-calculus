import CoherenceCalculus.PartIV.ClosureCurrentTrajectoryCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentCoordinateBridgeCore

One-way bridge from the detached local-event current object to the explicit
coordinate assembly.

`ClosureCurrentTrajectoryCore` shows that, once a coordinate assembly for
`ρ₃` is fixed, the detached future already factors through the selected bridge
and the initial reduced coordinate. The remaining live seam is therefore
smaller and more precise than the full assembled state field:

* one detached local-event current object;
* one signed readout of pair-current values;
* one genuine four-leg frame;
* one reduced transport law for the resulting concrete coordinate `ρ₃`.

This file packages exactly that smaller bridge. It remains detached from the
bedrock-certified spine. Its role is only to state cleanly what extra datum is
still needed to pass from the local pair-current/event object to the explicit
reduced selected-bridge dynamics.
-/

namespace ClosureCurrent

/-- Detached local-event current object together with the explicit microscopic
framing data needed to assemble a concrete four-state from the hidden pair
current. This isolates the non-dynamical part of the remaining microscopic
datum: one signed readout and one genuine four-leg frame. -/
structure FramedLocalEventObject (Index Time Carrier Law : Type) where
  object : LocalEventObject Index Time Carrier Law
  readout : SignedExchangeReadout object.currentCarrier
  frame : FourLegFrame object.Leg

/-- The framed local-event object already determines the explicit assembled
four-state. -/
def FramedLocalEventObject.currentState
    {Index Time Carrier Law : Type}
    (data : FramedLocalEventObject Index Time Carrier Law) :
    PairExchangeCurrent data.object.currentCarrier data.object.Leg → State :=
  assembledState data.readout data.frame

/-- The framed local-event object already determines the concrete reduced
hidden coordinate `ρ₃`. -/
def FramedLocalEventObject.currentCoordinates
    {Index Time Carrier Law : Type}
    (data : FramedLocalEventObject Index Time Carrier Law) :
    PairExchangeCurrent data.object.currentCarrier data.object.Leg →
      BalancedCoordinates :=
  assembledCoordinates data.readout data.frame

/-- The assembled four-state determined by the framing data is automatically
balanced. -/
theorem FramedLocalEventObject.currentState_balanced
    {Index Time Carrier Law : Type}
    (data : FramedLocalEventObject Index Time Carrier Law) :
    ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
      stateTotal (data.currentState current) = SignedCount.zero := by
  intro current
  exact assembledState_total_zero data.readout data.frame current

/-- Stronger local-event bridge to the explicit assembled state. This keeps
the same signed readout and genuine four-leg frame as the coordinate bridge,
but requires the exactifier/generator intertwining law on the explicit
four-coordinate assembled state itself. The reduced coordinate transport for
`ρ₃` will then be derived rather than postulated. -/
structure LocalEventStateBridge (Index Time Carrier Law : Type) where
  object : LocalEventObject Index Time Carrier Law
  readout : SignedExchangeReadout object.currentCarrier
  frame : FourLegFrame object.Leg
  exactifier_realized :
    ∀ current : PairExchangeCurrent object.currentCarrier object.Leg,
      assembledState readout frame (object.exactifier.exactify current) =
        object.bridge.generator.toFun (assembledState readout frame current)

/-- The local-event state bridge determines the anchored detached current
object by taking the first framed leg as the distinguished selected leg and by
reading the selected-cut closure transport from the local-event closure law. -/
def LocalEventStateBridge.toAnchoredCurrentObject
    {Index Time Carrier Law : Type}
    (data : LocalEventStateBridge Index Time Carrier Law) :
    AnchoredCurrentObject Index Time Carrier Law where
  bridge := data.object.bridge
  physicalPrinciple := data.object.physicalPrinciple
  sameSelectedLawAsBridge := data.object.sameSelectedLawAsBridge
  commonGrammar := data.object.commonGrammar
  currentCarrier := data.object.currentCarrier
  Leg := data.object.Leg
  distinguishedLeg := data.frame.l0
  firstStableBulkEventHasFourLegs := data.object.firstStableBulkEventHasFourLegs
  sixPairSlots := data.object.sixPairSlots
  current := data.object.current
  exactifier := data.object.exactifier
  visible := data.object.visible
  quotient := data.object.quotient
  closureTransport := {
    sameSelection := data.object.sameContinuumClosureClassOnSelectedBundle
  }
  bundleArisesIntrinsicallyOnLeastMotionCut :=
    data.object.bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses :=
    data.object.noCarrierWiseVisibilityHypotheses
  firstStableBulkEventHasFourLegs_valid :=
    data.object.firstStableBulkEventHasFourLegs_valid
  sixPairSlots_valid := data.object.sixPairSlots_valid
  hiddenCoherentLaw_valid := data.object.hiddenCoherentLaw_valid
  residualReturnFieldOnSelectedCut_valid :=
    data.object.residualReturnFieldOnSelectedCut_valid
  selectedVisibleLawPhysicallyRealized_valid :=
    data.object.selectedVisibleLawPhysicallyRealized_valid
  onlyReturnActsOnVisibleBundle_valid :=
    data.object.onlyReturnActsOnVisibleBundle_valid
  characteristicEndpointReduction_valid :=
    data.object.characteristicEndpointReduction_valid
  canonicalSectorGeneration_valid :=
    data.object.canonicalSectorGeneration_valid
  symmetryRigidMinimalClosure_valid :=
    data.object.symmetryRigidMinimalClosure_valid
  carrierLevelPhysicalLaw_valid :=
    data.object.carrierLevelPhysicalLaw_valid
  bundleArisesIntrinsicallyOnLeastMotionCut_valid :=
    data.object.bundleArisesIntrinsicallyOnLeastMotionCut_valid
  noCarrierWiseVisibilityHypotheses_valid :=
    data.object.noCarrierWiseVisibilityHypotheses_valid

/-- The local-event state bridge determines the explicit assembled hidden state
on the selected cut. -/
def LocalEventStateBridge.toCurrentStateAssembly
    {Index Time Carrier Law : Type}
    (data : LocalEventStateBridge Index Time Carrier Law) :
    CurrentStateAssembly data.toAnchoredCurrentObject where
  readout := data.readout
  frame := data.frame
  exactifier_realized := data.exactifier_realized

/-- On the stronger local-event state bridge, the reduced coordinate transport
for `ρ₃` is already a theorem. -/
theorem LocalEventStateBridge.coordinateTransport
    {Index Time Carrier Law : Type}
    (data : LocalEventStateBridge Index Time Carrier Law) :
    ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
      assembledCoordinates data.readout data.frame (data.object.exactifier.exactify current) =
        BalancedCoordinates.transport data.object.bridge.generator.toFun
          (assembledCoordinates data.readout data.frame current) := by
  intro current
  simpa [LocalEventStateBridge.toCurrentStateAssembly,
    CurrentStateAssembly.realizeCoordinates,
    CurrentStateAssembly.realizeBalanced,
    assembledBalancedState]
    using data.toCurrentStateAssembly.coordinateTransport current

/-- Explicit assembled four-state carried directly by the stronger local-event
state bridge. -/
def LocalEventStateBridge.currentState
    {Index Time Carrier Law : Type}
    (data : LocalEventStateBridge Index Time Carrier Law) :
    PairExchangeCurrent data.object.currentCarrier data.object.Leg → State :=
  assembledState data.readout data.frame

/-- The stronger local-event state bridge already carries the explicit
four-state transport law. -/
theorem LocalEventStateBridge.currentState_transport
    {Index Time Carrier Law : Type}
    (data : LocalEventStateBridge Index Time Carrier Law) :
    ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
      data.currentState (data.object.exactifier.exactify current) =
        data.object.bridge.generator.toFun (data.currentState current) := by
  intro current
  exact data.exactifier_realized current

/-- Concrete reduced hidden coordinates carried directly by the stronger
local-event state bridge. -/
def LocalEventStateBridge.currentCoordinates
    {Index Time Carrier Law : Type}
    (data : LocalEventStateBridge Index Time Carrier Law) :
    PairExchangeCurrent data.object.currentCarrier data.object.Leg →
      BalancedCoordinates :=
  assembledCoordinates data.readout data.frame

/-- The reduced coordinates on the stronger local-event state bridge are
exactly the first three framed leg-flux coordinates. -/
theorem LocalEventStateBridge.coordinateFormula
    {Index Time Carrier Law : Type}
    (data : LocalEventStateBridge Index Time Carrier Law) :
    ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
      data.currentCoordinates current =
        ⟨legFlux data.readout data.frame current data.frame.l0,
          legFlux data.readout data.frame current data.frame.l1,
          legFlux data.readout data.frame current data.frame.l2⟩ := by
  intro current
  rfl

/-- Pure reduced observed dynamics determined directly by the stronger
local-event state bridge. -/
def LocalEventStateBridge.reducedDynamics
    {Index Time Carrier Law : Type}
    (data : LocalEventStateBridge Index Time Carrier Law) :
    ReducedObservedDynamics :=
  data.toAnchoredCurrentObject.reducedObservedSystem.toDynamics

/-- Pure reduced initial-value state determined directly by one detached
current on the stronger local-event state bridge. -/
def LocalEventStateBridge.initialStateOf
    {Index Time Carrier Law : Type}
    (data : LocalEventStateBridge Index Time Carrier Law)
    (current : PairExchangeCurrent data.object.currentCarrier data.object.Leg) :
    ReducedObservedDynamicsState where
  dynamics := data.reducedDynamics
  initial := data.currentCoordinates current

/-- Pure four-state detached dynamics carried directly by the stronger
local-event state bridge. -/
def LocalEventStateBridge.stateDynamics
    {Index Time Carrier Law : Type}
    (data : LocalEventStateBridge Index Time Carrier Law) :
    StateDynamics where
  step := data.object.bridge.generator.toFun

/-- Pure four-state initial-value state determined directly by one detached
current on the stronger local-event state bridge. -/
def LocalEventStateBridge.stateInitialStateOf
    {Index Time Carrier Law : Type}
    (data : LocalEventStateBridge Index Time Carrier Law)
    (current : PairExchangeCurrent data.object.currentCarrier data.object.Leg) :
    StateDynamicsState where
  dynamics := data.stateDynamics
  initial := data.currentState current

/-- Smallest upstream bridge from the detached local-event current object to
the explicit coordinate assembly. Beyond the local pair current and exactifier,
the only remaining microscopic datum is a signed readout, a genuine four-leg
frame, and the reduced transport identity they induce for `ρ₃`. -/
structure LocalEventCoordinateObject (Index Time Carrier Law : Type) where
  object : LocalEventObject Index Time Carrier Law
  readout : SignedExchangeReadout object.currentCarrier
  frame : FourLegFrame object.Leg
  coordinateTransport :
    ∀ current : PairExchangeCurrent object.currentCarrier object.Leg,
      assembledCoordinates readout frame (object.exactifier.exactify current) =
        BalancedCoordinates.transport object.bridge.generator.toFun
          (assembledCoordinates readout frame current)

/-- Concrete reduced hidden coordinates read directly from the local-event
pair current by the signed readout and four-leg frame. -/
def LocalEventCoordinateObject.currentCoordinates
    {Index Time Carrier Law : Type}
    (data : LocalEventCoordinateObject Index Time Carrier Law) :
    PairExchangeCurrent data.object.currentCarrier data.object.Leg →
      BalancedCoordinates :=
  assembledCoordinates data.readout data.frame

/-- The local-event coordinate bridge determines the anchored detached current
object by taking the first framed leg as the distinguished selected leg and by
reading the selected-cut closure transport from the local-event closure law. -/
def LocalEventCoordinateObject.toAnchoredCurrentObject
    {Index Time Carrier Law : Type}
    (data : LocalEventCoordinateObject Index Time Carrier Law) :
    AnchoredCurrentObject Index Time Carrier Law where
  bridge := data.object.bridge
  physicalPrinciple := data.object.physicalPrinciple
  sameSelectedLawAsBridge := data.object.sameSelectedLawAsBridge
  commonGrammar := data.object.commonGrammar
  currentCarrier := data.object.currentCarrier
  Leg := data.object.Leg
  distinguishedLeg := data.frame.l0
  firstStableBulkEventHasFourLegs := data.object.firstStableBulkEventHasFourLegs
  sixPairSlots := data.object.sixPairSlots
  current := data.object.current
  exactifier := data.object.exactifier
  visible := data.object.visible
  quotient := data.object.quotient
  closureTransport := {
    sameSelection := data.object.sameContinuumClosureClassOnSelectedBundle
  }
  bundleArisesIntrinsicallyOnLeastMotionCut :=
    data.object.bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses :=
    data.object.noCarrierWiseVisibilityHypotheses
  firstStableBulkEventHasFourLegs_valid :=
    data.object.firstStableBulkEventHasFourLegs_valid
  sixPairSlots_valid := data.object.sixPairSlots_valid
  hiddenCoherentLaw_valid := data.object.hiddenCoherentLaw_valid
  residualReturnFieldOnSelectedCut_valid :=
    data.object.residualReturnFieldOnSelectedCut_valid
  selectedVisibleLawPhysicallyRealized_valid :=
    data.object.selectedVisibleLawPhysicallyRealized_valid
  onlyReturnActsOnVisibleBundle_valid :=
    data.object.onlyReturnActsOnVisibleBundle_valid
  characteristicEndpointReduction_valid :=
    data.object.characteristicEndpointReduction_valid
  canonicalSectorGeneration_valid :=
    data.object.canonicalSectorGeneration_valid
  symmetryRigidMinimalClosure_valid :=
    data.object.symmetryRigidMinimalClosure_valid
  carrierLevelPhysicalLaw_valid :=
    data.object.carrierLevelPhysicalLaw_valid
  bundleArisesIntrinsicallyOnLeastMotionCut_valid :=
    data.object.bundleArisesIntrinsicallyOnLeastMotionCut_valid
  noCarrierWiseVisibilityHypotheses_valid :=
    data.object.noCarrierWiseVisibilityHypotheses_valid

/-- The local-event coordinate bridge determines the smaller anchored
coordinate object used by the reduced detached dynamics. -/
def LocalEventCoordinateObject.toCoordinateAnchoredCurrentObject
    {Index Time Carrier Law : Type}
    (data : LocalEventCoordinateObject Index Time Carrier Law) :
    CoordinateAnchoredCurrentObject Index Time Carrier Law where
  object := data.toAnchoredCurrentObject
  coordinateAssembly := {
    readout := data.readout
    frame := data.frame
    coordinateTransport := data.coordinateTransport
  }

/-- The local-event coordinate bridge determines the selected reduced state of
the detached current directly from the selected bridge and the explicit
coordinate readout. -/
def LocalEventCoordinateObject.selectedReducedStateOf
    {Index Time Carrier Law : Type}
    (data : LocalEventCoordinateObject Index Time Carrier Law)
    (current : PairExchangeCurrent data.object.currentCarrier data.object.Leg) :
    SelectedReducedState :=
  data.toCoordinateAnchoredCurrentObject.selectedReducedStateOf current

/-- Pure reduced observed dynamics determined by the local-event coordinate
bridge. Once the coordinate bridge is part of the assumed microscopic package,
no further current-side datum is needed to state the detached reduced update
law or its observed readout. -/
def LocalEventCoordinateObject.reducedDynamics
    {Index Time Carrier Law : Type}
    (data : LocalEventCoordinateObject Index Time Carrier Law) :
    ReducedObservedDynamics :=
  data.toAnchoredCurrentObject.reducedObservedSystem.toDynamics

/-- Pure reduced initial-value state determined by one detached current on the
local-event coordinate bridge. -/
def LocalEventCoordinateObject.initialStateOf
    {Index Time Carrier Law : Type}
    (data : LocalEventCoordinateObject Index Time Carrier Law)
    (current : PairExchangeCurrent data.object.currentCarrier data.object.Leg) :
    ReducedObservedDynamicsState :=
  (data.selectedReducedStateOf current).toDynamicsState

/-- The detached hidden current trajectory already factors through the reduced
selected-bridge state determined by the local-event coordinate bridge. -/
theorem LocalEventCoordinateObject.hiddenTrajectory_selectedReducedStateOf
    {Index Time Carrier Law : Type}
    (data : LocalEventCoordinateObject Index Time Carrier Law) :
    ∀ n : Nat,
      ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
        data.currentCoordinates (data.toAnchoredCurrentObject.exactifyIterate n current) =
          (data.selectedReducedStateOf current).hiddenTrajectory n := by
  intro n current
  exact
    data.toCoordinateAnchoredCurrentObject.hiddenTrajectory_selectedReducedStateOf
      n current

/-- The detached observed trajectory already factors through the same reduced
selected-bridge state determined by the local-event coordinate bridge. -/
theorem LocalEventCoordinateObject.observedTrajectory_selectedReducedStateOf
    {Index Time Carrier Law : Type}
    (data : LocalEventCoordinateObject Index Time Carrier Law) :
    ∀ n : Nat,
      ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
        ((data.toCoordinateAnchoredCurrentObject.toReducedAnchoredCurrentObject).currentObservedState)
          (data.toAnchoredCurrentObject.exactifyIterate n current) =
          (data.selectedReducedStateOf current).observedTrajectory n := by
  intro n current
  exact
    data.toCoordinateAnchoredCurrentObject.observedTrajectory_selectedReducedStateOf
      n current

/-- The detached hidden current trajectory is exactly the hidden orbit of the
pure reduced initial-value problem determined by the local-event coordinate
bridge. -/
theorem LocalEventCoordinateObject.hiddenTrajectory_initialStateOf
    {Index Time Carrier Law : Type}
    (data : LocalEventCoordinateObject Index Time Carrier Law) :
    ∀ n : Nat,
      ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
        data.currentCoordinates (data.toAnchoredCurrentObject.exactifyIterate n current) =
          (data.initialStateOf current).hiddenTrajectory n := by
  intro n current
  calc
    data.currentCoordinates (data.toAnchoredCurrentObject.exactifyIterate n current) =
        (data.selectedReducedStateOf current).hiddenTrajectory n :=
      data.hiddenTrajectory_selectedReducedStateOf n current
    _ = (data.initialStateOf current).hiddenTrajectory n := by
      symm
      exact (data.selectedReducedStateOf current).hiddenTrajectory_toDynamicsState n

/-- The detached observed trajectory is exactly the observed orbit of the pure
reduced initial-value problem determined by the local-event coordinate bridge.
-/
theorem LocalEventCoordinateObject.observedTrajectory_initialStateOf
    {Index Time Carrier Law : Type}
    (data : LocalEventCoordinateObject Index Time Carrier Law) :
    ∀ n : Nat,
      ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
        ((data.toCoordinateAnchoredCurrentObject.toReducedAnchoredCurrentObject).currentObservedState)
          (data.toAnchoredCurrentObject.exactifyIterate n current) =
            (data.initialStateOf current).observedTrajectory n := by
  intro n current
  calc
    ((data.toCoordinateAnchoredCurrentObject.toReducedAnchoredCurrentObject).currentObservedState)
        (data.toAnchoredCurrentObject.exactifyIterate n current) =
          (data.selectedReducedStateOf current).observedTrajectory n :=
      data.observedTrajectory_selectedReducedStateOf n current
    _ = (data.initialStateOf current).observedTrajectory n := by
      symm
      exact (data.selectedReducedStateOf current).observedTrajectory_toDynamicsState n

/-- Surface theorem for the local-event coordinate bridge. Once the local
pair-current/event object is fixed, the only remaining upstream microscopic
datum needed to generate the detached future is the explicit coordinate
assembly for `ρ₃`; the hidden and observed futures then factor exactly through
the selected bridge from that reduced initial coordinate. -/
theorem LocalEventCoordinateObject.surface
    {Index Time Carrier Law : Type}
    (data : LocalEventCoordinateObject Index Time Carrier Law) :
    Nonempty (PairExchangeCurrent data.object.currentCarrier data.object.Leg) ∧
      data.object.currentDirectReturnCompatible ∧
      data.object.visiblePrimitiveReadoutAutonomous ∧
      data.object.minimalVisibleQuotients ∧
      (∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
        (data.initialStateOf current).dynamics = data.reducedDynamics) ∧
      (∀ n : Nat,
        ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
          data.currentCoordinates (data.toAnchoredCurrentObject.exactifyIterate n current) =
            (data.initialStateOf current).hiddenTrajectory n) ∧
      (∀ n : Nat,
        ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
          ((data.toCoordinateAnchoredCurrentObject.toReducedAnchoredCurrentObject).currentObservedState)
            (data.toAnchoredCurrentObject.exactifyIterate n current) =
            (data.initialStateOf current).observedTrajectory n) := by
  obtain ⟨hcurrent, hdirret, haut, hmin, _hstock, _hrel, _hloss, _hdefect⟩ :=
    data.object.surface
  exact
    ⟨hcurrent,
      hdirret,
      haut,
      hmin,
      by
        intro current
        rfl,
      data.hiddenTrajectory_initialStateOf,
      data.observedTrajectory_initialStateOf⟩

/-- The stronger local-event state bridge determines the smaller local-event
coordinate bridge. -/
def LocalEventStateBridge.toLocalEventCoordinateObject
    {Index Time Carrier Law : Type}
    (data : LocalEventStateBridge Index Time Carrier Law) :
    LocalEventCoordinateObject Index Time Carrier Law where
  object := data.object
  readout := data.readout
  frame := data.frame
  coordinateTransport := data.coordinateTransport

/-- The detached hidden current trajectory is exactly the hidden orbit of the
pure reduced initial-value problem carried directly by the stronger local-event
state bridge. -/
theorem LocalEventStateBridge.hiddenTrajectory_initialStateOf
    {Index Time Carrier Law : Type}
    (data : LocalEventStateBridge Index Time Carrier Law) :
    ∀ n : Nat,
      ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
        data.currentCoordinates (data.toAnchoredCurrentObject.exactifyIterate n current) =
          (data.initialStateOf current).hiddenTrajectory n := by
  intro n current
  calc
    data.currentCoordinates (data.toAnchoredCurrentObject.exactifyIterate n current) =
        (data.toLocalEventCoordinateObject.initialStateOf current).hiddenTrajectory n := by
      exact data.toLocalEventCoordinateObject.hiddenTrajectory_initialStateOf n current
    _ = (data.initialStateOf current).hiddenTrajectory n := by
      rfl

/-- The detached observed trajectory is exactly the observed orbit of the
pure reduced initial-value problem carried directly by the stronger local-event
state bridge. -/
theorem LocalEventStateBridge.observedTrajectory_initialStateOf
    {Index Time Carrier Law : Type}
    (data : LocalEventStateBridge Index Time Carrier Law) :
    ∀ n : Nat,
      ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
        ((data.toLocalEventCoordinateObject.toCoordinateAnchoredCurrentObject.toReducedAnchoredCurrentObject).currentObservedState)
        (data.toAnchoredCurrentObject.exactifyIterate n current) =
          (data.initialStateOf current).observedTrajectory n := by
  intro n current
  calc
    ((data.toLocalEventCoordinateObject.toCoordinateAnchoredCurrentObject.toReducedAnchoredCurrentObject).currentObservedState)
        (data.toAnchoredCurrentObject.exactifyIterate n current) =
          (data.toLocalEventCoordinateObject.initialStateOf current).observedTrajectory n := by
      exact data.toLocalEventCoordinateObject.observedTrajectory_initialStateOf n current
    _ = (data.initialStateOf current).observedTrajectory n := by
      rfl

/-- The detached four-state current trajectory is exactly the trajectory of the
pure four-state initial-value problem carried directly by the stronger
local-event state bridge. -/
theorem LocalEventStateBridge.stateTrajectory_initialStateOf
    {Index Time Carrier Law : Type}
    (data : LocalEventStateBridge Index Time Carrier Law) :
    ∀ n : Nat,
      ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
        data.currentState (data.toAnchoredCurrentObject.exactifyIterate n current) =
          (data.stateInitialStateOf current).trajectory n
  | 0, current => rfl
  | n + 1, current => by
      calc
        data.currentState
            (data.toAnchoredCurrentObject.exactifyIterate (n + 1) current) =
            data.currentState
              (data.toAnchoredCurrentObject.exactifyIterate n
                (data.object.exactifier.exactify current)) := by
              rfl
        _ = (data.stateInitialStateOf (data.object.exactifier.exactify current)).trajectory n :=
          data.stateTrajectory_initialStateOf n (data.object.exactifier.exactify current)
        _ = data.stateDynamics.step
              ((data.stateInitialStateOf current).trajectory n) := by
              change
                data.stateDynamics.trajectoryFrom
                    (data.currentState (data.object.exactifier.exactify current)) n =
                  data.stateDynamics.step
                    (data.stateDynamics.trajectoryFrom (data.currentState current) n)
              rw [data.currentState_transport current]
              exact data.stateDynamics.trajectoryFrom_step_start n (data.currentState current)
        _ = (data.stateInitialStateOf current).trajectory (n + 1) := by
              symm
              exact (data.stateInitialStateOf current).trajectory_step n

/-- Every four-state trajectory carried by the stronger local-event state bridge
stays in the balanced zero-sum sector. -/
theorem LocalEventStateBridge.stateTrajectory_balanced
    {Index Time Carrier Law : Type}
    (data : LocalEventStateBridge Index Time Carrier Law) :
    ∀ n : Nat,
      ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
        stateTotal ((data.stateInitialStateOf current).trajectory n) = SignedCount.zero := by
  intro n current
  rw [← data.stateTrajectory_initialStateOf n current]
  exact assembledState_total_zero
    data.readout data.frame
    (data.toAnchoredCurrentObject.exactifyIterate n current)

/-- The reduced hidden trajectory on the stronger local-event state bridge is
exactly the projection of the pure four-state trajectory to the balanced
three-coordinate quotient. -/
theorem LocalEventStateBridge.reducedTrajectory_projectState
    {Index Time Carrier Law : Type}
    (data : LocalEventStateBridge Index Time Carrier Law) :
    ∀ n : Nat,
      ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
        (data.initialStateOf current).hiddenTrajectory n =
          BalancedCoordinates.projectState
            ((data.stateInitialStateOf current).trajectory n) := by
  intro n current
  calc
    (data.initialStateOf current).hiddenTrajectory n =
        data.currentCoordinates (data.toAnchoredCurrentObject.exactifyIterate n current) := by
          symm
          exact data.hiddenTrajectory_initialStateOf n current
    _ = BalancedCoordinates.projectState
          (data.currentState (data.toAnchoredCurrentObject.exactifyIterate n current)) := by
          rfl
    _ = BalancedCoordinates.projectState
          ((data.stateInitialStateOf current).trajectory n) := by
          rw [data.stateTrajectory_initialStateOf n current]

/-- The reduced observed trajectory on the stronger local-event state bridge is
exactly the selected projection of the pure four-state trajectory. -/
theorem LocalEventStateBridge.observedTrajectory_stateProjection
    {Index Time Carrier Law : Type}
    (data : LocalEventStateBridge Index Time Carrier Law) :
    ∀ n : Nat,
      ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
        (data.initialStateOf current).observedTrajectory n =
          selectedProjection data.object.bridge
            ((data.stateInitialStateOf current).trajectory n) := by
  intro n current
  rw [(data.initialStateOf current).observedTrajectory_readout n]
  change
    selectedProjection data.object.bridge
      (((data.initialStateOf current).hiddenTrajectory n).toState) =
        selectedProjection data.object.bridge
          ((data.stateInitialStateOf current).trajectory n)
  rw [data.reducedTrajectory_projectState n current]
  let b : BalancedState :=
    ⟨(data.stateInitialStateOf current).trajectory n,
      data.stateTrajectory_balanced n current⟩
  have hstate :
      (BalancedCoordinates.projectState
          ((data.stateInitialStateOf current).trajectory n)).toState =
        (data.stateInitialStateOf current).trajectory n := by
    change (BalancedCoordinates.ofBalancedState b).toState = b.toState
    exact congrArg BalancedState.toState
      (BalancedCoordinates.toBalancedState_ofBalancedState b)
  rw [hstate]

/-- Surface theorem for the stronger local-event state bridge. The coordinate
bridge and the resulting pure reduced initial-value dynamics are now derived,
not separately postulated. -/
theorem LocalEventStateBridge.surface
    {Index Time Carrier Law : Type}
    (data : LocalEventStateBridge Index Time Carrier Law) :
    Nonempty (PairExchangeCurrent data.object.currentCarrier data.object.Leg) ∧
      data.object.currentDirectReturnCompatible ∧
      data.object.visiblePrimitiveReadoutAutonomous ∧
      data.object.minimalVisibleQuotients ∧
      (∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
        (data.toLocalEventCoordinateObject.initialStateOf current).dynamics =
          data.toLocalEventCoordinateObject.reducedDynamics) ∧
      (∀ n : Nat,
        ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
          assembledCoordinates data.readout data.frame
              (data.toAnchoredCurrentObject.exactifyIterate n current) =
            (data.toLocalEventCoordinateObject.initialStateOf current).hiddenTrajectory n) ∧
      (∀ n : Nat,
        ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
          ((data.toLocalEventCoordinateObject.toCoordinateAnchoredCurrentObject.toReducedAnchoredCurrentObject).currentObservedState)
              (data.toAnchoredCurrentObject.exactifyIterate n current) =
            (data.toLocalEventCoordinateObject.initialStateOf current).observedTrajectory n) := by
  exact data.toLocalEventCoordinateObject.surface

/-- Stronger surface theorem for the local-event state bridge. Beyond the
reduced detached law, the same microscopic package already determines a pure
four-state initial-value law, and the reduced hidden law is exactly its
balanced three-coordinate quotient. -/
theorem LocalEventStateBridge.stateSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventStateBridge Index Time Carrier Law) :
    Nonempty (PairExchangeCurrent data.object.currentCarrier data.object.Leg) ∧
      data.object.currentDirectReturnCompatible ∧
      data.object.visiblePrimitiveReadoutAutonomous ∧
      data.object.minimalVisibleQuotients ∧
      (∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
        (data.stateInitialStateOf current).dynamics = data.stateDynamics) ∧
      (∀ n : Nat,
        ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
          data.currentState (data.toAnchoredCurrentObject.exactifyIterate n current) =
            (data.stateInitialStateOf current).trajectory n) ∧
      (∀ n : Nat,
        ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
          stateTotal ((data.stateInitialStateOf current).trajectory n) = SignedCount.zero) ∧
      (∀ n : Nat,
        ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
          (data.initialStateOf current).hiddenTrajectory n =
            BalancedCoordinates.projectState
              ((data.stateInitialStateOf current).trajectory n)) ∧
      (∀ n : Nat,
        ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
          (data.initialStateOf current).observedTrajectory n =
            selectedProjection data.object.bridge
              ((data.stateInitialStateOf current).trajectory n)) := by
  obtain ⟨hcurrent, hdirret, haut, hmin, _hdyn, _hhidden, _hobs⟩ := data.surface
  exact
    ⟨hcurrent,
      hdirret,
      haut,
      hmin,
      by
        intro current
        rfl,
      data.stateTrajectory_initialStateOf,
      data.stateTrajectory_balanced,
      data.reducedTrajectory_projectState,
      data.observedTrajectory_stateProjection⟩

/-- No-stage detached microscopic law: one detached local-event current object,
one signed readout, one genuine four-leg frame, and the explicit four-state
exactifier/generator transport law. This is the smallest honest current-side
package that already determines both the four-state law and its reduced
balanced quotient. -/
structure LocalEventFourStateLaw (Index Time Carrier Law : Type) where
  framed : FramedLocalEventObject Index Time Carrier Law
  exactifier_realized :
    ∀ current : PairExchangeCurrent framed.object.currentCarrier framed.object.Leg,
      framed.currentState (framed.object.exactifier.exactify current) =
        framed.object.bridge.generator.toFun (framed.currentState current)

/-- The no-stage detached four-state law is exactly the stronger local-event
state bridge. -/
def LocalEventFourStateLaw.toLocalEventStateBridge
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    LocalEventStateBridge Index Time Carrier Law where
  object := data.framed.object
  readout := data.framed.readout
  frame := data.framed.frame
  exactifier_realized := data.exactifier_realized

/-- The no-stage detached four-state law already carries the explicit
four-state dynamics. -/
def LocalEventFourStateLaw.stateDynamics
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    StateDynamics :=
  data.toLocalEventStateBridge.stateDynamics

/-- The no-stage detached four-state law already determines the initial
four-state associated to one hidden current. -/
def LocalEventFourStateLaw.stateInitialStateOf
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law)
    (current : PairExchangeCurrent data.framed.object.currentCarrier data.framed.object.Leg) :
    StateDynamicsState :=
  data.toLocalEventStateBridge.stateInitialStateOf current

/-- Surface theorem for the no-stage detached four-state law. It already
determines a pure four-state initial-value system and the reduced `ρ₃` law as
its balanced quotient. -/
theorem LocalEventFourStateLaw.surface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    Nonempty (PairExchangeCurrent data.framed.object.currentCarrier data.framed.object.Leg) ∧
      data.framed.object.currentDirectReturnCompatible ∧
      data.framed.object.visiblePrimitiveReadoutAutonomous ∧
      data.framed.object.minimalVisibleQuotients ∧
      (∀ current : PairExchangeCurrent data.framed.object.currentCarrier data.framed.object.Leg,
        (data.stateInitialStateOf current).dynamics = data.stateDynamics) ∧
      (∀ n : Nat,
        ∀ current : PairExchangeCurrent data.framed.object.currentCarrier data.framed.object.Leg,
          data.framed.currentState
            (data.toLocalEventStateBridge.toAnchoredCurrentObject.exactifyIterate n current) =
            (data.stateInitialStateOf current).trajectory n) ∧
      (∀ n : Nat,
        ∀ current : PairExchangeCurrent data.framed.object.currentCarrier data.framed.object.Leg,
          stateTotal ((data.stateInitialStateOf current).trajectory n) = SignedCount.zero) ∧
      (∀ n : Nat,
        ∀ current : PairExchangeCurrent data.framed.object.currentCarrier data.framed.object.Leg,
          (data.toLocalEventStateBridge.initialStateOf current).hiddenTrajectory n =
            BalancedCoordinates.projectState
              ((data.stateInitialStateOf current).trajectory n)) ∧
      (∀ n : Nat,
        ∀ current : PairExchangeCurrent data.framed.object.currentCarrier data.framed.object.Leg,
          (data.toLocalEventStateBridge.initialStateOf current).observedTrajectory n =
            selectedProjection data.framed.object.bridge
              ((data.stateInitialStateOf current).trajectory n)) := by
  simpa [LocalEventFourStateLaw.stateDynamics, LocalEventFourStateLaw.stateInitialStateOf,
    FramedLocalEventObject.currentState, FramedLocalEventObject.currentCoordinates]
    using data.toLocalEventStateBridge.stateSurface

end ClosureCurrent

end CoherenceCalculus
