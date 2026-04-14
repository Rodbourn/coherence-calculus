import CoherenceCalculus.PartIV.ClosureCurrentObservationFieldCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentObserverFiberCore

Detached selected-observer fiber for the candidate closure-current lane.

`ClosureCurrentObservationFieldCore` still packages a function-level observation
field on a selected observer family. This file compresses that one step
further:

* one selected-observer fiber on the chosen cut;
* one role-indexed observation map on that fiber.

The earlier predicate-style observer realization is then read directly from
this fiber object.
-/

namespace ClosureCurrent

/-- A selected observer fiber on one chosen cut. The fiber remembers the
selected observer family itself, while the closure transport remains an honest
selected-cut condition. -/
structure SelectedObserverFiber
    (Time Carrier Law : Type)
    (selection : SelectionDatum Time)
    (endpointClosureClass : ContinuumLimitClass Law) where
  Fiber : Type
  asObserver : Fiber → ObserverSelection.LeastMotion Time Carrier Law
  sameSelection :
    ∀ f : Fiber, (asObserver f).selection = selection
  sameContinuumClosureClass :
    ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
      observer.selection = selection →
        endpointClosureClass = observer.continuumClass

/-- A role-indexed observation map on one selected observer fiber. -/
structure FiberObservationField
    (Time Carrier Law : Type)
    (selection : SelectionDatum Time)
    (endpointClosureClass : ContinuumLimitClass Law)
    (visible : VisibleCarrierRole → Type) where
  observers :
    SelectedObserverFiber
      Time Carrier Law selection endpointClosureClass
  observe :
    (role : VisibleCarrierRole) →
      observers.Fiber →
        visible role

/-- The fiber observation field induces the earlier predicate-style observer
realization. -/
def FiberObservationField.toVisibleObserverRealization
    {Time Carrier Law : Type}
    {selection : SelectionDatum Time}
    {endpointClosureClass : ContinuumLimitClass Law}
    {visible : VisibleCarrierRole → Type}
    (data :
      FiberObservationField
        Time Carrier Law selection endpointClosureClass visible) :
    VisibleObserverRealization
      Time Carrier Law selection endpointClosureClass visible where
  readsVisibleState := fun role state observer =>
    ∃ f : data.observers.Fiber,
      data.observers.asObserver f = observer ∧
        data.observe role f = state
  sameSelection := by
    intro role state observer hstate
    rcases hstate with ⟨f, hfobs, _hstate⟩
    calc
      observer.selection = (data.observers.asObserver f).selection := by
        rw [hfobs]
      _ = selection := data.observers.sameSelection f
  sameContinuumClosureClass :=
    data.observers.sameContinuumClosureClass

/-- Detached current object with selected-observer fiber and role-indexed
observation map. -/
structure FiberObservationObject (Index Time Carrier Law : Type) where
  bridge : BridgeData Index Time Carrier Law
  physicalPrinciple : PhysicalRealizationPrinciple Time Carrier Law
  sameSelectedLawAsBridge :
    physicalPrinciple.selectedLaw.selection =
      bridge.selectedBridge.observer.selection
  commonGrammar : CommonPartIVGrammar
  currentCarrier : PairExchangeCarrier
  Leg : Type
  distinguishedLeg : Leg
  firstStableBulkEventHasFourLegs : Prop
  sixPairSlots : Prop
  current : PairExchangeCurrent currentCarrier Leg
  exactifier : EventExactifier currentCarrier Leg
  visible : VisibleCarrierRole → Type
  quotient :
    (role : VisibleCarrierRole) →
      VisibleQuotient currentCarrier Leg (visible role)
  observation :
    FiberObservationField
      Time Carrier Law
      bridge.selectedBridge.observer.selection
      physicalPrinciple.selectedLaw.endpointClosureClass
      visible
  bundleArisesIntrinsicallyOnLeastMotionCut : Prop
  noCarrierWiseVisibilityHypotheses : Prop
  firstStableBulkEventHasFourLegs_valid :
    firstStableBulkEventHasFourLegs
  sixPairSlots_valid : sixPairSlots
  hiddenCoherentLaw_valid : commonGrammar.hiddenCoherentLaw
  residualReturnFieldOnSelectedCut_valid :
    commonGrammar.residualReturnFieldOnSelectedCut
  selectedVisibleLawPhysicallyRealized_valid :
    commonGrammar.selectedVisibleLawPhysicallyRealized
  onlyReturnActsOnVisibleBundle_valid :
    commonGrammar.onlyReturnActsOnVisibleBundle
  characteristicEndpointReduction_valid :
    commonGrammar.characteristicEndpointReduction
  canonicalSectorGeneration_valid :
    commonGrammar.canonicalSectorGeneration
  symmetryRigidMinimalClosure_valid :
    commonGrammar.symmetryRigidMinimalClosure
  carrierLevelPhysicalLaw_valid :
    commonGrammar.carrierLevelPhysicalLaw
  bundleArisesIntrinsicallyOnLeastMotionCut_valid :
    bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses_valid :
    noCarrierWiseVisibilityHypotheses

/-- The selected-observer fiber object recovers the observer-realized current
object directly from the fiber observation data. -/
def FiberObservationObject.toObservedCurrentObject
    {Index Time Carrier Law : Type}
    (data : FiberObservationObject Index Time Carrier Law) :
    ObservedCurrentObject Index Time Carrier Law where
  bridge := data.bridge
  physicalPrinciple := data.physicalPrinciple
  sameSelectedLawAsBridge := data.sameSelectedLawAsBridge
  commonGrammar := data.commonGrammar
  currentCarrier := data.currentCarrier
  Leg := data.Leg
  distinguishedLeg := data.distinguishedLeg
  firstStableBulkEventHasFourLegs := data.firstStableBulkEventHasFourLegs
  sixPairSlots := data.sixPairSlots
  current := data.current
  exactifier := data.exactifier
  visible := data.visible
  quotient := data.quotient
  observerRealization := data.observation.toVisibleObserverRealization
  bundleArisesIntrinsicallyOnLeastMotionCut :=
    data.bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses :=
    data.noCarrierWiseVisibilityHypotheses
  firstStableBulkEventHasFourLegs_valid :=
    data.firstStableBulkEventHasFourLegs_valid
  sixPairSlots_valid := data.sixPairSlots_valid
  hiddenCoherentLaw_valid := data.hiddenCoherentLaw_valid
  residualReturnFieldOnSelectedCut_valid :=
    data.residualReturnFieldOnSelectedCut_valid
  selectedVisibleLawPhysicallyRealized_valid :=
    data.selectedVisibleLawPhysicallyRealized_valid
  onlyReturnActsOnVisibleBundle_valid :=
    data.onlyReturnActsOnVisibleBundle_valid
  characteristicEndpointReduction_valid :=
    data.characteristicEndpointReduction_valid
  canonicalSectorGeneration_valid :=
    data.canonicalSectorGeneration_valid
  symmetryRigidMinimalClosure_valid :=
    data.symmetryRigidMinimalClosure_valid
  carrierLevelPhysicalLaw_valid :=
    data.carrierLevelPhysicalLaw_valid
  bundleArisesIntrinsicallyOnLeastMotionCut_valid :=
    data.bundleArisesIntrinsicallyOnLeastMotionCut_valid
  noCarrierWiseVisibilityHypotheses_valid :=
    data.noCarrierWiseVisibilityHypotheses_valid

/-- Surface theorem for the selected-observer fiber object. The function-level
observation-field layer is no longer needed: one observer fiber and one
role-indexed observation map already suffice to recover the reduced observer
surface. -/
theorem FiberObservationObject.surface
    {Index Time Carrier Law : Type}
    (data : FiberObservationObject Index Time Carrier Law) :
    Nonempty (PairExchangeCurrent data.currentCarrier data.Leg) ∧
      data.toObservedCurrentObject.toLocalEventObject.currentDirectReturnCompatible ∧
      data.toObservedCurrentObject.toLocalEventObject.visiblePrimitiveReadoutAutonomous ∧
      data.toObservedCurrentObject.toLocalEventObject.minimalVisibleQuotients ∧
      Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) := by
  exact data.toObservedCurrentObject.surface

/-- Selected-observer fiber object plus intrinsic sector-generation clauses. -/
structure FiberObservationSectorObject (Index Time Carrier Law : Type)
    extends FiberObservationObject Index Time Carrier Law where
  canonicalGeneration : SelectedBundle.CanonicalGeneration
  generatedFromIntrinsicChannelAlgebra : Prop
  minimalCompatibleRealizationsOnly : Prop
  generatedFromIntrinsicChannelAlgebra_valid :
    generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly_valid :
    minimalCompatibleRealizationsOnly

/-- The selected-observer fiber sector object recovers the observer-realized
sector object directly from the fiber observation data. -/
def FiberObservationSectorObject.toObservedCurrentSectorObject
    {Index Time Carrier Law : Type}
    (data : FiberObservationSectorObject Index Time Carrier Law) :
    ObservedCurrentSectorObject Index Time Carrier Law where
  toObservedCurrentObject :=
    data.toFiberObservationObject.toObservedCurrentObject
  canonicalGeneration := data.canonicalGeneration
  generatedFromIntrinsicChannelAlgebra :=
    data.generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly :=
    data.minimalCompatibleRealizationsOnly
  generatedFromIntrinsicChannelAlgebra_valid :=
    data.generatedFromIntrinsicChannelAlgebra_valid
  minimalCompatibleRealizationsOnly_valid :=
    data.minimalCompatibleRealizationsOnly_valid

/-- Surface theorem for the selected-observer fiber sector object. -/
theorem FiberObservationSectorObject.surface
    {Index Time Carrier Law : Type}
    (data : FiberObservationSectorObject Index Time Carrier Law) :
    Nonempty (PairExchangeCurrent data.currentCarrier data.Leg) ∧
      data.toObservedCurrentObject.toLocalEventObject.currentDirectReturnCompatible ∧
      data.toObservedCurrentObject.toLocalEventObject.visiblePrimitiveReadoutAutonomous ∧
      data.toObservedCurrentObject.toLocalEventObject.minimalVisibleQuotients ∧
      Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  exact data.toObservedCurrentSectorObject.surface

end ClosureCurrent

end CoherenceCalculus
