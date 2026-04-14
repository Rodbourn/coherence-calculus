import CoherenceCalculus.PartIV.ClosureCurrentObservedObjectCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentObservationFieldCore

Detached observation-field realization for the candidate closure-current lane.

`ClosureCurrentObservedObjectCore` still packaged observer realization as a
predicate-valued relation between visible quotient states and observers. This
file compresses that one step further.

The new input is:

* one selected-observer family on the chosen cut;
* one role-indexed observation field assigning a visible quotient value to each
  selected observer.

From that function-level package, the earlier predicate-style observer
realization is derived automatically.
-/

namespace ClosureCurrent

/-- Function-level observer realization of visible quotient values on one
selected cut. -/
structure VisibleObservationField
    (Time Carrier Law : Type)
    (selection : SelectionDatum Time)
    (endpointClosureClass : ContinuumLimitClass Law)
    (visible : VisibleCarrierRole → Type) where
  readsCurrent :
    ObserverSelection.LeastMotion Time Carrier Law → Prop
  observe :
    (role : VisibleCarrierRole) →
      (observer : ObserverSelection.LeastMotion Time Carrier Law) →
        readsCurrent observer →
          visible role
  sameSelection :
    ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
      readsCurrent observer →
        observer.selection = selection
  sameContinuumClosureClass :
    ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
      observer.selection = selection →
        endpointClosureClass = observer.continuumClass

/-- The function-level observation field induces the earlier predicate-style
observer realization package. -/
def VisibleObservationField.toVisibleObserverRealization
    {Time Carrier Law : Type}
    {selection : SelectionDatum Time}
    {endpointClosureClass : ContinuumLimitClass Law}
    {visible : VisibleCarrierRole → Type}
    (data :
      VisibleObservationField
        Time Carrier Law selection endpointClosureClass visible) :
    VisibleObserverRealization
      Time Carrier Law selection endpointClosureClass visible where
  readsVisibleState := fun role state observer =>
    ∃ hread : data.readsCurrent observer,
      data.observe role observer hread = state
  sameSelection := by
    intro role state observer hstate
    rcases hstate with ⟨hread, _⟩
    exact data.sameSelection observer hread
  sameContinuumClosureClass := by
    intro observer hselection
    exact data.sameContinuumClosureClass observer hselection

/-- Detached current object with function-level observation field instead of
the predicate-style observer realization. -/
structure ObservationFieldObject (Index Time Carrier Law : Type) where
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
  observationField :
    VisibleObservationField
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

/-- The function-level observation field object recovers the earlier
observer-realized current object. -/
def ObservationFieldObject.toObservedCurrentObject
    {Index Time Carrier Law : Type}
    (data : ObservationFieldObject Index Time Carrier Law) :
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
  observerRealization := data.observationField.toVisibleObserverRealization
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

/-- Surface theorem for the function-level observation field object. The
predicate-style observer realization layer is now downstream of one selected
observer family and one role-indexed observation field. -/
theorem ObservationFieldObject.surface
    {Index Time Carrier Law : Type}
    (data : ObservationFieldObject Index Time Carrier Law) :
    Nonempty (PairExchangeCurrent data.currentCarrier data.Leg) ∧
      data.toObservedCurrentObject.toLocalEventObject.currentDirectReturnCompatible ∧
      data.toObservedCurrentObject.toLocalEventObject.visiblePrimitiveReadoutAutonomous ∧
      data.toObservedCurrentObject.toLocalEventObject.minimalVisibleQuotients ∧
      Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) := by
  exact data.toObservedCurrentObject.surface

/-- Function-level observation field object plus intrinsic sector-generation
clauses. -/
structure ObservationFieldSectorObject (Index Time Carrier Law : Type)
    extends ObservationFieldObject Index Time Carrier Law where
  canonicalGeneration : SelectedBundle.CanonicalGeneration
  generatedFromIntrinsicChannelAlgebra : Prop
  minimalCompatibleRealizationsOnly : Prop
  generatedFromIntrinsicChannelAlgebra_valid :
    generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly_valid :
    minimalCompatibleRealizationsOnly

/-- The function-level observation field sector object recovers the earlier
observer-realized sector object. -/
def ObservationFieldSectorObject.toObservedCurrentSectorObject
    {Index Time Carrier Law : Type}
    (data : ObservationFieldSectorObject Index Time Carrier Law) :
    ObservedCurrentSectorObject Index Time Carrier Law where
  toObservedCurrentObject := data.toObservationFieldObject.toObservedCurrentObject
  canonicalGeneration := data.canonicalGeneration
  generatedFromIntrinsicChannelAlgebra :=
    data.generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly :=
    data.minimalCompatibleRealizationsOnly
  generatedFromIntrinsicChannelAlgebra_valid :=
    data.generatedFromIntrinsicChannelAlgebra_valid
  minimalCompatibleRealizationsOnly_valid :=
    data.minimalCompatibleRealizationsOnly_valid

/-- Surface theorem for the function-level observation field sector object. -/
theorem ObservationFieldSectorObject.surface
    {Index Time Carrier Law : Type}
    (data : ObservationFieldSectorObject Index Time Carrier Law) :
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
