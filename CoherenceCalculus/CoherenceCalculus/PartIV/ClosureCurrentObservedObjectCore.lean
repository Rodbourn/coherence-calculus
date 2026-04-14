import CoherenceCalculus.PartIV.ClosureCurrentObjectCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentObservedObjectCore

Detached observer-realized current object for the candidate closure-current
lane.

`ClosureCurrentObjectCore` introduced a first genuine current object, but it
still stored the selected bundle sectors and role-readout predicates as fields.
This file compresses that object one step further.

The new input is:

* one detached pair-exchange current object;
* one observer-side realization of the visible quotient values on the selected
  cut.

From that, the selected-bundle sectors, role-indexed readout family, and common
continuum-closure transport are derived rather than stored independently.
-/

namespace ClosureCurrent

/-- Observer realization of visible quotient values on one selected cut. -/
structure VisibleObserverRealization
    (Time Carrier Law : Type)
    (selection : SelectionDatum Time)
    (endpointClosureClass : ContinuumLimitClass Law)
    (visible : VisibleCarrierRole → Type) where
  readsVisibleState :
    (role : VisibleCarrierRole) →
      visible role →
        ObserverSelection.LeastMotion Time Carrier Law → Prop
  sameSelection :
    ∀ role : VisibleCarrierRole,
      ∀ state : visible role,
        ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
          readsVisibleState role state observer →
            observer.selection = selection
  sameContinuumClosureClass :
    ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
      observer.selection = selection →
        endpointClosureClass = observer.continuumClass

/-- Detached observer-realized current object. The visible bundle and readout
surface are read from the quotient values through the observer realization
package, rather than carried as separate fields. -/
structure ObservedCurrentObject (Index Time Carrier Law : Type) where
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
  observerRealization :
    VisibleObserverRealization
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

/-- The visible bundle sectors derived from the observer-realized quotient
object. The four direct visible sectors are witnessed by quotient values, while
the kinetic sector is witnessed by stock on a distinguished local leg. -/
def ObservedCurrentObject.derivedSectors
    {Index Time Carrier Law : Type}
    (data : ObservedCurrentObject Index Time Carrier Law) :
    BundleSectorFamily where
  sector
    | BundleSectorRole.phase => Nonempty (data.visible VisibleCarrierRole.phase)
    | BundleSectorRole.wave => Nonempty (data.visible VisibleCarrierRole.wave)
    | BundleSectorRole.kinetic => Nonempty data.currentCarrier.Stock
    | BundleSectorRole.gauge => Nonempty (data.visible VisibleCarrierRole.gauge)
    | BundleSectorRole.geometric =>
        Nonempty (data.visible VisibleCarrierRole.geometric)

/-- The observer-realized quotient object reads one visible role on the
selected bundle by feeding the current quotient value into the observer
realization interface. -/
def ObservedCurrentObject.readsRoleOnSelectedBundle
    {Index Time Carrier Law : Type}
    (data : ObservedCurrentObject Index Time Carrier Law)
    (role : VisibleCarrierRole) :
    ObserverSelection.LeastMotion Time Carrier Law → Prop :=
  fun observer =>
    data.observerRealization.readsVisibleState
      role
      ((data.quotient role).read data.current)
      observer

/-- The observer-realized quotient object determines the detached local-event
current object. -/
def ObservedCurrentObject.toLocalEventObject
    {Index Time Carrier Law : Type}
    (data : ObservedCurrentObject Index Time Carrier Law) :
    LocalEventObject Index Time Carrier Law where
  bridge := data.bridge
  physicalPrinciple := data.physicalPrinciple
  sameSelectedLawAsBridge := data.sameSelectedLawAsBridge
  commonGrammar := data.commonGrammar
  currentCarrier := data.currentCarrier
  Leg := data.Leg
  firstStableBulkEventHasFourLegs := data.firstStableBulkEventHasFourLegs
  sixPairSlots := data.sixPairSlots
  current := data.current
  exactifier := data.exactifier
  visible := data.visible
  quotient := data.quotient
  selectedObservedBundle := data.physicalPrinciple.sameCoherentBundle
  sectors := data.derivedSectors
  bundlePhysicallyRealized :=
    data.commonGrammar.selectedVisibleLawPhysicallyRealized
  bundleSharedByAllCarriers :=
    ∀ role : VisibleCarrierRole,
      ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
        data.readsRoleOnSelectedBundle role observer →
          observer.selection = data.bridge.selectedBridge.observer.selection
  sameSelectedEffectiveLawOnEachCarrier :=
    data.physicalPrinciple.selectedLaw.selection =
      data.bridge.selectedBridge.observer.selection
  carrierLevelIdentificationOnlyFinalStep :=
    data.commonGrammar.carrierLevelPhysicalLaw
  readsRoleOnSelectedBundle := data.readsRoleOnSelectedBundle
  readsRoleOnSelectedBundle_sameSelection := by
    intro role observer hread
    exact
      data.observerRealization.sameSelection
        role
        ((data.quotient role).read data.current)
        observer
        hread
  sameContinuumClosureClassOnSelectedBundle :=
    data.observerRealization.sameContinuumClosureClass
  bundleArisesIntrinsicallyOnLeastMotionCut :=
    data.bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses :=
    data.noCarrierWiseVisibilityHypotheses
  selectedObservedBundle_valid := data.physicalPrinciple.sameCoherentBundle_valid
  phaseCarrierSector_valid :=
    ⟨(data.quotient VisibleCarrierRole.phase).read data.current⟩
  waveCarrierSector_valid :=
    ⟨(data.quotient VisibleCarrierRole.wave).read data.current⟩
  kineticCarrierSector_valid :=
    ⟨data.currentCarrier.stock
        (data.current.value data.distinguishedLeg data.distinguishedLeg)⟩
  gaugeCarrierSector_valid :=
    ⟨(data.quotient VisibleCarrierRole.gauge).read data.current⟩
  geometricCarrierSector_valid :=
    ⟨(data.quotient VisibleCarrierRole.geometric).read data.current⟩
  bundlePhysicallyRealized_valid :=
    data.selectedVisibleLawPhysicallyRealized_valid
  bundleSharedByAllCarriers_valid := by
    intro role observer hread
    exact
      data.observerRealization.sameSelection
        role
        ((data.quotient role).read data.current)
        observer
        hread
  sameSelectedEffectiveLawOnEachCarrier_valid :=
    data.sameSelectedLawAsBridge
  carrierLevelIdentificationOnlyFinalStep_valid :=
    data.carrierLevelPhysicalLaw_valid
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

/-- Surface theorem for the observer-realized current object. This is the first
step where the selected-bundle sectors and role-readout predicates are derived
from the quotient object and its observer realization, rather than stored as
independent fields. -/
theorem ObservedCurrentObject.surface
    {Index Time Carrier Law : Type}
    (data : ObservedCurrentObject Index Time Carrier Law) :
    Nonempty (PairExchangeCurrent data.currentCarrier data.Leg) ∧
      data.toLocalEventObject.currentDirectReturnCompatible ∧
      data.toLocalEventObject.visiblePrimitiveReadoutAutonomous ∧
      data.toLocalEventObject.minimalVisibleQuotients ∧
      Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) := by
  obtain ⟨hcurrent, hdirret, haut, hmin, _hstock, _hrel, _hloss, _hdefect⟩ :=
    data.toLocalEventObject.surface
  have hsurf := data.toLocalEventObject.toLocalEventExactificationLaw.surface
  rcases hsurf with ⟨_, hsurf⟩
  rcases hsurf with ⟨_, hsurf⟩
  rcases hsurf with ⟨_, hsurf⟩
  rcases hsurf with ⟨_, hsurf⟩
  rcases hsurf with ⟨_, hsurf⟩
  rcases hsurf with ⟨_, hsurf⟩
  rcases hsurf with ⟨_, hsurf⟩
  rcases hsurf with ⟨_, hsurf⟩
  rcases hsurf with ⟨_, hsurf⟩
  rcases hsurf with ⟨hbundle, _⟩
  exact ⟨hcurrent, hdirret, haut, hmin, hbundle⟩

/-- Observer-realized current object plus intrinsic sector-generation clauses.
-/
structure ObservedCurrentSectorObject (Index Time Carrier Law : Type)
    extends ObservedCurrentObject Index Time Carrier Law where
  canonicalGeneration : SelectedBundle.CanonicalGeneration
  generatedFromIntrinsicChannelAlgebra : Prop
  minimalCompatibleRealizationsOnly : Prop
  generatedFromIntrinsicChannelAlgebra_valid :
    generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly_valid :
    minimalCompatibleRealizationsOnly

/-- The observer-realized sector object determines the detached local-event
sector object. -/
def ObservedCurrentSectorObject.toLocalEventSectorObject
    {Index Time Carrier Law : Type}
    (data : ObservedCurrentSectorObject Index Time Carrier Law) :
    LocalEventSectorObject Index Time Carrier Law where
  toLocalEventObject := data.toObservedCurrentObject.toLocalEventObject
  canonicalGeneration := data.canonicalGeneration
  generatedFromIntrinsicChannelAlgebra :=
    data.generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly :=
    data.minimalCompatibleRealizationsOnly
  generatedFromIntrinsicChannelAlgebra_valid :=
    data.generatedFromIntrinsicChannelAlgebra_valid
  minimalCompatibleRealizationsOnly_valid :=
    data.minimalCompatibleRealizationsOnly_valid

/-- Surface theorem for the observer-realized sector object. The same forcing
surface now follows from the current object together with one observer-side
realization package, with the bundle sectors and role-readout predicates
derived rather than separately stored. -/
theorem ObservedCurrentSectorObject.surface
    {Index Time Carrier Law : Type}
    (data : ObservedCurrentSectorObject Index Time Carrier Law) :
    Nonempty (PairExchangeCurrent data.currentCarrier data.Leg) ∧
      data.toLocalEventObject.currentDirectReturnCompatible ∧
      data.toLocalEventObject.visiblePrimitiveReadoutAutonomous ∧
      data.toLocalEventObject.minimalVisibleQuotients ∧
      Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  obtain ⟨hcurrent, hdirret, haut, hmin, hbundle⟩ := data.toObservedCurrentObject.surface
  obtain ⟨_hcurrent', _hdirret', _haut', _hmin', _hbundle', hsector, hprofile⟩ :=
    data.toLocalEventSectorObject.surface
  exact ⟨hcurrent, hdirret, haut, hmin, hbundle, hsector, hprofile⟩

end ClosureCurrent

end CoherenceCalculus
