import CoherenceCalculus.PartIV.ClosureCurrentLocalEventCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentObjectCore

Detached object-level current for the candidate closure-current lane.

The existing detached microscopic files still describe the candidate physical
law mainly as an interface: a hidden current, a local exactification law, and
the visible bundle-side readouts they determine. This file introduces a first
genuine mathematical object for that candidate law:

* a pair-exchange carrier with reversal and conserved stock;
* a local pair current on event legs;
* an event exactifier with returned defect;
* visible quotient objects read from that current.

The object remains detached from the bedrock-certified spine. Its role is to
make the candidate physics more concrete while preserving the same honest
boundary: the theorem that this object is forced from the active spine is still
separate work.
-/

namespace ClosureCurrent

/-- Abstract carrier for the detached pair-exchange current. The primitive data
are only reversal, a neutral current value, and a stock readout. No analytic or
continuum realization is imposed here. -/
structure PairExchangeCarrier where
  Value : Type
  Stock : Type
  zero : Value
  reverse : Value → Value
  stock : Value → Stock
  reverse_involutive : ∀ x : Value, reverse (reverse x) = x
  reverse_zero : reverse zero = zero
  stock_reverse : ∀ x : Value, stock (reverse x) = stock x

/-- Local pair current on one event leg type. The current vanishes on the
diagonal and changes orientation by the reversal involution. -/
structure PairExchangeCurrent
    (carrier : PairExchangeCarrier)
    (Leg : Type) where
  value : Leg → Leg → carrier.Value
  diagonal_zero : ∀ a : Leg, value a a = carrier.zero
  swap_reverse : ∀ a b : Leg, value b a = carrier.reverse (value a b)

/-- The local pair current already carries the oriented-pair grammar expected
of the detached closure current. -/
theorem PairExchangeCurrent.surface
    {carrier : PairExchangeCarrier}
    {Leg : Type}
    (data : PairExchangeCurrent carrier Leg) :
    (∀ a : Leg, data.value a a = carrier.zero) ∧
      (∀ a b : Leg, data.value b a = carrier.reverse (data.value a b)) := by
  exact ⟨data.diagonal_zero, data.swap_reverse⟩

/-- Detached local event exactifier. This packages local exactification,
returned defect, and the current-side exactification laws without choosing a
particular coordinate or continuum representation. -/
structure EventExactifier
    (carrier : PairExchangeCarrier)
    (Leg : Type) where
  exactify : PairExchangeCurrent carrier Leg → PairExchangeCurrent carrier Leg
  returnedDefect :
    PairExchangeCurrent carrier Leg → PairExchangeCurrent carrier Leg
  stockPreserved : Prop
  reverseCompatible : Prop
  relabelingEquivariant : Prop
  localLossless : Prop
  returnedDefectVisibleResidual : Prop
  stockPreserved_valid : stockPreserved
  reverseCompatible_valid : reverseCompatible
  relabelingEquivariant_valid : relabelingEquivariant
  localLossless_valid : localLossless
  returnedDefectVisibleResidual_valid :
    returnedDefectVisibleResidual

/-- A visible quotient of the detached local pair current. The quotient keeps
only the visible state and the induced autonomous visible evolution on that
state. -/
structure VisibleQuotient
    (carrier : PairExchangeCarrier)
    (Leg : Type)
    (Visible : Type) where
  read : PairExchangeCurrent carrier Leg → Visible
  evolve : Visible → Visible
  autonomousReadout : Prop
  minimalNontrivial : Prop
  autonomousReadout_valid : autonomousReadout
  minimalNontrivial_valid : minimalNontrivial

/-- Detached object-level realization of the local closure current. This is
the first object-level package in the current lane: one pair-exchange carrier,
one local pair current, one exactifier, and one visible quotient object for
each present visible role. -/
structure LocalEventObject (Index Time Carrier Law : Type) where
  bridge : BridgeData Index Time Carrier Law
  physicalPrinciple : PhysicalRealizationPrinciple Time Carrier Law
  sameSelectedLawAsBridge :
    physicalPrinciple.selectedLaw.selection =
      bridge.selectedBridge.observer.selection
  commonGrammar : CommonPartIVGrammar
  currentCarrier : PairExchangeCarrier
  Leg : Type
  firstStableBulkEventHasFourLegs : Prop
  sixPairSlots : Prop
  current : PairExchangeCurrent currentCarrier Leg
  exactifier : EventExactifier currentCarrier Leg
  visible : VisibleCarrierRole → Type
  quotient :
    (role : VisibleCarrierRole) →
      VisibleQuotient currentCarrier Leg (visible role)
  selectedObservedBundle : Prop
  sectors : BundleSectorFamily
  bundlePhysicallyRealized : Prop
  bundleSharedByAllCarriers : Prop
  sameSelectedEffectiveLawOnEachCarrier : Prop
  carrierLevelIdentificationOnlyFinalStep : Prop
  readsRoleOnSelectedBundle :
    VisibleCarrierRole →
      ObserverSelection.LeastMotion Time Carrier Law → Prop
  readsRoleOnSelectedBundle_sameSelection :
    ∀ role : VisibleCarrierRole,
      ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
        readsRoleOnSelectedBundle role observer →
          observer.selection = bridge.selectedBridge.observer.selection
  sameContinuumClosureClassOnSelectedBundle :
    ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
      observer.selection = bridge.selectedBridge.observer.selection →
        physicalPrinciple.selectedLaw.endpointClosureClass =
          observer.continuumClass
  bundleArisesIntrinsicallyOnLeastMotionCut : Prop
  noCarrierWiseVisibilityHypotheses : Prop
  selectedObservedBundle_valid : selectedObservedBundle
  phaseCarrierSector_valid : sectors.sector BundleSectorRole.phase
  waveCarrierSector_valid : sectors.sector BundleSectorRole.wave
  kineticCarrierSector_valid : sectors.sector BundleSectorRole.kinetic
  gaugeCarrierSector_valid : sectors.sector BundleSectorRole.gauge
  geometricCarrierSector_valid : sectors.sector BundleSectorRole.geometric
  bundlePhysicallyRealized_valid : bundlePhysicallyRealized
  bundleSharedByAllCarriers_valid : bundleSharedByAllCarriers
  sameSelectedEffectiveLawOnEachCarrier_valid :
    sameSelectedEffectiveLawOnEachCarrier
  carrierLevelIdentificationOnlyFinalStep_valid :
    carrierLevelIdentificationOnlyFinalStep
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

/-- Direct/return compatibility carried by the object-level pair-exchange
carrier itself. -/
def LocalEventObject.currentDirectReturnCompatible
    {Index Time Carrier Law : Type}
    (data : LocalEventObject Index Time Carrier Law) : Prop :=
  ∀ x : data.currentCarrier.Value,
    data.currentCarrier.reverse (data.currentCarrier.reverse x) = x ∧
      data.currentCarrier.stock (data.currentCarrier.reverse x) =
        data.currentCarrier.stock x

/-- All visible quotient objects are autonomous on their own visible states. -/
def LocalEventObject.visiblePrimitiveReadoutAutonomous
    {Index Time Carrier Law : Type}
    (data : LocalEventObject Index Time Carrier Law) : Prop :=
  ∀ role : VisibleCarrierRole,
    (data.quotient role).autonomousReadout

/-- All visible quotient objects are minimal nontrivial visible quotients. -/
def LocalEventObject.minimalVisibleQuotients
    {Index Time Carrier Law : Type}
    (data : LocalEventObject Index Time Carrier Law) : Prop :=
  ∀ role : VisibleCarrierRole,
    (data.quotient role).minimalNontrivial

/-- The object-level carrier supplies direct/return compatibility. -/
theorem LocalEventObject.currentDirectReturnCompatible_valid
    {Index Time Carrier Law : Type}
    (data : LocalEventObject Index Time Carrier Law) :
    data.currentDirectReturnCompatible := by
  intro x
  exact
    ⟨data.currentCarrier.reverse_involutive x,
      data.currentCarrier.stock_reverse x⟩

/-- The object-level visible quotient family is autonomous role by role. -/
theorem LocalEventObject.visiblePrimitiveReadoutAutonomous_valid
    {Index Time Carrier Law : Type}
    (data : LocalEventObject Index Time Carrier Law) :
    data.visiblePrimitiveReadoutAutonomous := by
  intro role
  exact (data.quotient role).autonomousReadout_valid

/-- The object-level visible quotient family is minimal role by role. -/
theorem LocalEventObject.minimalVisibleQuotients_valid
    {Index Time Carrier Law : Type}
    (data : LocalEventObject Index Time Carrier Law) :
    data.minimalVisibleQuotients := by
  intro role
  exact (data.quotient role).minimalNontrivial_valid

/-- The object-level realization recovers the detached local-event current law. -/
def LocalEventObject.toLocalEventCurrentLaw
    {Index Time Carrier Law : Type}
    (data : LocalEventObject Index Time Carrier Law) :
    LocalEventCurrentLaw Index Time Carrier Law where
  bridge := data.bridge
  physicalPrinciple := data.physicalPrinciple
  sameSelectedLawAsBridge := data.sameSelectedLawAsBridge
  commonGrammar := data.commonGrammar
  selectedObservedBundle := data.selectedObservedBundle
  sectors := data.sectors
  bundlePhysicallyRealized := data.bundlePhysicallyRealized
  bundleSharedByAllCarriers := data.bundleSharedByAllCarriers
  sameSelectedEffectiveLawOnEachCarrier :=
    data.sameSelectedEffectiveLawOnEachCarrier
  carrierLevelIdentificationOnlyFinalStep :=
    data.carrierLevelIdentificationOnlyFinalStep
  hiddenExactExchangeCurrent :=
    Nonempty (PairExchangeCurrent data.currentCarrier data.Leg)
  currentLivesOnOrientedPairSlots :=
    ∀ a b : data.Leg,
      data.current.value b a =
        data.currentCarrier.reverse (data.current.value a b)
  firstStableBulkEventCarriesSixSlotCurrent :=
    data.firstStableBulkEventHasFourLegs ∧ data.sixPairSlots
  currentStockConserved := data.exactifier.stockPreserved
  currentDirectReturnCompatible := data.currentDirectReturnCompatible
  readsRoleOnSelectedBundle := data.readsRoleOnSelectedBundle
  readsRoleOnSelectedBundle_sameSelection :=
    data.readsRoleOnSelectedBundle_sameSelection
  sameContinuumClosureClassOnSelectedBundle :=
    data.sameContinuumClosureClassOnSelectedBundle
  selectedObservedBundle_valid := data.selectedObservedBundle_valid
  phaseCarrierSector_valid := data.phaseCarrierSector_valid
  waveCarrierSector_valid := data.waveCarrierSector_valid
  kineticCarrierSector_valid := data.kineticCarrierSector_valid
  gaugeCarrierSector_valid := data.gaugeCarrierSector_valid
  geometricCarrierSector_valid := data.geometricCarrierSector_valid
  bundlePhysicallyRealized_valid := data.bundlePhysicallyRealized_valid
  bundleSharedByAllCarriers_valid := data.bundleSharedByAllCarriers_valid
  sameSelectedEffectiveLawOnEachCarrier_valid :=
    data.sameSelectedEffectiveLawOnEachCarrier_valid
  carrierLevelIdentificationOnlyFinalStep_valid :=
    data.carrierLevelIdentificationOnlyFinalStep_valid
  hiddenExactExchangeCurrent_valid := ⟨data.current⟩
  currentLivesOnOrientedPairSlots_valid := data.current.swap_reverse
  firstStableBulkEventCarriesSixSlotCurrent_valid :=
    ⟨data.firstStableBulkEventHasFourLegs_valid,
      data.sixPairSlots_valid⟩
  currentStockConserved_valid := data.exactifier.stockPreserved_valid
  currentDirectReturnCompatible_valid :=
    data.currentDirectReturnCompatible_valid
  hiddenCoherentLaw_valid := data.hiddenCoherentLaw_valid
  residualReturnFieldOnSelectedCut_valid :=
    data.residualReturnFieldOnSelectedCut_valid
  selectedVisibleLawPhysicallyRealized_valid :=
    data.selectedVisibleLawPhysicallyRealized_valid
  onlyReturnActsOnVisibleBundle_valid :=
    data.onlyReturnActsOnVisibleBundle_valid
  characteristicEndpointReduction_valid :=
    data.characteristicEndpointReduction_valid
  canonicalSectorGeneration_valid := data.canonicalSectorGeneration_valid
  symmetryRigidMinimalClosure_valid :=
    data.symmetryRigidMinimalClosure_valid
  carrierLevelPhysicalLaw_valid := data.carrierLevelPhysicalLaw_valid

/-- The object-level realization recovers the detached local-event
exactification/autonomy law. -/
def LocalEventObject.toLocalEventExactificationLaw
    {Index Time Carrier Law : Type}
    (data : LocalEventObject Index Time Carrier Law) :
    LocalEventExactificationLaw Index Time Carrier Law where
  toLocalEventCurrentLaw := data.toLocalEventCurrentLaw
  relabelingEquivariant := data.exactifier.relabelingEquivariant
  localLosslessExactification := data.exactifier.localLossless
  visiblePrimitiveReadoutAutonomous :=
    data.visiblePrimitiveReadoutAutonomous
  returnedDefectActsAsVisibleResidual :=
    data.exactifier.returnedDefectVisibleResidual
  bundleArisesIntrinsicallyOnLeastMotionCut :=
    data.bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses :=
    data.noCarrierWiseVisibilityHypotheses
  relabelingEquivariant_valid :=
    data.exactifier.relabelingEquivariant_valid
  localLosslessExactification_valid := data.exactifier.localLossless_valid
  visiblePrimitiveReadoutAutonomous_valid :=
    data.visiblePrimitiveReadoutAutonomous_valid
  returnedDefectActsAsVisibleResidual_valid :=
    data.exactifier.returnedDefectVisibleResidual_valid
  bundleArisesIntrinsicallyOnLeastMotionCut_valid :=
    data.bundleArisesIntrinsicallyOnLeastMotionCut_valid
  noCarrierWiseVisibilityHypotheses_valid :=
    data.noCarrierWiseVisibilityHypotheses_valid

/-- Surface theorem for the object-level realization. This is the first
detached point where the candidate closure current appears as an actual object
rather than only as a bundle of proposition-level clauses. -/
theorem LocalEventObject.surface
    {Index Time Carrier Law : Type}
    (data : LocalEventObject Index Time Carrier Law) :
    Nonempty (PairExchangeCurrent data.currentCarrier data.Leg) ∧
      data.currentDirectReturnCompatible ∧
      data.visiblePrimitiveReadoutAutonomous ∧
      data.minimalVisibleQuotients ∧
      data.exactifier.stockPreserved ∧
      data.exactifier.relabelingEquivariant ∧
      data.exactifier.localLossless ∧
      data.exactifier.returnedDefectVisibleResidual := by
  exact
    ⟨⟨data.current⟩,
      data.currentDirectReturnCompatible_valid,
      data.visiblePrimitiveReadoutAutonomous_valid,
      data.minimalVisibleQuotients_valid,
      data.exactifier.stockPreserved_valid,
      data.exactifier.relabelingEquivariant_valid,
      data.exactifier.localLossless_valid,
      data.exactifier.returnedDefectVisibleResidual_valid⟩

/-- Detached object-level realization plus the intrinsic non-dictionary sector
generation package. This is the object-side version of the present local-event
sector law. -/
structure LocalEventSectorObject (Index Time Carrier Law : Type)
    extends LocalEventObject Index Time Carrier Law where
  canonicalGeneration : SelectedBundle.CanonicalGeneration
  generatedFromIntrinsicChannelAlgebra : Prop
  minimalCompatibleRealizationsOnly : Prop
  generatedFromIntrinsicChannelAlgebra_valid :
    generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly_valid :
    minimalCompatibleRealizationsOnly

/-- The object-level sector realization recovers the detached local-event
sector law. -/
def LocalEventSectorObject.toLocalEventSectorLaw
    {Index Time Carrier Law : Type}
    (data : LocalEventSectorObject Index Time Carrier Law) :
    LocalEventSectorLaw Index Time Carrier Law where
  toLocalEventExactificationLaw :=
    data.toLocalEventObject.toLocalEventExactificationLaw
  canonicalGeneration := data.canonicalGeneration
  generatedFromIntrinsicChannelAlgebra :=
    data.generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly :=
    data.minimalCompatibleRealizationsOnly
  generatedFromIntrinsicChannelAlgebra_valid :=
    data.generatedFromIntrinsicChannelAlgebra_valid
  minimalCompatibleRealizationsOnly_valid :=
    data.minimalCompatibleRealizationsOnly_valid

/-- Surface theorem for the object-level sector realization. Once the intrinsic
sector-generation clauses are attached, the same local-event forcing seam
closes from an actual detached current object. -/
theorem LocalEventSectorObject.surface
    {Index Time Carrier Law : Type}
    (data : LocalEventSectorObject Index Time Carrier Law) :
    Nonempty (PairExchangeCurrent data.currentCarrier data.Leg) ∧
      data.currentDirectReturnCompatible ∧
      data.visiblePrimitiveReadoutAutonomous ∧
      data.minimalVisibleQuotients ∧
      Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  obtain ⟨hcurrent, hdirret, haut, hmin, _hstock, _hrel, _hloss, _hdefect⟩ :=
    data.toLocalEventObject.surface
  obtain ⟨_hhidden, _hslots, _hsix, _hstock, _hdirret', _hrel', _hexact',
    _haut', _hdefect', hbundle, hsector, _hbedrock, _haut'', _hfiber, _hreadout,
    _hgen, _hmin', hprofile⟩ := data.toLocalEventSectorLaw.surface
  exact ⟨hcurrent, hdirret, haut, hmin, hbundle, hsector, hprofile⟩

end ClosureCurrent

end CoherenceCalculus
