import CoherenceCalculus.PartIV.ClosureCurrentCompletionBridgeCore
import CoherenceCalculus.PartIV.ClosureCurrentNormalFormBridgeCore
import CoherenceCalculus.PartIV.ClosureCurrentAnchorCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentTargetBridgeCore

Concrete witness bridge into the abstract closure-program targets.

`ClosureCurrentOriginClosureCore` and `ClosureCurrentCompletionTargetCore`
state the remaining Newton-like theorem program above the smaller primitive
`MicroscopicClosureLaw`. This file shows that the stronger detached packages
already present in Part IV are honest witnesses for those targets:

* an object-level detached current already realizes the origin-closure target;
* an observer-realized and then anchored detached current already realize that
  same origin-closure target with progressively less primitive bundle-side
  packaging;
* an object-level detached current plus intrinsic sector data already realizes
  the sector-closure target;
* observer-realized and anchored sector objects likewise realize the
  sector-closure target;
* a no-stage detached completion law already realizes the sharper split
  completion-side targets and hence the no-stage completion target;
* an endpoint-complete flagship law already realizes the corresponding
  endpoint-witness target for its canonical no-stage completion witness;
* that same endpoint-complete flagship law therefore realizes the concrete
  existence-level full closure-program surface for its underlying smaller
  microscopic law.

This does not prove the smaller microscopic law always forces those witnesses.
It proves the target language is correctly aligned with the stronger detached
realizations already present in the codebase.
-/

namespace ClosureCurrent

/-- Read the smaller one-law microscopic closure package from a detached
object-level current. -/
def LocalEventObject.toMicroscopicClosureLaw
    {Index Time Carrier Law : Type}
    (data : LocalEventObject Index Time Carrier Law) :
    MicroscopicClosureLaw Index Time Carrier Law where
  bridge := data.bridge
  physicalPrinciple := data.physicalPrinciple
  sameSelectedLawAsBridge := data.sameSelectedLawAsBridge
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
  relabelingEquivariant := data.exactifier.relabelingEquivariant
  localLosslessExactification := data.exactifier.localLossless
  visiblePrimitiveReadoutAutonomous := data.visiblePrimitiveReadoutAutonomous
  returnedDefectActsAsVisibleResidual :=
    data.exactifier.returnedDefectVisibleResidual
  hiddenExactExchangeCurrent_valid := ⟨data.current⟩
  currentLivesOnOrientedPairSlots_valid := data.current.swap_reverse
  firstStableBulkEventCarriesSixSlotCurrent_valid :=
    ⟨data.firstStableBulkEventHasFourLegs_valid,
      data.sixPairSlots_valid⟩
  currentStockConserved_valid := data.exactifier.stockPreserved_valid
  currentDirectReturnCompatible_valid := data.currentDirectReturnCompatible_valid
  relabelingEquivariant_valid := data.exactifier.relabelingEquivariant_valid
  localLosslessExactification_valid := data.exactifier.localLossless_valid
  visiblePrimitiveReadoutAutonomous_valid :=
    data.visiblePrimitiveReadoutAutonomous_valid
  returnedDefectActsAsVisibleResidual_valid :=
    data.exactifier.returnedDefectVisibleResidual_valid

/-- Read the origin-closure witness directly from a detached object-level
current. -/
def LocalEventObject.toOriginClosureWitness
    {Index Time Carrier Law : Type}
    (data : LocalEventObject Index Time Carrier Law) :
    OriginClosureWitness data.toMicroscopicClosureLaw where
  commonGrammar := data.commonGrammar
  selectedObservedBundle := data.selectedObservedBundle
  sectors := data.sectors
  bundlePhysicallyRealized := data.bundlePhysicallyRealized
  bundleSharedByAllCarriers := data.bundleSharedByAllCarriers
  sameSelectedEffectiveLawOnEachCarrier :=
    data.sameSelectedEffectiveLawOnEachCarrier
  carrierLevelIdentificationOnlyFinalStep :=
    data.carrierLevelIdentificationOnlyFinalStep
  bundleArisesIntrinsicallyOnLeastMotionCut :=
    data.bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses :=
    data.noCarrierWiseVisibilityHypotheses
  readsRoleOnSelectedBundle := data.readsRoleOnSelectedBundle
  readsRoleOnSelectedBundle_sameSelection :=
    data.readsRoleOnSelectedBundle_sameSelection
  sameContinuumClosureClassOnSelectedBundle :=
    data.sameContinuumClosureClassOnSelectedBundle
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
  bundleArisesIntrinsicallyOnLeastMotionCut_valid :=
    data.bundleArisesIntrinsicallyOnLeastMotionCut_valid
  noCarrierWiseVisibilityHypotheses_valid :=
    data.noCarrierWiseVisibilityHypotheses_valid

/-- A detached object-level current already realizes the origin-closure target
for its associated smaller microscopic law. -/
theorem LocalEventObject.originClosureTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventObject Index Time Carrier Law) :
    OriginClosureTarget data.toMicroscopicClosureLaw := by
  exact ⟨data.toOriginClosureWitness⟩

/-- The corresponding origin-target forcing surface follows immediately from the
object-level current. -/
theorem LocalEventObject.originTargetSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventObject Index Time Carrier Law) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      realized_generator_carries_bedrock_law data.bridge.generator ∧
      AutonomousHorizon
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator ∧
      horizonFiberInvariant
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator := by
  exact
    data.toMicroscopicClosureLaw.originTargetSurface
      data.originClosureTarget

/-- Read the smaller microscopic law from an object-level sector realization. -/
def LocalEventSectorObject.toMicroscopicClosureLaw
    {Index Time Carrier Law : Type}
    (data : LocalEventSectorObject Index Time Carrier Law) :
    MicroscopicClosureLaw Index Time Carrier Law :=
  data.toLocalEventObject.toMicroscopicClosureLaw

/-- Read the origin-closure witness from an object-level sector realization. -/
def LocalEventSectorObject.toOriginClosureWitness
    {Index Time Carrier Law : Type}
    (data : LocalEventSectorObject Index Time Carrier Law) :
    OriginClosureWitness data.toMicroscopicClosureLaw :=
  data.toLocalEventObject.toOriginClosureWitness

/-- Read the sector-closure witness directly from an object-level sector
realization. -/
def LocalEventSectorObject.toSectorOriginWitness
    {Index Time Carrier Law : Type}
    (data : LocalEventSectorObject Index Time Carrier Law) :
    SectorOriginWitness data.toMicroscopicClosureLaw where
  canonicalGeneration := data.canonicalGeneration
  generatedFromIntrinsicChannelAlgebra :=
    data.generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly :=
    data.minimalCompatibleRealizationsOnly
  generatedFromIntrinsicChannelAlgebra_valid :=
    data.generatedFromIntrinsicChannelAlgebra_valid
  minimalCompatibleRealizationsOnly_valid :=
    data.minimalCompatibleRealizationsOnly_valid

/-- An object-level sector realization already realizes the sector-closure
target for its associated smaller microscopic law. -/
theorem LocalEventSectorObject.sectorClosureTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventSectorObject Index Time Carrier Law) :
    SectorClosureTarget data.toMicroscopicClosureLaw := by
  intro _origin
  exact ⟨data.toSectorOriginWitness⟩

/-- The corresponding Step 3 target surface follows immediately from the
object-level sector realization. -/
theorem LocalEventSectorObject.sectorTargetSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventSectorObject Index Time Carrier Law) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
      realized_generator_carries_bedrock_law data.bridge.generator ∧
      AutonomousHorizon
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator ∧
      horizonFiberInvariant
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator ∧
      (∃ generatedFromIntrinsicChannelAlgebra :
          Prop,
          ∃ minimalCompatibleRealizationsOnly : Prop,
            generatedFromIntrinsicChannelAlgebra ∧
              minimalCompatibleRealizationsOnly) ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  exact
    data.toMicroscopicClosureLaw.sectorTargetSurface
      data.toLocalEventObject.originClosureTarget
      data.sectorClosureTarget

/-- Read the smaller microscopic law from an observer-realized current object.
This sits one layer closer to the intended upstream theorem target: selected-
bundle sectors and role readouts are already derived from quotient data plus
observer realization, rather than stored independently. -/
def ObservedCurrentObject.toMicroscopicClosureLaw
    {Index Time Carrier Law : Type}
    (data : ObservedCurrentObject Index Time Carrier Law) :
    MicroscopicClosureLaw Index Time Carrier Law :=
  data.toLocalEventObject.toMicroscopicClosureLaw

/-- Read the origin-closure witness from an observer-realized current object.
-/
def ObservedCurrentObject.toOriginClosureWitness
    {Index Time Carrier Law : Type}
    (data : ObservedCurrentObject Index Time Carrier Law) :
    OriginClosureWitness data.toMicroscopicClosureLaw :=
  data.toLocalEventObject.toOriginClosureWitness

/-- An observer-realized current object already realizes the origin-closure
target for its associated smaller microscopic law. -/
theorem ObservedCurrentObject.originClosureTarget
    {Index Time Carrier Law : Type}
    (data : ObservedCurrentObject Index Time Carrier Law) :
    OriginClosureTarget data.toMicroscopicClosureLaw := by
  exact ⟨data.toOriginClosureWitness⟩

/-- The corresponding origin-target surface now follows from the observer-
realized current object, with the bundle/readout witness derived from observer
realization rather than stored as primitive object-level data. -/
theorem ObservedCurrentObject.originTargetSurface
    {Index Time Carrier Law : Type}
    (data : ObservedCurrentObject Index Time Carrier Law) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      realized_generator_carries_bedrock_law data.bridge.generator ∧
      AutonomousHorizon
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator ∧
      horizonFiberInvariant
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator := by
  exact
    data.toMicroscopicClosureLaw.originTargetSurface
      data.originClosureTarget

/-- Read the smaller microscopic law from an observer-realized sector object.
-/
def ObservedCurrentSectorObject.toMicroscopicClosureLaw
    {Index Time Carrier Law : Type}
    (data : ObservedCurrentSectorObject Index Time Carrier Law) :
    MicroscopicClosureLaw Index Time Carrier Law :=
  data.toLocalEventSectorObject.toMicroscopicClosureLaw

/-- Read the origin-closure witness from an observer-realized sector object.
-/
def ObservedCurrentSectorObject.toOriginClosureWitness
    {Index Time Carrier Law : Type}
    (data : ObservedCurrentSectorObject Index Time Carrier Law) :
    OriginClosureWitness data.toMicroscopicClosureLaw :=
  data.toLocalEventSectorObject.toOriginClosureWitness

/-- Read the sector-closure witness from an observer-realized sector object.
-/
def ObservedCurrentSectorObject.toSectorOriginWitness
    {Index Time Carrier Law : Type}
    (data : ObservedCurrentSectorObject Index Time Carrier Law) :
    SectorOriginWitness data.toMicroscopicClosureLaw :=
  data.toLocalEventSectorObject.toSectorOriginWitness

/-- An observer-realized sector object already realizes the sector-closure
target for its associated smaller microscopic law. -/
theorem ObservedCurrentSectorObject.sectorClosureTarget
    {Index Time Carrier Law : Type}
    (data : ObservedCurrentSectorObject Index Time Carrier Law) :
    SectorClosureTarget data.toMicroscopicClosureLaw := by
  intro _origin
  exact ⟨data.toSectorOriginWitness⟩

/-- The corresponding Step 3 target surface now follows from the observer-
realized sector object, so both bundle/readout and sector-generation witnesses
are already derived from a smaller observer-realized package. -/
theorem ObservedCurrentSectorObject.sectorTargetSurface
    {Index Time Carrier Law : Type}
    (data : ObservedCurrentSectorObject Index Time Carrier Law) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
      realized_generator_carries_bedrock_law data.bridge.generator ∧
      AutonomousHorizon
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator ∧
      horizonFiberInvariant
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator ∧
      (∃ generatedFromIntrinsicChannelAlgebra :
          Prop,
          ∃ minimalCompatibleRealizationsOnly : Prop,
            generatedFromIntrinsicChannelAlgebra ∧
              minimalCompatibleRealizationsOnly) ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  exact
    data.toMicroscopicClosureLaw.sectorTargetSurface
      data.toObservedCurrentObject.originClosureTarget
      data.sectorClosureTarget

/-- Read the smaller microscopic law from an anchored current object. This is
the next compression step above observer realization: one selected bridge
observer anchor plus closure transport already determine the observer-side
bundle/readout witness. -/
def AnchoredCurrentObject.toMicroscopicClosureLaw
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentObject Index Time Carrier Law) :
    MicroscopicClosureLaw Index Time Carrier Law :=
  data.toObservedCurrentObject.toMicroscopicClosureLaw

/-- Read the origin-closure witness from an anchored current object. -/
def AnchoredCurrentObject.toOriginClosureWitness
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentObject Index Time Carrier Law) :
    OriginClosureWitness data.toMicroscopicClosureLaw :=
  data.toObservedCurrentObject.toOriginClosureWitness

/-- An anchored current object already realizes the origin-closure target for
its associated smaller microscopic law. -/
theorem AnchoredCurrentObject.originClosureTarget
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentObject Index Time Carrier Law) :
    OriginClosureTarget data.toMicroscopicClosureLaw := by
  exact ⟨data.toOriginClosureWitness⟩

/-- The corresponding origin-target surface now follows from the anchored
current object itself. -/
theorem AnchoredCurrentObject.originTargetSurface
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentObject Index Time Carrier Law) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      realized_generator_carries_bedrock_law data.bridge.generator ∧
      AutonomousHorizon
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator ∧
      horizonFiberInvariant
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator := by
  exact
    data.toMicroscopicClosureLaw.originTargetSurface
      data.originClosureTarget

/-- Read the smaller microscopic law from an anchored current sector object.
-/
def AnchoredCurrentSectorObject.toMicroscopicClosureLaw
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentSectorObject Index Time Carrier Law) :
    MicroscopicClosureLaw Index Time Carrier Law :=
  data.toObservedCurrentSectorObject.toMicroscopicClosureLaw

/-- Read the origin-closure witness from an anchored current sector object. -/
def AnchoredCurrentSectorObject.toOriginClosureWitness
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentSectorObject Index Time Carrier Law) :
    OriginClosureWitness data.toMicroscopicClosureLaw :=
  data.toObservedCurrentSectorObject.toOriginClosureWitness

/-- Read the sector-closure witness from an anchored current sector object. -/
def AnchoredCurrentSectorObject.toSectorOriginWitness
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentSectorObject Index Time Carrier Law) :
    SectorOriginWitness data.toMicroscopicClosureLaw :=
  data.toObservedCurrentSectorObject.toSectorOriginWitness

/-- An anchored current sector object already realizes the sector-closure
target for its associated smaller microscopic law. -/
theorem AnchoredCurrentSectorObject.sectorClosureTarget
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentSectorObject Index Time Carrier Law) :
    SectorClosureTarget data.toMicroscopicClosureLaw := by
  intro _origin
  exact ⟨data.toSectorOriginWitness⟩

/-- The corresponding Step 3 target surface now follows from the anchored
sector object itself. -/
theorem AnchoredCurrentSectorObject.sectorTargetSurface
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentSectorObject Index Time Carrier Law) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
      realized_generator_carries_bedrock_law data.bridge.generator ∧
      AutonomousHorizon
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator ∧
      horizonFiberInvariant
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator ∧
      (∃ generatedFromIntrinsicChannelAlgebra :
          Prop,
          ∃ minimalCompatibleRealizationsOnly : Prop,
            generatedFromIntrinsicChannelAlgebra ∧
              minimalCompatibleRealizationsOnly) ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  exact
    data.toMicroscopicClosureLaw.sectorTargetSurface
      data.toAnchoredCurrentObject.originClosureTarget
      data.sectorClosureTarget

/-- Read the smaller microscopic closure law from a no-stage completion law. -/
def LocalEventFourStateCompletionLaw.toMicroscopicClosureLaw
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    MicroscopicClosureLaw Index Time Carrier Law :=
  data.fourStateLaw.framed.object.toMicroscopicClosureLaw

/-- Read the origin-closure witness from a no-stage completion law. -/
def LocalEventFourStateCompletionLaw.toOriginClosureWitness
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    OriginClosureWitness data.toMicroscopicClosureLaw :=
  data.fourStateLaw.framed.object.toOriginClosureWitness

/-- Read the sector-closure witness from a no-stage completion law. -/
def LocalEventFourStateCompletionLaw.toSectorOriginWitness
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    SectorOriginWitness data.toMicroscopicClosureLaw where
  canonicalGeneration := data.canonicalGeneration
  generatedFromIntrinsicChannelAlgebra :=
    data.generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly :=
    data.minimalCompatibleRealizationsOnly
  generatedFromIntrinsicChannelAlgebra_valid :=
    data.generatedFromIntrinsicChannelAlgebra_valid
  minimalCompatibleRealizationsOnly_valid :=
    data.minimalCompatibleRealizationsOnly_valid

/-- Read the smaller constructive sector law from a no-stage completion law.
This forgets the stronger object-level witness packaging while retaining the
constructive origin and Step 3 data already internal to the completion law. -/
def LocalEventFourStateCompletionLaw.toConstructiveSectorLaw
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    ConstructiveSectorLaw Index Time Carrier Law where
  toConstructiveMicroscopicLaw :=
    data.fourStateLaw.framed.object.toConstructiveMicroscopicLaw
  canonicalGeneration := data.canonicalGeneration
  generatedFromIntrinsicChannelAlgebra :=
    data.generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly :=
    data.minimalCompatibleRealizationsOnly
  generatedFromIntrinsicChannelAlgebra_valid :=
    data.generatedFromIntrinsicChannelAlgebra_valid
  minimalCompatibleRealizationsOnly_valid :=
    data.minimalCompatibleRealizationsOnly_valid

/-- Read the current-side four-state assembly witness from a no-stage
completion law. -/
def LocalEventFourStateCompletionLaw.toFourStateReadout
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    FourStateReadout data.toConstructiveSectorLaw where
  readout := data.fourStateLaw.framed.readout
  frame := data.fourStateLaw.framed.frame

/-- Read the current-side four-state assembly witness from a no-stage
completion law. -/
def LocalEventFourStateCompletionLaw.toFourStateAssembly
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    FourStateAssembly data.toConstructiveSectorLaw where
  toFourStateReadout := data.toFourStateReadout
  exactifier_realized := data.fourStateLaw.exactifier_realized

/-- Read the smaller Step 4 completion datum from a no-stage completion law.
This keeps only the carrier classification, rigidity clauses, endpoint
reduction, and canonical representative identities. -/
def LocalEventFourStateCompletionLaw.toCompletionRigidity
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    CompletionRigidity data.toConstructiveSectorLaw where
  rigidityPrinciple := {
    sectorGeneration := data.toConstructiveSectorLaw.toIntrinsicSectorGeneration
    localLawsReduceToFiniteJetOrder := data.localLawsReduceToFiniteJetOrder
    generatedSymmetryActsOnJetLevel := data.generatedSymmetryActsOnJetLevel
    compatibilityIdentitiesCutJetOperatorSpace :=
      data.compatibilityIdentitiesCutJetOperatorSpace
    admissibleEndpointEquivalenceRelation :=
      data.admissibleEndpointEquivalenceRelation
    minimalTruncationProducesFiniteClosureQuotient :=
      data.minimalTruncationProducesFiniteClosureQuotient
    singletonQuotientForcesUniqueCanonicalRepresentative :=
      data.singletonQuotientForcesUniqueCanonicalRepresentative
    nonsingletonQuotientForcesCanonicalNormalFormFamily :=
      data.nonsingletonQuotientForcesCanonicalNormalFormFamily
    localLawsReduceToFiniteJetOrder_valid :=
      data.localLawsReduceToFiniteJetOrder_valid
    generatedSymmetryActsOnJetLevel_valid :=
      data.generatedSymmetryActsOnJetLevel_valid
    compatibilityIdentitiesCutJetOperatorSpace_valid :=
      data.compatibilityIdentitiesCutJetOperatorSpace_valid
    admissibleEndpointEquivalenceRelation_valid :=
      data.admissibleEndpointEquivalenceRelation_valid
    minimalTruncationProducesFiniteClosureQuotient_valid :=
      data.minimalTruncationProducesFiniteClosureQuotient_valid
    singletonQuotientForcesUniqueCanonicalRepresentative_valid :=
      data.singletonQuotientForcesUniqueCanonicalRepresentative_valid
    nonsingletonQuotientForcesCanonicalNormalFormFamily_valid :=
      data.nonsingletonQuotientForcesCanonicalNormalFormFamily_valid }
  usesSectorGeneration := rfl
  endpointRigidity := data.endpointRigidity

/-- Read the canonical representative package from a no-stage completion law.
-/
def LocalEventFourStateCompletionLaw.toCanonicalRepresentatives
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    CanonicalRepresentatives where
  phaseCanonicalRepresentative := data.phaseCanonicalRepresentative
  waveCanonicalRepresentative := data.waveCanonicalRepresentative
  kineticRepresentativeClassified := data.kineticRepresentativeClassified
  gaugeCanonicalRepresentative := data.gaugeCanonicalRepresentative
  geometricCanonicalRepresentative := data.geometricCanonicalRepresentative
  phaseCanonicalRepresentative_valid := data.phaseCanonicalRepresentative_valid
  waveCanonicalRepresentative_valid := data.waveCanonicalRepresentative_valid
  kineticRepresentativeClassified_valid :=
    data.kineticRepresentativeClassified_valid
  gaugeCanonicalRepresentative_valid := data.gaugeCanonicalRepresentative_valid
  geometricCanonicalRepresentative_valid :=
    data.geometricCanonicalRepresentative_valid

/-- Read the smaller Step 4 completion datum from a no-stage completion law.
This keeps only the rigidity clauses, endpoint reduction, and canonical
representative identities; carrier classification is recovered from the latter.
-/
def LocalEventFourStateCompletionLaw.toCompletionAlignment
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    CompletionAlignment data.toConstructiveSectorLaw where
  localLawsReduceToFiniteJetOrder :=
    data.localLawsReduceToFiniteJetOrder
  generatedSymmetryActsOnJetLevel :=
    data.generatedSymmetryActsOnJetLevel
  compatibilityIdentitiesCutJetOperatorSpace :=
    data.compatibilityIdentitiesCutJetOperatorSpace
  admissibleEndpointEquivalenceRelation :=
    data.admissibleEndpointEquivalenceRelation
  minimalTruncationProducesFiniteClosureQuotient :=
    data.minimalTruncationProducesFiniteClosureQuotient
  singletonQuotientForcesUniqueCanonicalRepresentative :=
    data.singletonQuotientForcesUniqueCanonicalRepresentative
  nonsingletonQuotientForcesCanonicalNormalFormFamily :=
    data.nonsingletonQuotientForcesCanonicalNormalFormFamily
  endpointRigidity := data.endpointRigidity
  phaseCanonicalRepresentative := data.phaseCanonicalRepresentative
  waveCanonicalRepresentative := data.waveCanonicalRepresentative
  kineticRepresentativeClassified := data.kineticRepresentativeClassified
  gaugeCanonicalRepresentative := data.gaugeCanonicalRepresentative
  geometricCanonicalRepresentative := data.geometricCanonicalRepresentative
  localLawsReduceToFiniteJetOrder_valid :=
    data.localLawsReduceToFiniteJetOrder_valid
  generatedSymmetryActsOnJetLevel_valid :=
    data.generatedSymmetryActsOnJetLevel_valid
  compatibilityIdentitiesCutJetOperatorSpace_valid :=
    data.compatibilityIdentitiesCutJetOperatorSpace_valid
  admissibleEndpointEquivalenceRelation_valid :=
    data.admissibleEndpointEquivalenceRelation_valid
  minimalTruncationProducesFiniteClosureQuotient_valid :=
    data.minimalTruncationProducesFiniteClosureQuotient_valid
  singletonQuotientForcesUniqueCanonicalRepresentative_valid :=
    data.singletonQuotientForcesUniqueCanonicalRepresentative_valid
  nonsingletonQuotientForcesCanonicalNormalFormFamily_valid :=
    data.nonsingletonQuotientForcesCanonicalNormalFormFamily_valid
  phaseCanonicalRepresentative_valid :=
    data.phaseCanonicalRepresentative_valid
  waveCanonicalRepresentative_valid :=
    data.waveCanonicalRepresentative_valid
  kineticRepresentativeClassified_valid :=
    data.kineticRepresentativeClassified_valid
  gaugeCanonicalRepresentative_valid :=
    data.gaugeCanonicalRepresentative_valid
  geometricCanonicalRepresentative_valid :=
    data.geometricCanonicalRepresentative_valid

/-- A no-stage completion law already realizes the exact four-state assembly
target above its associated constructive sector law. -/
theorem LocalEventFourStateCompletionLaw.fourStateReadoutTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    FourStateReadoutTarget data.toConstructiveSectorLaw := by
  exact data.toFourStateReadout.readoutTarget

/-- A no-stage completion law already realizes the exact exactifier/generator
intertwining target above its chosen current-side readout package. -/
theorem LocalEventFourStateCompletionLaw.exactifierRealizationTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    ExactifierRealizationTarget data.toFourStateReadout := by
  exact data.fourStateLaw.exactifier_realized

/-- A no-stage completion law already realizes the exact four-state assembly
target above its associated constructive sector law. -/
theorem LocalEventFourStateCompletionLaw.fourStateAssemblyTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    FourStateAssemblyTarget data.toConstructiveSectorLaw := by
  exact
    data.toConstructiveSectorLaw.fourStateAssemblyTargetOfParts
      data.toFourStateReadout
      data.exactifierRealizationTarget

/-- A no-stage completion law already realizes the exact Step 4
carrier-classification target above its associated constructive sector law. -/
theorem LocalEventFourStateCompletionLaw.completionClassificationTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    CompletionClassificationTarget data.toConstructiveSectorLaw := by
  exact ⟨data.toClassification⟩

/-- A no-stage completion law already realizes the exact law-native Step 4
rigidity target above its associated constructive sector law. -/
theorem LocalEventFourStateCompletionLaw.completionRigidityTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    CompletionRigidityTarget data.toConstructiveSectorLaw := by
  exact ⟨data.toCompletionRigidity⟩

/-- A no-stage completion law already realizes the exact canonical-representative
target above its associated constructive sector law. -/
theorem LocalEventFourStateCompletionLaw.canonicalRepresentativeTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    CanonicalRepresentativeTarget data.toConstructiveSectorLaw := by
  exact ⟨data.toCanonicalRepresentatives⟩

/-- A no-stage completion law already realizes the exact Step 4 completion
target above its associated constructive sector law. -/
theorem LocalEventFourStateCompletionLaw.completionAlignmentTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    CompletionAlignmentTarget data.toConstructiveSectorLaw := by
  exact
    data.toConstructiveSectorLaw.completionAlignmentTargetOfParts
      data.completionRigidityTarget
      data.canonicalRepresentativeTarget

/-- A no-stage completion law already realizes the smaller split completion
target for its associated microscopic law. -/
theorem LocalEventFourStateCompletionLaw.completionSplitTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    CompletionSplitTarget data.toMicroscopicClosureLaw := by
  simpa [LocalEventFourStateCompletionLaw.toConstructiveSectorLaw,
    LocalEventFourStateCompletionLaw.toMicroscopicClosureLaw]
    using
      data.toConstructiveSectorLaw.completionSplitTargetOfSplitData
        data.toFourStateReadout
        data.exactifierRealizationTarget
        data.completionRigidityTarget
        data.canonicalRepresentativeTarget

/-- A no-stage completion law already realizes the exact split completion-bridge
target for its associated smaller microscopic law. -/
theorem LocalEventFourStateCompletionLaw.completionBridgeTargetOfSplitData
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    NoStageCompletionBridgeTarget data.toMicroscopicClosureLaw := by
  simpa [LocalEventFourStateCompletionLaw.toConstructiveSectorLaw,
    LocalEventFourStateCompletionLaw.toMicroscopicClosureLaw]
    using
      data.toConstructiveSectorLaw.completionBridgeTargetOfSplitData
        data.toFourStateReadout
        data.exactifierRealizationTarget
        data.completionRigidityTarget
        data.canonicalRepresentativeTarget

/-- A no-stage completion law already realizes the exact split completion-bridge
target for its associated smaller microscopic law. -/
theorem LocalEventFourStateCompletionLaw.completionBridgeTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    NoStageCompletionBridgeTarget data.toMicroscopicClosureLaw := by
  exact
    data.toMicroscopicClosureLaw.completionBridgeTargetOfSplitTarget
      data.completionSplitTarget

/-- Read the canonical no-stage completion witness from a no-stage completion
law itself. -/
def LocalEventFourStateCompletionLaw.toNoStageCompletionWitness
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    NoStageCompletionWitness data.toMicroscopicClosureLaw where
  completionLaw := data
  sameBridge := rfl
  samePhysicalPrinciple := rfl

/-- A no-stage completion law already realizes the origin-closure target for
its associated smaller microscopic law. -/
theorem LocalEventFourStateCompletionLaw.originClosureTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    OriginClosureTarget data.toMicroscopicClosureLaw := by
  exact ⟨data.toOriginClosureWitness⟩

/-- A no-stage completion law already realizes the sector-closure target for
its associated smaller microscopic law. -/
theorem LocalEventFourStateCompletionLaw.sectorClosureTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    SectorClosureTarget data.toMicroscopicClosureLaw := by
  intro _origin
  exact ⟨data.toSectorOriginWitness⟩

/-- A no-stage completion law already realizes the no-stage completion target
for its associated smaller microscopic law. -/
theorem LocalEventFourStateCompletionLaw.completionTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    NoStageCompletionTarget data.toMicroscopicClosureLaw := by
  simpa [LocalEventFourStateCompletionLaw.toConstructiveSectorLaw,
    LocalEventFourStateCompletionLaw.toMicroscopicClosureLaw]
    using
      data.toConstructiveSectorLaw.completionTargetOfSplitData
        data.toFourStateReadout
        data.exactifierRealizationTarget
        data.completionRigidityTarget
        data.canonicalRepresentativeTarget

/-- The corresponding split completion-bridge surface follows immediately from
the no-stage completion law. -/
theorem LocalEventFourStateCompletionLaw.completionBridgeTargetSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    ∃ witness : NoStageCompletionWitness data.toMicroscopicClosureLaw,
      witness.completionLaw.fourStateLaw.framed.object.bridge =
          data.toMicroscopicClosureLaw.bridge ∧
      witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          data.toMicroscopicClosureLaw.physicalPrinciple ∧
        PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion := by
  exact
    data.toMicroscopicClosureLaw.completionBridgeTargetSurfaceOfSplitTarget
      data.completionSplitTarget

/-- The corresponding completion-target surface follows immediately from the
no-stage completion law. -/
theorem LocalEventFourStateCompletionLaw.completionTargetSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    ∃ witness : NoStageCompletionWitness data.toMicroscopicClosureLaw,
      witness.completionLaw.fourStateLaw.framed.object.bridge = data.toMicroscopicClosureLaw.bridge ∧
        witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          data.toMicroscopicClosureLaw.physicalPrinciple ∧
        PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion := by
  simpa [LocalEventFourStateCompletionLaw.toConstructiveSectorLaw,
    LocalEventFourStateCompletionLaw.toMicroscopicClosureLaw]
    using
      data.toConstructiveSectorLaw.completionTargetSurfaceOfSplitData
        data.toFourStateReadout
        data.exactifierRealizationTarget
        data.completionRigidityTarget
        data.canonicalRepresentativeTarget

namespace MicroscopicClosureLaw

/-- Any existence-level exact endpoint-witness target already carries a
no-stage completion witness. -/
theorem completionTargetOfExactTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hexact : FlagshipExactTarget law) :
    NoStageCompletionTarget law := by
  rcases hexact with ⟨data, _hboundary⟩
  exact ⟨data⟩

/-- Any existence-level recognizable target already carries a no-stage
completion witness. -/
theorem completionTargetOfRecognizableTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hrecognizable : FlagshipRecognizableTarget law) :
    NoStageCompletionTarget law := by
  rcases hrecognizable with ⟨data, _hboundary⟩
  exact ⟨data⟩

/-- Any existence-level frontier target already carries a no-stage completion
witness. -/
theorem completionTargetOfFrontierTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hfrontier : FlagshipFrontierTarget law) :
    NoStageCompletionTarget law := by
  rcases hfrontier with ⟨data, _hboundary⟩
  exact ⟨data⟩

/-- A no-stage completion target already forces origin closure, because every
completion witness forgets to the selected-bundle/readout witness on the same
microscopic law. -/
theorem originClosureTargetOfCompletionTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hcompletion : NoStageCompletionTarget law) :
    OriginClosureTarget law := by
  rcases hcompletion with ⟨data⟩
  refine ⟨{
    commonGrammar := data.completionLaw.toOriginClosureWitness.commonGrammar
    selectedObservedBundle :=
      data.completionLaw.toOriginClosureWitness.selectedObservedBundle
    sectors := data.completionLaw.toOriginClosureWitness.sectors
    bundlePhysicallyRealized :=
      data.completionLaw.toOriginClosureWitness.bundlePhysicallyRealized
    bundleSharedByAllCarriers :=
      data.completionLaw.toOriginClosureWitness.bundleSharedByAllCarriers
    sameSelectedEffectiveLawOnEachCarrier :=
      data.completionLaw.toOriginClosureWitness.sameSelectedEffectiveLawOnEachCarrier
    carrierLevelIdentificationOnlyFinalStep :=
      data.completionLaw.toOriginClosureWitness.carrierLevelIdentificationOnlyFinalStep
    bundleArisesIntrinsicallyOnLeastMotionCut :=
      data.completionLaw.toOriginClosureWitness.bundleArisesIntrinsicallyOnLeastMotionCut
    noCarrierWiseVisibilityHypotheses :=
      data.completionLaw.toOriginClosureWitness.noCarrierWiseVisibilityHypotheses
    readsRoleOnSelectedBundle :=
      data.completionLaw.toOriginClosureWitness.readsRoleOnSelectedBundle
    readsRoleOnSelectedBundle_sameSelection := by
      intro role observer hread
      simpa
          [LocalEventFourStateCompletionLaw.toMicroscopicClosureLaw,
            LocalEventObject.toMicroscopicClosureLaw,
            data.sameBridge] using
        data.completionLaw.toOriginClosureWitness.readsRoleOnSelectedBundle_sameSelection
          role observer hread
    sameContinuumClosureClassOnSelectedBundle := by
      intro observer hselection
      have hselection' :
          observer.selection =
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection := by
        simpa
            [LocalEventFourStateCompletionLaw.toMicroscopicClosureLaw,
              LocalEventObject.toMicroscopicClosureLaw,
              data.sameBridge] using
          hselection
      simpa
          [LocalEventFourStateCompletionLaw.toMicroscopicClosureLaw,
            LocalEventObject.toMicroscopicClosureLaw,
            data.samePhysicalPrinciple] using
        data.completionLaw.toOriginClosureWitness.sameContinuumClosureClassOnSelectedBundle
          observer hselection'
    hiddenCoherentLaw_valid :=
      data.completionLaw.toOriginClosureWitness.hiddenCoherentLaw_valid
    residualReturnFieldOnSelectedCut_valid :=
      data.completionLaw.toOriginClosureWitness.residualReturnFieldOnSelectedCut_valid
    selectedVisibleLawPhysicallyRealized_valid :=
      data.completionLaw.toOriginClosureWitness.selectedVisibleLawPhysicallyRealized_valid
    onlyReturnActsOnVisibleBundle_valid :=
      data.completionLaw.toOriginClosureWitness.onlyReturnActsOnVisibleBundle_valid
    characteristicEndpointReduction_valid :=
      data.completionLaw.toOriginClosureWitness.characteristicEndpointReduction_valid
    canonicalSectorGeneration_valid :=
      data.completionLaw.toOriginClosureWitness.canonicalSectorGeneration_valid
    symmetryRigidMinimalClosure_valid :=
      data.completionLaw.toOriginClosureWitness.symmetryRigidMinimalClosure_valid
    carrierLevelPhysicalLaw_valid :=
      data.completionLaw.toOriginClosureWitness.carrierLevelPhysicalLaw_valid
    selectedObservedBundle_valid :=
      data.completionLaw.toOriginClosureWitness.selectedObservedBundle_valid
    phaseCarrierSector_valid :=
      data.completionLaw.toOriginClosureWitness.phaseCarrierSector_valid
    waveCarrierSector_valid :=
      data.completionLaw.toOriginClosureWitness.waveCarrierSector_valid
    kineticCarrierSector_valid :=
      data.completionLaw.toOriginClosureWitness.kineticCarrierSector_valid
    gaugeCarrierSector_valid :=
      data.completionLaw.toOriginClosureWitness.gaugeCarrierSector_valid
    geometricCarrierSector_valid :=
      data.completionLaw.toOriginClosureWitness.geometricCarrierSector_valid
    bundlePhysicallyRealized_valid :=
      data.completionLaw.toOriginClosureWitness.bundlePhysicallyRealized_valid
    bundleSharedByAllCarriers_valid :=
      data.completionLaw.toOriginClosureWitness.bundleSharedByAllCarriers_valid
    sameSelectedEffectiveLawOnEachCarrier_valid :=
      data.completionLaw.toOriginClosureWitness.sameSelectedEffectiveLawOnEachCarrier_valid
    carrierLevelIdentificationOnlyFinalStep_valid :=
      data.completionLaw.toOriginClosureWitness.carrierLevelIdentificationOnlyFinalStep_valid
    bundleArisesIntrinsicallyOnLeastMotionCut_valid :=
      data.completionLaw.toOriginClosureWitness.bundleArisesIntrinsicallyOnLeastMotionCut_valid
    noCarrierWiseVisibilityHypotheses_valid :=
      data.completionLaw.toOriginClosureWitness.noCarrierWiseVisibilityHypotheses_valid
  }⟩

/-- A no-stage completion target already forces sector closure, because every
completion witness forgets to the intrinsic sector witness on the same
microscopic law. -/
theorem sectorClosureTargetOfCompletionTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hcompletion : NoStageCompletionTarget law) :
    SectorClosureTarget law := by
  rcases hcompletion with ⟨data⟩
  intro _origin
  exact ⟨{
    canonicalGeneration := data.completionLaw.toSectorOriginWitness.canonicalGeneration
    generatedFromIntrinsicChannelAlgebra :=
      data.completionLaw.toSectorOriginWitness.generatedFromIntrinsicChannelAlgebra
    minimalCompatibleRealizationsOnly :=
      data.completionLaw.toSectorOriginWitness.minimalCompatibleRealizationsOnly
    generatedFromIntrinsicChannelAlgebra_valid :=
      data.completionLaw.toSectorOriginWitness.generatedFromIntrinsicChannelAlgebra_valid
    minimalCompatibleRealizationsOnly_valid :=
      data.completionLaw.toSectorOriginWitness.minimalCompatibleRealizationsOnly_valid
  }⟩

/-- The exact endpoint-witness target already forces origin closure. -/
theorem originClosureTargetOfExactTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hexact : FlagshipExactTarget law) :
    OriginClosureTarget law := by
  exact
    law.originClosureTargetOfCompletionTarget
      (law.completionTargetOfExactTarget hexact)

/-- The exact endpoint-witness target already forces sector closure. -/
theorem sectorClosureTargetOfExactTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hexact : FlagshipExactTarget law) :
    SectorClosureTarget law := by
  exact
    law.sectorClosureTargetOfCompletionTarget
      (law.completionTargetOfExactTarget hexact)

/-- The recognizable target already forces origin closure. -/
theorem originClosureTargetOfRecognizableTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hrecognizable : FlagshipRecognizableTarget law) :
    OriginClosureTarget law := by
  exact
    law.originClosureTargetOfCompletionTarget
      (law.completionTargetOfRecognizableTarget hrecognizable)

/-- The recognizable target already forces sector closure. -/
theorem sectorClosureTargetOfRecognizableTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hrecognizable : FlagshipRecognizableTarget law) :
    SectorClosureTarget law := by
  exact
    law.sectorClosureTargetOfCompletionTarget
      (law.completionTargetOfRecognizableTarget hrecognizable)

/-- The frontier target already forces origin closure. -/
theorem originClosureTargetOfFrontierTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hfrontier : FlagshipFrontierTarget law) :
    OriginClosureTarget law := by
  exact
    law.originClosureTargetOfCompletionTarget
      (law.completionTargetOfFrontierTarget hfrontier)

/-- The frontier target already forces sector closure. -/
theorem sectorClosureTargetOfFrontierTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hfrontier : FlagshipFrontierTarget law) :
    SectorClosureTarget law := by
  exact
    law.sectorClosureTargetOfCompletionTarget
      (law.completionTargetOfFrontierTarget hfrontier)

/-- The exact endpoint-witness target already closes the full detached closure
capstone. The separate origin and sector hypotheses are redundant once the
exact target itself is present, because it already carries a completion witness
on the same microscopic law. -/
theorem exactTargetFullClosureWitnessSurface
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hexact : FlagshipExactTarget law) :
    ∃ data : NoStageCompletionWitness law,
      ∃ endpointWitnesses : FlagshipEndpointWitnesses data.completionLaw,
        data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
          data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple ∧
          Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
          Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
          realized_generator_carries_bedrock_law law.bridge.generator ∧
          AutonomousHorizon
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          horizonFiberInvariant
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.phase.Field
              endpointWitnesses.phase.Scalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.wave.Field
              endpointWitnesses.wave.Scalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.gauge.Field
              endpointWitnesses.gauge.Source) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.geometric.Tensor
              endpointWitnesses.geometric.Scalar) := by
  exact
    law.fullClosureWitnessSurfaceOfExactTarget
      (law.originClosureTargetOfExactTarget hexact)
      (law.sectorClosureTargetOfExactTarget hexact)
      hexact

/-- The frontier target already closes the full detached closure capstone. -/
theorem frontierTargetFullClosureWitnessSurface
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hfrontier : FlagshipFrontierTarget law) :
    ∃ data : NoStageCompletionWitness law,
      ∃ endpointWitnesses : FlagshipEndpointWitnesses data.completionLaw,
        data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
          data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple ∧
          Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
          Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
          realized_generator_carries_bedrock_law law.bridge.generator ∧
          AutonomousHorizon
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          horizonFiberInvariant
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.phase.Field
              endpointWitnesses.phase.Scalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.wave.Field
              endpointWitnesses.wave.Scalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.gauge.Field
              endpointWitnesses.gauge.Source) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.geometric.Tensor
              endpointWitnesses.geometric.Scalar) := by
  exact
    law.fullClosureWitnessSurfaceOfFrontierTarget
      (law.originClosureTargetOfFrontierTarget hfrontier)
      (law.sectorClosureTargetOfFrontierTarget hfrontier)
      hfrontier

/-- The recognizable target already closes the full detached normal-form
capstone. -/
theorem recognizableTargetFullNormalFormSurface
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hrecognizable : FlagshipRecognizableTarget law) :
    ∃ data : NoStageCompletionWitness law,
      ∃ normalForms : FlagshipNormalForms Time Carrier Law,
        data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
          data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple ∧
          Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
          Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
          realized_generator_carries_bedrock_law law.bridge.generator ∧
          AutonomousHorizon
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          horizonFiberInvariant
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              normalForms.PhaseField
              normalForms.PhaseScalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              normalForms.WaveField
              normalForms.WaveScalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GaugeField
              normalForms.GaugeSource) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GeometricTensor
              normalForms.GeometricScalar) := by
  exact
    law.fullNormalFormSurfaceOfRecognizableTarget
      (law.originClosureTargetOfRecognizableTarget hrecognizable)
      (law.sectorClosureTargetOfRecognizableTarget hrecognizable)
      hrecognizable

/-- The exact endpoint-witness target already closes the full detached
normal-form capstone. -/
theorem exactTargetFullNormalFormSurface
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hexact : FlagshipExactTarget law) :
    ∃ data : NoStageCompletionWitness law,
      ∃ normalForms : FlagshipNormalForms Time Carrier Law,
        data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
          data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple ∧
          Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
          Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
          realized_generator_carries_bedrock_law law.bridge.generator ∧
          AutonomousHorizon
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          horizonFiberInvariant
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              normalForms.PhaseField
              normalForms.PhaseScalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              normalForms.WaveField
              normalForms.WaveScalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GaugeField
              normalForms.GaugeSource) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GeometricTensor
              normalForms.GeometricScalar) := by
  exact
    law.fullNormalFormSurfaceOfExactTarget
      (law.originClosureTargetOfExactTarget hexact)
      (law.sectorClosureTargetOfExactTarget hexact)
      hexact

/-- The frontier target already closes the full detached normal-form capstone.
-/
theorem frontierTargetFullNormalFormSurface
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hfrontier : FlagshipFrontierTarget law) :
    ∃ data : NoStageCompletionWitness law,
      ∃ normalForms : FlagshipNormalForms Time Carrier Law,
        data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
          data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple ∧
          Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
          Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
          realized_generator_carries_bedrock_law law.bridge.generator ∧
          AutonomousHorizon
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          horizonFiberInvariant
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              normalForms.PhaseField
              normalForms.PhaseScalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              normalForms.WaveField
              normalForms.WaveScalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GaugeField
              normalForms.GaugeSource) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GeometricTensor
              normalForms.GeometricScalar) := by
  exact
    law.fullNormalFormSurfaceOfFrontierTarget
      (law.originClosureTargetOfFrontierTarget hfrontier)
      (law.sectorClosureTargetOfFrontierTarget hfrontier)
      hfrontier

end MicroscopicClosureLaw

/-- Read the canonical split completion bridge directly from a no-stage
completion law. -/
def LocalEventFourStateCompletionLaw.toNoStageCompletionBridge
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    NoStageCompletionBridge Index Time Carrier Law :=
  data.toFourStateAssembly.toNoStageCompletionBridge
    data.toCompletionAlignment

/-- Rebuilding the canonical split completion bridge of a no-stage completion
law recovers exactly the collapsed data that the bridge remembers: the smaller
constructive sector law, the current-side four-state assembly, and the smaller
Step 4 completion alignment. The richer object-level selected-bundle witness
packaging stored by the original completion law is not part of the split
bridge and is therefore not claimed to be recovered definitionally here. -/
theorem LocalEventFourStateCompletionLaw.completionBridgeSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    data.toNoStageCompletionBridge.toLocalEventFourStateCompletionLaw.toConstructiveSectorLaw =
        data.toConstructiveSectorLaw ∧
      data.toNoStageCompletionBridge.toLocalEventFourStateCompletionLaw.toFourStateAssembly =
        data.toFourStateAssembly ∧
      data.toNoStageCompletionBridge.toLocalEventFourStateCompletionLaw.toCompletionAlignment =
        data.toCompletionAlignment := by
  cases data with
  | mk fourStateLaw canonicalGeneration
      generatedFromIntrinsicChannelAlgebra
      minimalCompatibleRealizationsOnly
      localLawsReduceToFiniteJetOrder
      generatedSymmetryActsOnJetLevel
      compatibilityIdentitiesCutJetOperatorSpace
      admissibleEndpointEquivalenceRelation
      minimalTruncationProducesFiniteClosureQuotient
      singletonQuotientForcesUniqueCanonicalRepresentative
      nonsingletonQuotientForcesCanonicalNormalFormFamily
      endpointRigidity
      phaseCanonicalRepresentative
      waveCanonicalRepresentative
      kineticRepresentativeClassified
      gaugeCanonicalRepresentative
      geometricCanonicalRepresentative
      generatedFromIntrinsicChannelAlgebra_valid
      minimalCompatibleRealizationsOnly_valid
      localLawsReduceToFiniteJetOrder_valid
      generatedSymmetryActsOnJetLevel_valid
      compatibilityIdentitiesCutJetOperatorSpace_valid
      admissibleEndpointEquivalenceRelation_valid
      minimalTruncationProducesFiniteClosureQuotient_valid
      singletonQuotientForcesUniqueCanonicalRepresentative_valid
      nonsingletonQuotientForcesCanonicalNormalFormFamily_valid
      phaseCanonicalRepresentative_valid
      waveCanonicalRepresentative_valid
      kineticRepresentativeClassified_valid
      gaugeCanonicalRepresentative_valid
      geometricCanonicalRepresentative_valid =>
    cases fourStateLaw with
    | mk framed exactifier_realized =>
        cases framed with
        | mk object readout frame =>
            cases object
            simp [LocalEventFourStateCompletionLaw.toNoStageCompletionBridge,
              NoStageCompletionBridge.toLocalEventFourStateCompletionLaw,
              NoStageCompletionBridge.toLocalEventFourStateLaw,
              NoStageCompletionBridge.toFramedLocalEventObject,
              NoStageCompletionBridge.toLocalEventObject,
              FourStateAssembly.toNoStageCompletionBridge,
              LocalEventObject.toConstructiveMicroscopicLaw,
              LocalEventFourStateCompletionLaw.toConstructiveSectorLaw,
              LocalEventFourStateCompletionLaw.toFourStateReadout,
              LocalEventFourStateCompletionLaw.toFourStateAssembly,
              LocalEventFourStateCompletionLaw.toCompletionAlignment,
              ConstructiveMicroscopicLaw.toOriginReadoutLaw,
              ConstructiveMicroscopicLaw.toOriginClosureWitness,
              ConstructiveMicroscopicLaw.toLocalEventObject,
              CompletionAlignment.toClassification,
              CompletionAlignment.toRigidityPrinciple,
              CompletionAlignment.toNaturalOperatorCompletion,
              OriginClosureWitness.toMicroscopicBundleLaw,
              ConstructiveSectorLaw.toSectorOriginWitness,
              ConstructiveSectorLaw.toIntrinsicSectorForcing,
              ConstructiveSectorLaw.toIntrinsicSectorGeneration,
              SectorOriginWitness.toIntrinsicSectorForcing,
              SectorOriginWitness.toMicroscopicSectorLaw,
              MicroscopicSectorLaw.toIntrinsicSectorForcing,
              IntrinsicSectorForcing.toIntrinsicSectorGeneration]

/-- An endpoint-complete flagship law already realizes the exact phase
endpoint-witness target for its canonical no-stage completion witness. -/
theorem LocalEventFourStateFlagshipLaw.phaseEndpointWitnessTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    PhaseEndpointWitnessTarget data.completionLaw.toNoStageCompletionWitness := by
  exact ⟨data.endpointWitnesses.phase⟩

/-- An endpoint-complete flagship law already realizes the exact wave
endpoint-witness target for its canonical no-stage completion witness. -/
theorem LocalEventFourStateFlagshipLaw.waveEndpointWitnessTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    WaveEndpointWitnessTarget data.completionLaw.toNoStageCompletionWitness := by
  exact ⟨data.endpointWitnesses.wave⟩

/-- An endpoint-complete flagship law already realizes the exact gauge
endpoint-witness target for its canonical no-stage completion witness. -/
theorem LocalEventFourStateFlagshipLaw.gaugeEndpointWitnessTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    GaugeEndpointWitnessTarget data.completionLaw.toNoStageCompletionWitness := by
  exact ⟨data.endpointWitnesses.gauge⟩

/-- An endpoint-complete flagship law already realizes the exact geometric
endpoint-witness target for its canonical no-stage completion witness. -/
theorem LocalEventFourStateFlagshipLaw.geometricEndpointWitnessTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    GeometricEndpointWitnessTarget data.completionLaw.toNoStageCompletionWitness := by
  exact ⟨data.endpointWitnesses.geometric⟩

/-- An endpoint-complete flagship law already realizes the endpoint-witness
target for its canonical no-stage completion witness. -/
theorem LocalEventFourStateFlagshipLaw.endpointWitnessTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    EndpointWitnessTarget data.completionLaw.toNoStageCompletionWitness := by
  exact
    data.completionLaw.toNoStageCompletionWitness.endpointWitnessTargetOfLaneTargets
      data.phaseEndpointWitnessTarget
      data.waveEndpointWitnessTarget
      data.gaugeEndpointWitnessTarget
      data.geometricEndpointWitnessTarget

/-- An endpoint-complete flagship law already realizes the exact fixed-witness
flagship boundary target on its canonical no-stage completion witness. -/
theorem LocalEventFourStateFlagshipLaw.flagshipExactBoundaryTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    FlagshipExactBoundaryTarget data.completionLaw.toNoStageCompletionWitness := by
  exact
    data.completionLaw.toNoStageCompletionWitness.flagshipExactBoundaryTargetOfLaneTargets
      data.phaseEndpointWitnessTarget
      data.waveEndpointWitnessTarget
      data.gaugeEndpointWitnessTarget
      data.geometricEndpointWitnessTarget

/-- An endpoint-complete flagship law already realizes the existence-level
exact endpoint-witness target for its associated smaller microscopic law. -/
theorem LocalEventFourStateFlagshipLaw.flagshipExactTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    FlagshipExactTarget data.completionLaw.toMicroscopicClosureLaw := by
  exact
    MicroscopicClosureLaw.flagshipExactTargetOfExactBoundaryTarget
      data.completionLaw.toMicroscopicClosureLaw
      data.flagshipExactBoundaryTarget

/-- An endpoint-complete flagship law already realizes the existence-level
flagship target for its associated smaller microscopic law. -/
theorem LocalEventFourStateFlagshipLaw.flagshipTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    FlagshipTarget data.completionLaw.toMicroscopicClosureLaw := by
  exact
    ⟨data.completionLaw.toNoStageCompletionWitness,
      data.endpointWitnessTarget⟩

/-- Read the direct recognizable flagship-form package from an endpoint-
complete flagship law. This forgets the auxiliary endpoint witness data and
keeps only the resulting recognizable identities. -/
def LocalEventFourStateFlagshipLaw.toFlagshipNormalForms
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    FlagshipNormalForms Time Carrier Law := by
  have hsurface := data.surface
  exact
    { PhaseField := data.endpointWitnesses.phase.Field
      PhaseScalar := data.endpointWitnesses.phase.Scalar
      phase := hsurface.2.1
      WaveField := data.endpointWitnesses.wave.Field
      WaveScalar := data.endpointWitnesses.wave.Scalar
      wave := hsurface.2.2.1
      GaugeField := data.endpointWitnesses.gauge.Field
      GaugeSource := data.endpointWitnesses.gauge.Source
      gauge := hsurface.2.2.2.1
      GeometricTensor := data.endpointWitnesses.geometric.Tensor
      GeometricScalar := data.endpointWitnesses.geometric.Scalar
      geometric := hsurface.2.2.2.2 }

/-- An endpoint-complete flagship law already realizes the direct normal-form
target for its associated smaller microscopic law. -/
theorem LocalEventFourStateFlagshipLaw.normalFormTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    NormalFormTarget data.completionLaw.toMicroscopicClosureLaw := by
  exact
      ⟨data.completionLaw.toNoStageCompletionWitness,
      ⟨data.toFlagshipNormalForms⟩⟩

/-- An endpoint-complete flagship law therefore realizes the direct
normal-form target already from the four exact endpoint-witness lane targets
above its canonical no-stage completion witness. -/
theorem LocalEventFourStateFlagshipLaw.normalFormTargetOfEndpointLaneTargets
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    NormalFormTarget data.completionLaw.toMicroscopicClosureLaw := by
  exact
    data.completionLaw.toNoStageCompletionWitness.normalFormTargetOfEndpointLaneTargets
      data.phaseEndpointWitnessTarget
      data.waveEndpointWitnessTarget
      data.gaugeEndpointWitnessTarget
      data.geometricEndpointWitnessTarget

/-- An endpoint-complete flagship law already realizes the smaller phase
frontier target above its canonical no-stage completion witness. -/
theorem LocalEventFourStateFlagshipLaw.phaseFrontierTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    PhaseFrontierTarget data.completionLaw.toNoStageCompletionWitness := by
  exact ⟨data.endpointWitnesses.phase.toFrontier⟩

/-- An endpoint-complete flagship law already realizes the smaller wave
frontier target above its canonical no-stage completion witness. -/
theorem LocalEventFourStateFlagshipLaw.waveFrontierTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    WaveFrontierTarget data.completionLaw.toNoStageCompletionWitness := by
  exact ⟨data.endpointWitnesses.wave.toFrontier⟩

/-- An endpoint-complete flagship law already realizes the smaller gauge
frontier target above its canonical no-stage completion witness. -/
theorem LocalEventFourStateFlagshipLaw.gaugeFrontierTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    GaugeFrontierTarget data.completionLaw.toNoStageCompletionWitness := by
  exact ⟨data.endpointWitnesses.gauge.toFrontier⟩

/-- An endpoint-complete flagship law already realizes the smaller geometric
frontier target above its canonical no-stage completion witness. -/
theorem LocalEventFourStateFlagshipLaw.geometricFrontierTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    GeometricFrontierTarget data.completionLaw.toNoStageCompletionWitness := by
  exact ⟨data.endpointWitnesses.geometric.toFrontier⟩

/-- An endpoint-complete flagship law already realizes the existence-level
exact fixed-witness flagship boundary target on its canonical no-stage
completion witness. -/
theorem LocalEventFourStateFlagshipLaw.flagshipBoundaryTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    FlagshipBoundaryTarget data.completionLaw.toNoStageCompletionWitness := by
  exact
    data.completionLaw.toNoStageCompletionWitness.flagshipBoundaryTargetOfFrontierTargets
      data.phaseFrontierTarget
      data.waveFrontierTarget
      data.gaugeFrontierTarget
      data.geometricFrontierTarget

/-- An endpoint-complete flagship law already realizes the existence-level
law-native frontier target for its associated smaller microscopic law. -/
theorem LocalEventFourStateFlagshipLaw.flagshipFrontierTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    FlagshipFrontierTarget data.completionLaw.toMicroscopicClosureLaw := by
  exact
    data.completionLaw.toMicroscopicClosureLaw.flagshipFrontierTargetOfBoundaryTarget
      data.flagshipBoundaryTarget

/-- An endpoint-complete flagship law already realizes the smaller phase
recognizable target above its canonical no-stage completion witness. -/
theorem LocalEventFourStateFlagshipLaw.phaseRecognizableTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    PhaseRecognizableTarget data.completionLaw.toNoStageCompletionWitness := by
  exact
    NoStageCompletionWitness.phaseRecognizableTargetOfFrontierTarget
      data.completionLaw.toNoStageCompletionWitness
      data.phaseFrontierTarget

/-- An endpoint-complete flagship law already realizes the smaller wave
recognizable target above its canonical no-stage completion witness. -/
theorem LocalEventFourStateFlagshipLaw.waveRecognizableTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    WaveRecognizableTarget data.completionLaw.toNoStageCompletionWitness := by
  exact
    NoStageCompletionWitness.waveRecognizableTargetOfFrontierTarget
      data.completionLaw.toNoStageCompletionWitness
      data.waveFrontierTarget

/-- An endpoint-complete flagship law already realizes the smaller gauge
recognizable target above its canonical no-stage completion witness. -/
theorem LocalEventFourStateFlagshipLaw.gaugeRecognizableTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    GaugeRecognizableTarget data.completionLaw.toNoStageCompletionWitness := by
  exact
    NoStageCompletionWitness.gaugeRecognizableTargetOfFrontierTarget
      data.completionLaw.toNoStageCompletionWitness
      data.gaugeFrontierTarget

/-- An endpoint-complete flagship law already realizes the smaller geometric
recognizable target above its canonical no-stage completion witness. -/
theorem LocalEventFourStateFlagshipLaw.geometricRecognizableTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    GeometricRecognizableTarget data.completionLaw.toNoStageCompletionWitness := by
  exact
    NoStageCompletionWitness.geometricRecognizableTargetOfFrontierTarget
      data.completionLaw.toNoStageCompletionWitness
      data.geometricFrontierTarget

/-- An endpoint-complete flagship law already realizes the smaller fixed-
witness recognizable boundary target above its canonical no-stage completion
witness. -/
theorem LocalEventFourStateFlagshipLaw.flagshipRecognizableBoundaryTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    FlagshipRecognizableBoundaryTarget
      data.completionLaw.toNoStageCompletionWitness := by
  exact
    NoStageCompletionWitness.flagshipRecognizableBoundaryTargetOfRecognizableTargets
      data.completionLaw.toNoStageCompletionWitness
      data.phaseRecognizableTarget
      data.waveRecognizableTarget
      data.gaugeRecognizableTarget
      data.geometricRecognizableTarget

/-- An endpoint-complete flagship law already realizes the smaller
existence-level recognizable target for its associated microscopic law. -/
theorem LocalEventFourStateFlagshipLaw.flagshipRecognizableTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    FlagshipRecognizableTarget data.completionLaw.toMicroscopicClosureLaw := by
  exact
    MicroscopicClosureLaw.flagshipRecognizableTargetOfRecognizableBoundaryTarget
      data.completionLaw.toMicroscopicClosureLaw
      data.flagshipRecognizableBoundaryTarget

/-- An endpoint-complete flagship law therefore realizes the direct
normal-form target already from the four smaller frontier targets above its
canonical no-stage completion witness. -/
theorem LocalEventFourStateFlagshipLaw.normalFormTargetOfFrontierTargets
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    NormalFormTarget data.completionLaw.toMicroscopicClosureLaw := by
  exact
    data.completionLaw.toNoStageCompletionWitness.normalFormTargetOfFrontierTargets
      data.phaseFrontierTarget
      data.waveFrontierTarget
      data.gaugeFrontierTarget
      data.geometricFrontierTarget

/-- An endpoint-complete flagship law therefore realizes the direct
normal-form target already from the four smaller recognizable lane targets
above its canonical no-stage completion witness. -/
theorem LocalEventFourStateFlagshipLaw.normalFormTargetOfRecognizableTargets
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    NormalFormTarget data.completionLaw.toMicroscopicClosureLaw := by
  exact
    data.completionLaw.toNoStageCompletionWitness.normalFormTargetOfRecognizableTargets
      data.phaseRecognizableTarget
      data.waveRecognizableTarget
      data.gaugeRecognizableTarget
      data.geometricRecognizableTarget

/-- The direct recognizable flagship surface also follows immediately from the
endpoint-complete flagship law viewed as a witness for the normal-form target.
-/
theorem LocalEventFourStateFlagshipLaw.normalFormTargetSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    ∃ witness : NoStageCompletionWitness data.completionLaw.toMicroscopicClosureLaw,
      ∃ normalForms : FlagshipNormalForms Time Carrier Law,
        witness.completionLaw.fourStateLaw.framed.object.bridge =
            data.completionLaw.toMicroscopicClosureLaw.bridge ∧
          witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.completionLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
          PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              normalForms.PhaseField
              normalForms.PhaseScalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              normalForms.WaveField
              normalForms.WaveScalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GaugeField
              normalForms.GaugeSource) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GeometricTensor
              normalForms.GeometricScalar) := by
  exact
    data.completionLaw.toMicroscopicClosureLaw.normalFormTargetSurface
      data.normalFormTarget

/-- The canonical flagship surface follows immediately from the endpoint-
complete flagship law viewed as a witness for the abstract target program. -/
theorem LocalEventFourStateFlagshipLaw.canonicalTargetSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    ∃ endpointWitnesses :
        FlagshipEndpointWitnesses data.completionLaw.toNoStageCompletionWitness.completionLaw,
      PartIVLawCompletionStatement
        data.completionLaw.toNoStageCompletionWitness.completionLaw.toNaturalOperatorCompletion ∧
      Nonempty
        (PhaseLane.RecognizableIdentity
          Time Carrier Law
          endpointWitnesses.phase.Field
          endpointWitnesses.phase.Scalar) ∧
      Nonempty
        (WaveLane.RecognizableIdentity
          Time Carrier Law
          endpointWitnesses.wave.Field
          endpointWitnesses.wave.Scalar) ∧
      Nonempty
        (GaugeLane.RecognizableIdentity
          Time Carrier Law
          endpointWitnesses.gauge.Field
          endpointWitnesses.gauge.Source) ∧
      Nonempty
        (GeometricLane.RecognizableIdentity
          Time Carrier Law
          endpointWitnesses.geometric.Tensor
          endpointWitnesses.geometric.Scalar) := by
  simpa [LocalEventFourStateCompletionLaw.toNoStageCompletionWitness] using
    data.completionLaw.toNoStageCompletionWitness.flagshipSurface
      data.endpointWitnessTarget

/-- Concrete capstone for the abstract closure-program targets. An endpoint-
complete detached flagship law already realizes the full existence-level
closure surface for its underlying smaller microscopic law from its exact
flagship target alone. -/
theorem LocalEventFourStateFlagshipLaw.fullClosureWitnessSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    ∃ witness : NoStageCompletionWitness data.completionLaw.toMicroscopicClosureLaw,
      ∃ endpointWitnesses :
          FlagshipEndpointWitnesses witness.completionLaw,
        witness.completionLaw.fourStateLaw.framed.object.bridge =
            data.completionLaw.toMicroscopicClosureLaw.bridge ∧
          witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.completionLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
          Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
          Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
          realized_generator_carries_bedrock_law
            data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
          AutonomousHorizon
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
            data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
          horizonFiberInvariant
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
            data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
          PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.phase.Field
              endpointWitnesses.phase.Scalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.wave.Field
              endpointWitnesses.wave.Scalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.gauge.Field
              endpointWitnesses.gauge.Source) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.geometric.Tensor
              endpointWitnesses.geometric.Scalar) := by
  exact
    data.completionLaw.toMicroscopicClosureLaw.exactTargetFullClosureWitnessSurface
      data.flagshipExactTarget

/-- Concrete capstone for the sharper direct normal-form surface. An
endpoint-complete detached flagship law already realizes the full detached
normal-form surface for its underlying smaller microscopic law from its
recognizable flagship target alone. -/
theorem LocalEventFourStateFlagshipLaw.fullNormalFormSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    ∃ witness : NoStageCompletionWitness data.completionLaw.toMicroscopicClosureLaw,
      ∃ normalForms : FlagshipNormalForms Time Carrier Law,
        witness.completionLaw.fourStateLaw.framed.object.bridge =
            data.completionLaw.toMicroscopicClosureLaw.bridge ∧
          witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.completionLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
          Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
          Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
          realized_generator_carries_bedrock_law
            data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
          AutonomousHorizon
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
            data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
          horizonFiberInvariant
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
            data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
          PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              normalForms.PhaseField
              normalForms.PhaseScalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              normalForms.WaveField
              normalForms.WaveScalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GaugeField
              normalForms.GaugeSource) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GeometricTensor
              normalForms.GeometricScalar) := by
  exact
    data.completionLaw.toMicroscopicClosureLaw.recognizableTargetFullNormalFormSurface
      data.flagshipRecognizableTarget

namespace StrongMicroscopicLaw

/-- Read the first theorem-bearing canonical-origin detached law from the
strong microscopic law by forgetting the explicit completion and endpoint
witness layers. -/
def toCanonicalOriginLaw
    {Index Time Carrier Law : Type}
    (data : StrongMicroscopicLaw Index Time Carrier Law) :
    CanonicalOriginLaw Index Time Carrier Law :=
  data.completionLaw.toConstructiveSectorLaw.toConstructiveMicroscopicLaw

/-- The strong microscopic law already realizes the exact constructive
microscopic target for its underlying proposition-level microscopic law. -/
theorem canonicalOriginTarget
    {Index Time Carrier Law : Type}
    (data : StrongMicroscopicLaw Index Time Carrier Law) :
    ConstructiveMicroscopicTarget data.completionLaw.toMicroscopicClosureLaw := by
  exact data.toCanonicalOriginLaw.target

/-- The strong microscopic law already forces origin closure on its own
underlying proposition-level microscopic law. -/
theorem originClosureTarget
    {Index Time Carrier Law : Type}
    (data : StrongMicroscopicLaw Index Time Carrier Law) :
    OriginClosureTarget data.completionLaw.toMicroscopicClosureLaw := by
  exact data.toCanonicalOriginLaw.originClosureTarget

/-- The strong microscopic law already forces the detached selected-bundle
surface through its canonical-origin realization. -/
theorem canonicalOriginSurface
    {Index Time Carrier Law : Type}
    (data : StrongMicroscopicLaw Index Time Carrier Law) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      realized_generator_carries_bedrock_law
        data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
      AutonomousHorizon
        data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
        data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
        data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
      horizonFiberInvariant
        data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
        data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
        data.completionLaw.toMicroscopicClosureLaw.bridge.generator := by
  simpa [LocalEventFourStateCompletionLaw.toMicroscopicClosureLaw] using
    data.toCanonicalOriginLaw.canonicalOriginSurface

/-- The strong microscopic law already forces sector closure on its own
underlying proposition-level microscopic law. -/
theorem sectorClosureTarget
    {Index Time Carrier Law : Type}
    (data : StrongMicroscopicLaw Index Time Carrier Law) :
    SectorClosureTarget data.completionLaw.toMicroscopicClosureLaw := by
  exact data.completionLaw.sectorClosureTarget

/-- The strong microscopic law already carries the no-stage completion target
on its own underlying proposition-level microscopic law. -/
theorem completionTarget
    {Index Time Carrier Law : Type}
    (data : StrongMicroscopicLaw Index Time Carrier Law) :
    NoStageCompletionTarget data.completionLaw.toMicroscopicClosureLaw := by
  exact data.completionLaw.completionTarget

/-- The strong microscopic law already realizes the exact flagship target on
its own underlying proposition-level microscopic law. -/
theorem flagshipExactTarget
    {Index Time Carrier Law : Type}
    (data : StrongMicroscopicLaw Index Time Carrier Law) :
    FlagshipExactTarget data.completionLaw.toMicroscopicClosureLaw := by
  exact LocalEventFourStateFlagshipLaw.flagshipExactTarget data

/-- The strong microscopic law already realizes the smaller recognizable
flagship target on its own underlying proposition-level microscopic law. -/
theorem flagshipRecognizableTarget
    {Index Time Carrier Law : Type}
    (data : StrongMicroscopicLaw Index Time Carrier Law) :
    FlagshipRecognizableTarget data.completionLaw.toMicroscopicClosureLaw := by
  exact LocalEventFourStateFlagshipLaw.flagshipRecognizableTarget data

/-- Target surface for the strong microscopic law. It already subsumes the
canonical-origin law, sector closure, the no-stage completion target, and the
exact and recognizable flagship targets on one same underlying microscopic
law. -/
theorem targetSurface
    {Index Time Carrier Law : Type}
    (data : StrongMicroscopicLaw Index Time Carrier Law) :
    ConstructiveMicroscopicTarget data.completionLaw.toMicroscopicClosureLaw ∧
      OriginClosureTarget data.completionLaw.toMicroscopicClosureLaw ∧
      SectorClosureTarget data.completionLaw.toMicroscopicClosureLaw ∧
      NoStageCompletionTarget data.completionLaw.toMicroscopicClosureLaw ∧
      FlagshipExactTarget data.completionLaw.toMicroscopicClosureLaw ∧
      FlagshipRecognizableTarget data.completionLaw.toMicroscopicClosureLaw := by
  exact
    ⟨data.canonicalOriginTarget,
      data.originClosureTarget,
      data.sectorClosureTarget,
      data.completionTarget,
      data.flagshipExactTarget,
      data.flagshipRecognizableTarget⟩

/-- Concrete capstone for the abstract closure-program targets, read through
the manuscript-facing strong microscopic law surface. -/
theorem fullClosureWitnessSurface
    {Index Time Carrier Law : Type}
    (data : StrongMicroscopicLaw Index Time Carrier Law) :
    ∃ witness : NoStageCompletionWitness data.completionLaw.toMicroscopicClosureLaw,
      ∃ endpointWitnesses :
          FlagshipEndpointWitnesses witness.completionLaw,
        witness.completionLaw.fourStateLaw.framed.object.bridge =
            data.completionLaw.toMicroscopicClosureLaw.bridge ∧
          witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.completionLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
          Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
          Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
          realized_generator_carries_bedrock_law
            data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
          AutonomousHorizon
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
            data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
          horizonFiberInvariant
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
            data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
          PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.phase.Field
              endpointWitnesses.phase.Scalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.wave.Field
              endpointWitnesses.wave.Scalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.gauge.Field
              endpointWitnesses.gauge.Source) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.geometric.Tensor
              endpointWitnesses.geometric.Scalar) := by
  exact LocalEventFourStateFlagshipLaw.fullClosureWitnessSurface data

/-- Concrete capstone for the sharper direct normal-form surface, read through
the manuscript-facing strong microscopic law surface. -/
theorem fullNormalFormSurface
    {Index Time Carrier Law : Type}
    (data : StrongMicroscopicLaw Index Time Carrier Law) :
    ∃ witness : NoStageCompletionWitness data.completionLaw.toMicroscopicClosureLaw,
      ∃ normalForms : FlagshipNormalForms Time Carrier Law,
        witness.completionLaw.fourStateLaw.framed.object.bridge =
            data.completionLaw.toMicroscopicClosureLaw.bridge ∧
          witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.completionLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
          Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
          Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
          realized_generator_carries_bedrock_law
            data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
          AutonomousHorizon
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
            data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
          horizonFiberInvariant
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
            data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
          PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              normalForms.PhaseField
              normalForms.PhaseScalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              normalForms.WaveField
              normalForms.WaveScalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GaugeField
              normalForms.GaugeSource) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GeometricTensor
              normalForms.GeometricScalar) := by
  exact LocalEventFourStateFlagshipLaw.fullNormalFormSurface data

end StrongMicroscopicLaw

end ClosureCurrent

end CoherenceCalculus
