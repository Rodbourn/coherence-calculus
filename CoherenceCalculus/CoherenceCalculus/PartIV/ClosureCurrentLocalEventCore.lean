import CoherenceCalculus.PartIV.ClosureCurrentEventLawCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentLocalEventCore

Detached local-event interface for the candidate closure-current lane.

`ClosureCurrentEventLawCore` packages the present detached microscopic law in
two stages: one exact exchange current law and one event exactification /
autonomy law. This file compresses that interface one step further toward the
physical statement discussed in Chapter 10.

The new input is a genuinely local event/current package, now split into two
layers:

* `MicroscopicClosureLaw` is the smaller one-law primitive: hidden exchange
  current plus local exactification/autonomy, before any selected-bundle or
  carrier-classification conclusions are built in;
* `OriginClosureWitness` is the explicit selected-bundle/readout package that
  would have to be recovered as a theorem to close the present upstream seam;
* the existing two-law detached microscopic package is then recovered from
  `MicroscopicClosureLaw` together with that explicit origin-closure witness.

Nothing here is part of the narrower bedrock-certified spine. The point is to
make the remaining microscopic theorem target smaller and more physically
legible without overstating what the active Lean spine already proves.
-/

namespace ClosureCurrent

/-- One-law microscopic closure law. This is the smaller detached primitive
below the current selected-bundle surface: one hidden exact exchange current
carried on oriented pair-comparison slots of the first closure-stable bulk
event, together with the local exactification/autonomy clauses governing its
visible readout.

No bundle-first assembly, role-indexed selected-bundle family, common
continuum-closure transport law, or intrinsic sector-generation claim is built
into this primitive. Those belong to the origin-closure theorems that still
need to be proved downstream. -/
structure MicroscopicClosureLaw (Index Time Carrier Law : Type) where
  bridge : BridgeData Index Time Carrier Law
  physicalPrinciple : PhysicalRealizationPrinciple Time Carrier Law
  sameSelectedLawAsBridge :
    physicalPrinciple.selectedLaw.selection =
      bridge.selectedBridge.observer.selection
  hiddenExactExchangeCurrent : Prop
  currentLivesOnOrientedPairSlots : Prop
  firstStableBulkEventCarriesSixSlotCurrent : Prop
  currentStockConserved : Prop
  currentDirectReturnCompatible : Prop
  relabelingEquivariant : Prop
  localLosslessExactification : Prop
  visiblePrimitiveReadoutAutonomous : Prop
  returnedDefectActsAsVisibleResidual : Prop
  hiddenExactExchangeCurrent_valid : hiddenExactExchangeCurrent
  currentLivesOnOrientedPairSlots_valid :
    currentLivesOnOrientedPairSlots
  firstStableBulkEventCarriesSixSlotCurrent_valid :
    firstStableBulkEventCarriesSixSlotCurrent
  currentStockConserved_valid : currentStockConserved
  currentDirectReturnCompatible_valid : currentDirectReturnCompatible
  relabelingEquivariant_valid : relabelingEquivariant
  localLosslessExactification_valid : localLosslessExactification
  visiblePrimitiveReadoutAutonomous_valid : visiblePrimitiveReadoutAutonomous
  returnedDefectActsAsVisibleResidual_valid :
    returnedDefectActsAsVisibleResidual

/-- Surface theorem for the smaller one-law microscopic closure package. This
is the exact current/event primitive that one would want to use as the input to
an upstream origin-closure theorem. -/
theorem MicroscopicClosureLaw.surface
    {Index Time Carrier Law : Type}
    (data : MicroscopicClosureLaw Index Time Carrier Law) :
    data.hiddenExactExchangeCurrent ∧
      data.currentLivesOnOrientedPairSlots ∧
      data.firstStableBulkEventCarriesSixSlotCurrent ∧
      data.currentStockConserved ∧
      data.currentDirectReturnCompatible ∧
      data.relabelingEquivariant ∧
      data.localLosslessExactification ∧
      data.visiblePrimitiveReadoutAutonomous ∧
      data.returnedDefectActsAsVisibleResidual := by
  exact
    ⟨data.hiddenExactExchangeCurrent_valid,
      data.currentLivesOnOrientedPairSlots_valid,
      data.firstStableBulkEventCarriesSixSlotCurrent_valid,
      data.currentStockConserved_valid,
      data.currentDirectReturnCompatible_valid,
      data.relabelingEquivariant_valid,
      data.localLosslessExactification_valid,
      data.visiblePrimitiveReadoutAutonomous_valid,
      data.returnedDefectActsAsVisibleResidual_valid⟩

/-- Explicit origin-closure witness package above one microscopic closure law.
This is not a second microscopic primitive. It is the exact selected-bundle and
role-readout data that would need to be recovered as a theorem in order to
replace the current selected-bundle seam by a genuine origin-closure theorem.
-/
structure OriginClosureWitness
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) where
  commonGrammar : CommonPartIVGrammar
  selectedObservedBundle : Prop
  sectors : BundleSectorFamily
  bundlePhysicallyRealized : Prop
  bundleSharedByAllCarriers : Prop
  sameSelectedEffectiveLawOnEachCarrier : Prop
  carrierLevelIdentificationOnlyFinalStep : Prop
  bundleArisesIntrinsicallyOnLeastMotionCut : Prop
  noCarrierWiseVisibilityHypotheses : Prop
  readsRoleOnSelectedBundle :
    VisibleCarrierRole →
      ObserverSelection.LeastMotion Time Carrier Law → Prop
  readsRoleOnSelectedBundle_sameSelection :
    ∀ role : VisibleCarrierRole,
      ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
        readsRoleOnSelectedBundle role observer →
          observer.selection = law.bridge.selectedBridge.observer.selection
  sameContinuumClosureClassOnSelectedBundle :
    ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
      observer.selection = law.bridge.selectedBridge.observer.selection →
        law.physicalPrinciple.selectedLaw.endpointClosureClass =
          observer.continuumClass
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
  bundleArisesIntrinsicallyOnLeastMotionCut_valid :
    bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses_valid :
    noCarrierWiseVisibilityHypotheses

/-- The explicit origin-closure witness already contains the entire
selected-bundle/readout surface that the current upstream theorem target still
needs to recover from the smaller microscopic closure law. -/
theorem OriginClosureWitness.surface
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : OriginClosureWitness law) :
    data.commonGrammar.hiddenCoherentLaw ∧
      data.commonGrammar.residualReturnFieldOnSelectedCut ∧
      data.commonGrammar.selectedVisibleLawPhysicallyRealized ∧
      data.commonGrammar.onlyReturnActsOnVisibleBundle ∧
      data.commonGrammar.characteristicEndpointReduction ∧
      data.commonGrammar.canonicalSectorGeneration ∧
      data.commonGrammar.symmetryRigidMinimalClosure ∧
      data.commonGrammar.carrierLevelPhysicalLaw ∧
      data.selectedObservedBundle ∧
      data.sectors.sector BundleSectorRole.phase ∧
      data.sectors.sector BundleSectorRole.wave ∧
      data.sectors.sector BundleSectorRole.kinetic ∧
      data.sectors.sector BundleSectorRole.gauge ∧
      data.sectors.sector BundleSectorRole.geometric ∧
      data.bundlePhysicallyRealized ∧
      data.bundleSharedByAllCarriers ∧
      data.sameSelectedEffectiveLawOnEachCarrier ∧
      data.carrierLevelIdentificationOnlyFinalStep ∧
      data.bundleArisesIntrinsicallyOnLeastMotionCut ∧
      data.noCarrierWiseVisibilityHypotheses := by
  exact
    ⟨data.hiddenCoherentLaw_valid,
      data.residualReturnFieldOnSelectedCut_valid,
      data.selectedVisibleLawPhysicallyRealized_valid,
      data.onlyReturnActsOnVisibleBundle_valid,
      data.characteristicEndpointReduction_valid,
      data.canonicalSectorGeneration_valid,
      data.symmetryRigidMinimalClosure_valid,
      data.carrierLevelPhysicalLaw_valid,
      data.selectedObservedBundle_valid,
      data.phaseCarrierSector_valid,
      data.waveCarrierSector_valid,
      data.kineticCarrierSector_valid,
      data.gaugeCarrierSector_valid,
      data.geometricCarrierSector_valid,
      data.bundlePhysicallyRealized_valid,
      data.bundleSharedByAllCarriers_valid,
      data.sameSelectedEffectiveLawOnEachCarrier_valid,
      data.carrierLevelIdentificationOnlyFinalStep_valid,
      data.bundleArisesIntrinsicallyOnLeastMotionCut_valid,
      data.noCarrierWiseVisibilityHypotheses_valid⟩

/-- The selected-bundle portion of the origin-closure witness. -/
def OriginClosureWitness.toBundleAssemblyLaw
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : OriginClosureWitness law) :
    BundleAssemblyLaw Time Carrier Law where
  selectedObservedBundle := data.selectedObservedBundle
  sectors := data.sectors
  physicalPrinciple := law.physicalPrinciple
  bundlePhysicallyRealized := data.bundlePhysicallyRealized
  bundleSharedByAllCarriers := data.bundleSharedByAllCarriers
  sameSelectedEffectiveLawOnEachCarrier :=
    data.sameSelectedEffectiveLawOnEachCarrier
  carrierLevelIdentificationOnlyFinalStep :=
    data.carrierLevelIdentificationOnlyFinalStep
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

/-- The role-indexed readout family extracted from the origin-closure witness.
-/
def OriginClosureWitness.toRoleReadoutFamily
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : OriginClosureWitness law) :
    RoleReadoutFamily
      Time Carrier Law
      law.bridge.selectedBridge.observer.selection where
  readsOnSelectedBundle := data.readsRoleOnSelectedBundle
  sameSelection := data.readsRoleOnSelectedBundle_sameSelection

/-- The common continuum-closure transport law extracted from the
origin-closure witness. -/
def OriginClosureWitness.toClosureClassTransport
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : OriginClosureWitness law) :
    ClosureClassTransport
      Time Carrier Law
      law.bridge.selectedBridge.observer.selection
      law.physicalPrinciple.selectedLaw.endpointClosureClass where
  sameSelection := data.sameContinuumClosureClassOnSelectedBundle

/-- Explicit intrinsic-sector witness above one microscopic closure law. This
packages the remaining non-dictionary sector-generation clauses that would need
to be recovered after origin closure but before the four carrier-side endpoint
normal-form collapses. -/
structure SectorOriginWitness
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) where
  canonicalGeneration : SelectedBundle.CanonicalGeneration
  generatedFromIntrinsicChannelAlgebra : Prop
  minimalCompatibleRealizationsOnly : Prop
  generatedFromIntrinsicChannelAlgebra_valid :
    generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly_valid :
    minimalCompatibleRealizationsOnly

/-- The intrinsic-sector witness is exactly the remaining Step 3 package sitting
above origin closure and below the carrier-side endpoint frontiers. -/
theorem SectorOriginWitness.surface
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : SectorOriginWitness law) :
    data.generatedFromIntrinsicChannelAlgebra ∧
      data.minimalCompatibleRealizationsOnly ∧
      data.canonicalGeneration.scalarChannelVisible ∧
      data.canonicalGeneration.scalarChannelGeneratesPhase ∧
      data.canonicalGeneration.scalarChannelGeneratesWave ∧
      data.canonicalGeneration.balanceCompatibleCarrierGeneratesKinetic ∧
      data.canonicalGeneration.exactOneFormExchangeGeneratesGauge ∧
      data.canonicalGeneration.symmetricResponseGeneratesGeometry ∧
      data.canonicalGeneration.notPrimitiveDictionary := by
  exact
    ⟨data.generatedFromIntrinsicChannelAlgebra_valid,
      data.minimalCompatibleRealizationsOnly_valid,
      data.canonicalGeneration.scalarChannelVisible_valid,
      data.canonicalGeneration.scalarChannelGeneratesPhase_valid,
      data.canonicalGeneration.scalarChannelGeneratesWave_valid,
      data.canonicalGeneration.balanceCompatibleCarrierGeneratesKinetic_valid,
      data.canonicalGeneration.exactOneFormExchangeGeneratesGauge_valid,
      data.canonicalGeneration.symmetricResponseGeneratesGeometry_valid,
      data.canonicalGeneration.notPrimitiveDictionary_valid⟩

/-- Detached local-event current law. This is the current-side microscopic
package stated directly on one selected local event: the hidden current lives
on oriented pair-comparison slots, the first closure-stable bulk event carries
the six-slot comparison ledger, and the visible bundle-side readouts are read
directly from that same local package. -/
structure LocalEventCurrentLaw (Index Time Carrier Law : Type) where
  bridge : BridgeData Index Time Carrier Law
  physicalPrinciple : PhysicalRealizationPrinciple Time Carrier Law
  sameSelectedLawAsBridge :
    physicalPrinciple.selectedLaw.selection =
      bridge.selectedBridge.observer.selection
  commonGrammar : CommonPartIVGrammar
  selectedObservedBundle : Prop
  sectors : BundleSectorFamily
  bundlePhysicallyRealized : Prop
  bundleSharedByAllCarriers : Prop
  sameSelectedEffectiveLawOnEachCarrier : Prop
  carrierLevelIdentificationOnlyFinalStep : Prop
  hiddenExactExchangeCurrent : Prop
  currentLivesOnOrientedPairSlots : Prop
  firstStableBulkEventCarriesSixSlotCurrent : Prop
  currentStockConserved : Prop
  currentDirectReturnCompatible : Prop
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
  hiddenExactExchangeCurrent_valid : hiddenExactExchangeCurrent
  currentLivesOnOrientedPairSlots_valid :
    currentLivesOnOrientedPairSlots
  firstStableBulkEventCarriesSixSlotCurrent_valid :
    firstStableBulkEventCarriesSixSlotCurrent
  currentStockConserved_valid : currentStockConserved
  currentDirectReturnCompatible_valid : currentDirectReturnCompatible
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

/-- The local-event current law determines the bundle-first assembly law. -/
def LocalEventCurrentLaw.toBundleAssemblyLaw
    {Index Time Carrier Law : Type}
    (data : LocalEventCurrentLaw Index Time Carrier Law) :
    BundleAssemblyLaw Time Carrier Law where
  selectedObservedBundle := data.selectedObservedBundle
  sectors := data.sectors
  physicalPrinciple := data.physicalPrinciple
  bundlePhysicallyRealized := data.bundlePhysicallyRealized
  bundleSharedByAllCarriers := data.bundleSharedByAllCarriers
  sameSelectedEffectiveLawOnEachCarrier :=
    data.sameSelectedEffectiveLawOnEachCarrier
  carrierLevelIdentificationOnlyFinalStep :=
    data.carrierLevelIdentificationOnlyFinalStep
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

/-- The local-event current law determines the role-indexed visible readout
family on the selected bundle. -/
def LocalEventCurrentLaw.toRoleReadoutFamily
    {Index Time Carrier Law : Type}
    (data : LocalEventCurrentLaw Index Time Carrier Law) :
    RoleReadoutFamily
      Time Carrier Law
      data.bridge.selectedBridge.observer.selection where
  readsOnSelectedBundle := data.readsRoleOnSelectedBundle
  sameSelection := data.readsRoleOnSelectedBundle_sameSelection

/-- The local-event current law determines the common continuum-closure
transport law on the selected cut. -/
def LocalEventCurrentLaw.toClosureClassTransport
    {Index Time Carrier Law : Type}
    (data : LocalEventCurrentLaw Index Time Carrier Law) :
    ClosureClassTransport
      Time Carrier Law
      data.bridge.selectedBridge.observer.selection
      data.physicalPrinciple.selectedLaw.endpointClosureClass where
  sameSelection := data.sameContinuumClosureClassOnSelectedBundle

/-- One smaller microscopic closure law together with an explicit
origin-closure witness recovers the current local-event current package
exactly. This does not prove origin closure; it isolates the exact selected
bundle/readout datum that an origin-closure theorem would need to supply. -/
def MicroscopicClosureLaw.toLocalEventCurrentLaw
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (witness : OriginClosureWitness law) :
    LocalEventCurrentLaw Index Time Carrier Law where
  bridge := law.bridge
  physicalPrinciple := law.physicalPrinciple
  sameSelectedLawAsBridge := law.sameSelectedLawAsBridge
  commonGrammar := witness.commonGrammar
  selectedObservedBundle := witness.selectedObservedBundle
  sectors := witness.sectors
  bundlePhysicallyRealized := witness.bundlePhysicallyRealized
  bundleSharedByAllCarriers := witness.bundleSharedByAllCarriers
  sameSelectedEffectiveLawOnEachCarrier :=
    witness.sameSelectedEffectiveLawOnEachCarrier
  carrierLevelIdentificationOnlyFinalStep :=
    witness.carrierLevelIdentificationOnlyFinalStep
  hiddenExactExchangeCurrent := law.hiddenExactExchangeCurrent
  currentLivesOnOrientedPairSlots := law.currentLivesOnOrientedPairSlots
  firstStableBulkEventCarriesSixSlotCurrent :=
    law.firstStableBulkEventCarriesSixSlotCurrent
  currentStockConserved := law.currentStockConserved
  currentDirectReturnCompatible := law.currentDirectReturnCompatible
  readsRoleOnSelectedBundle := witness.readsRoleOnSelectedBundle
  readsRoleOnSelectedBundle_sameSelection :=
    witness.readsRoleOnSelectedBundle_sameSelection
  sameContinuumClosureClassOnSelectedBundle :=
    witness.sameContinuumClosureClassOnSelectedBundle
  selectedObservedBundle_valid := witness.selectedObservedBundle_valid
  phaseCarrierSector_valid := witness.phaseCarrierSector_valid
  waveCarrierSector_valid := witness.waveCarrierSector_valid
  kineticCarrierSector_valid := witness.kineticCarrierSector_valid
  gaugeCarrierSector_valid := witness.gaugeCarrierSector_valid
  geometricCarrierSector_valid := witness.geometricCarrierSector_valid
  bundlePhysicallyRealized_valid := witness.bundlePhysicallyRealized_valid
  bundleSharedByAllCarriers_valid := witness.bundleSharedByAllCarriers_valid
  sameSelectedEffectiveLawOnEachCarrier_valid :=
    witness.sameSelectedEffectiveLawOnEachCarrier_valid
  carrierLevelIdentificationOnlyFinalStep_valid :=
    witness.carrierLevelIdentificationOnlyFinalStep_valid
  hiddenExactExchangeCurrent_valid := law.hiddenExactExchangeCurrent_valid
  currentLivesOnOrientedPairSlots_valid :=
    law.currentLivesOnOrientedPairSlots_valid
  firstStableBulkEventCarriesSixSlotCurrent_valid :=
    law.firstStableBulkEventCarriesSixSlotCurrent_valid
  currentStockConserved_valid := law.currentStockConserved_valid
  currentDirectReturnCompatible_valid :=
    law.currentDirectReturnCompatible_valid
  hiddenCoherentLaw_valid := witness.hiddenCoherentLaw_valid
  residualReturnFieldOnSelectedCut_valid :=
    witness.residualReturnFieldOnSelectedCut_valid
  selectedVisibleLawPhysicallyRealized_valid :=
    witness.selectedVisibleLawPhysicallyRealized_valid
  onlyReturnActsOnVisibleBundle_valid :=
    witness.onlyReturnActsOnVisibleBundle_valid
  characteristicEndpointReduction_valid :=
    witness.characteristicEndpointReduction_valid
  canonicalSectorGeneration_valid :=
    witness.canonicalSectorGeneration_valid
  symmetryRigidMinimalClosure_valid :=
    witness.symmetryRigidMinimalClosure_valid
  carrierLevelPhysicalLaw_valid :=
    witness.carrierLevelPhysicalLaw_valid

/-- The current-side local-event surface is already a consequence of one smaller
microscopic closure law plus the explicit origin-closure witness. -/
theorem MicroscopicClosureLaw.currentSurface
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (witness : OriginClosureWitness law) :
    law.hiddenExactExchangeCurrent ∧
      law.currentLivesOnOrientedPairSlots ∧
      law.firstStableBulkEventCarriesSixSlotCurrent ∧
      law.currentStockConserved ∧
      law.currentDirectReturnCompatible ∧
      witness.commonGrammar.hiddenCoherentLaw ∧
      witness.commonGrammar.residualReturnFieldOnSelectedCut ∧
      witness.commonGrammar.selectedVisibleLawPhysicallyRealized ∧
      witness.commonGrammar.onlyReturnActsOnVisibleBundle ∧
      witness.commonGrammar.characteristicEndpointReduction ∧
      witness.commonGrammar.canonicalSectorGeneration ∧
      witness.commonGrammar.symmetryRigidMinimalClosure ∧
      witness.commonGrammar.carrierLevelPhysicalLaw := by
  exact
    ⟨law.hiddenExactExchangeCurrent_valid,
      law.currentLivesOnOrientedPairSlots_valid,
      law.firstStableBulkEventCarriesSixSlotCurrent_valid,
      law.currentStockConserved_valid,
      law.currentDirectReturnCompatible_valid,
      witness.hiddenCoherentLaw_valid,
      witness.residualReturnFieldOnSelectedCut_valid,
      witness.selectedVisibleLawPhysicallyRealized_valid,
      witness.onlyReturnActsOnVisibleBundle_valid,
      witness.characteristicEndpointReduction_valid,
      witness.canonicalSectorGeneration_valid,
      witness.symmetryRigidMinimalClosure_valid,
      witness.carrierLevelPhysicalLaw_valid⟩

/-- The local-event current law recovers the detached exact exchange current
law. -/
def LocalEventCurrentLaw.toExactExchangeCurrentLaw
    {Index Time Carrier Law : Type}
    (data : LocalEventCurrentLaw Index Time Carrier Law) :
    ExactExchangeCurrentLaw Index Time Carrier Law where
  bridge := data.bridge
  assembly := data.toBundleAssemblyLaw
  sameSelectedLawAsBridge := data.sameSelectedLawAsBridge
  commonGrammar := data.commonGrammar
  hiddenExactExchangeCurrent := data.hiddenExactExchangeCurrent
  currentStockConserved := data.currentStockConserved
  currentDirectReturnCompatible := data.currentDirectReturnCompatible
  roleReadout := data.toRoleReadoutFamily
  continuumClosure := data.toClosureClassTransport
  hiddenExactExchangeCurrent_valid := data.hiddenExactExchangeCurrent_valid
  currentStockConserved_valid := data.currentStockConserved_valid
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

/-- Surface theorem for the local-event current law. It records the local
pair-slot interpretation and shows that the existing detached exact exchange
current law is already recovered from this smaller interface. -/
theorem LocalEventCurrentLaw.surface
    {Index Time Carrier Law : Type}
    (data : LocalEventCurrentLaw Index Time Carrier Law) :
    data.hiddenExactExchangeCurrent ∧
      data.currentLivesOnOrientedPairSlots ∧
      data.firstStableBulkEventCarriesSixSlotCurrent ∧
      data.currentStockConserved ∧
      data.currentDirectReturnCompatible ∧
      data.commonGrammar.hiddenCoherentLaw ∧
      data.commonGrammar.residualReturnFieldOnSelectedCut ∧
      data.commonGrammar.selectedVisibleLawPhysicallyRealized ∧
      data.commonGrammar.onlyReturnActsOnVisibleBundle ∧
      data.commonGrammar.characteristicEndpointReduction ∧
      data.commonGrammar.canonicalSectorGeneration ∧
      data.commonGrammar.symmetryRigidMinimalClosure ∧
      data.commonGrammar.carrierLevelPhysicalLaw := by
  exact
    ⟨data.hiddenExactExchangeCurrent_valid,
      data.currentLivesOnOrientedPairSlots_valid,
      data.firstStableBulkEventCarriesSixSlotCurrent_valid,
      data.currentStockConserved_valid,
      data.currentDirectReturnCompatible_valid,
      data.hiddenCoherentLaw_valid,
      data.residualReturnFieldOnSelectedCut_valid,
      data.selectedVisibleLawPhysicallyRealized_valid,
      data.onlyReturnActsOnVisibleBundle_valid,
      data.characteristicEndpointReduction_valid,
      data.canonicalSectorGeneration_valid,
      data.symmetryRigidMinimalClosure_valid,
      data.carrierLevelPhysicalLaw_valid⟩

/-- Detached local-event exactification/autonomy law. This adds the event-side
exactification clauses to the local pair-exchange current package. -/
structure LocalEventExactificationLaw (Index Time Carrier Law : Type)
    extends LocalEventCurrentLaw Index Time Carrier Law where
  relabelingEquivariant : Prop
  localLosslessExactification : Prop
  visiblePrimitiveReadoutAutonomous : Prop
  returnedDefectActsAsVisibleResidual : Prop
  bundleArisesIntrinsicallyOnLeastMotionCut : Prop
  noCarrierWiseVisibilityHypotheses : Prop
  relabelingEquivariant_valid : relabelingEquivariant
  localLosslessExactification_valid : localLosslessExactification
  visiblePrimitiveReadoutAutonomous_valid : visiblePrimitiveReadoutAutonomous
  returnedDefectActsAsVisibleResidual_valid :
    returnedDefectActsAsVisibleResidual
  bundleArisesIntrinsicallyOnLeastMotionCut_valid :
    bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses_valid :
    noCarrierWiseVisibilityHypotheses

/-- The local-event exactification law recovers the detached event
exactification/autonomy law. -/
def LocalEventExactificationLaw.toEventExactificationLaw
    {Index Time Carrier Law : Type}
    (data : LocalEventExactificationLaw Index Time Carrier Law) :
    EventExactificationLaw Index Time Carrier Law where
  toExactExchangeCurrentLaw :=
    data.toLocalEventCurrentLaw.toExactExchangeCurrentLaw
  relabelingEquivariant := data.relabelingEquivariant
  localLosslessExactification := data.localLosslessExactification
  visiblePrimitiveReadoutAutonomous :=
    data.visiblePrimitiveReadoutAutonomous
  returnedDefectActsAsVisibleResidual :=
    data.returnedDefectActsAsVisibleResidual
  bundleArisesIntrinsicallyOnLeastMotionCut :=
    data.bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses :=
    data.noCarrierWiseVisibilityHypotheses
  relabelingEquivariant_valid := data.relabelingEquivariant_valid
  localLosslessExactification_valid :=
    data.localLosslessExactification_valid
  visiblePrimitiveReadoutAutonomous_valid :=
    data.visiblePrimitiveReadoutAutonomous_valid
  returnedDefectActsAsVisibleResidual_valid :=
    data.returnedDefectActsAsVisibleResidual_valid
  bundleArisesIntrinsicallyOnLeastMotionCut_valid :=
    data.bundleArisesIntrinsicallyOnLeastMotionCut_valid
  noCarrierWiseVisibilityHypotheses_valid :=
    data.noCarrierWiseVisibilityHypotheses_valid

/-- One smaller microscopic closure law together with an explicit
origin-closure witness recovers the current local-event exactification package
exactly. The only additional data beyond the smaller law are the selected-bundle
and readout surfaces recorded in that witness. -/
def MicroscopicClosureLaw.toLocalEventExactificationLaw
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (witness : OriginClosureWitness law) :
    LocalEventExactificationLaw Index Time Carrier Law where
  toLocalEventCurrentLaw := law.toLocalEventCurrentLaw witness
  relabelingEquivariant := law.relabelingEquivariant
  localLosslessExactification := law.localLosslessExactification
  visiblePrimitiveReadoutAutonomous :=
    law.visiblePrimitiveReadoutAutonomous
  returnedDefectActsAsVisibleResidual :=
    law.returnedDefectActsAsVisibleResidual
  bundleArisesIntrinsicallyOnLeastMotionCut :=
    witness.bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses :=
    witness.noCarrierWiseVisibilityHypotheses
  relabelingEquivariant_valid := law.relabelingEquivariant_valid
  localLosslessExactification_valid :=
    law.localLosslessExactification_valid
  visiblePrimitiveReadoutAutonomous_valid :=
    law.visiblePrimitiveReadoutAutonomous_valid
  returnedDefectActsAsVisibleResidual_valid :=
    law.returnedDefectActsAsVisibleResidual_valid
  bundleArisesIntrinsicallyOnLeastMotionCut_valid :=
    witness.bundleArisesIntrinsicallyOnLeastMotionCut_valid
  noCarrierWiseVisibilityHypotheses_valid :=
    witness.noCarrierWiseVisibilityHypotheses_valid

/-- The selected-bundle surface recovered by the existing local-event
exactification package is already a consequence of one smaller microscopic
closure law plus the explicit origin-closure witness. -/
theorem MicroscopicClosureLaw.originClosureSurface
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (witness : OriginClosureWitness law) :
    law.hiddenExactExchangeCurrent ∧
      law.currentLivesOnOrientedPairSlots ∧
      law.firstStableBulkEventCarriesSixSlotCurrent ∧
      law.currentStockConserved ∧
      law.currentDirectReturnCompatible ∧
      law.relabelingEquivariant ∧
      law.localLosslessExactification ∧
      law.visiblePrimitiveReadoutAutonomous ∧
      law.returnedDefectActsAsVisibleResidual ∧
      Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      realized_generator_carries_bedrock_law law.bridge.generator ∧
      AutonomousHorizon
        law.bridge.selectedBridge.observer.selection.realization.tower
        law.bridge.selectedBridge.observer.selection.horizon
        law.bridge.generator ∧
      horizonFiberInvariant
        law.bridge.selectedBridge.observer.selection.realization.tower
        law.bridge.selectedBridge.observer.selection.horizon
        law.bridge.generator ∧
      (∀ role : VisibleCarrierRole,
        ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
          witness.readsRoleOnSelectedBundle role observer →
            (law.physicalPrinciple.selectedLaw.selection =
              observer.selection) ∧
            exactVisibleOnCut
              (observer.selection.realization.tower.π observer.selection.horizon)
              (selected_observed_law observer.selection).op ∧
            ForcedContinuumLaw
              observer.continuumClass
              law.physicalPrinciple.selectedLaw.selectedClosureLaw) := by
  obtain ⟨hcurrent, hstock, hdirret, hrel, hexact, hautread, hdefect,
    _hhidden, _hreturn, _hvislaw, _honlyReturn, hbundle, hbedrock, haut, hfiber,
    hreadout⟩ :=
    (law.toLocalEventExactificationLaw witness).toEventExactificationLaw.surface
  have hreadout' :
      ∀ role : VisibleCarrierRole,
        ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
          witness.readsRoleOnSelectedBundle role observer →
            (law.physicalPrinciple.selectedLaw.selection =
              observer.selection) ∧
            exactVisibleOnCut
              (observer.selection.realization.tower.π observer.selection.horizon)
              (selected_observed_law observer.selection).op ∧
            ForcedContinuumLaw
              observer.continuumClass
              law.physicalPrinciple.selectedLaw.selectedClosureLaw := by
    intro role observer hrole
    exact hreadout role observer hrole
  exact
    ⟨hcurrent,
      law.currentLivesOnOrientedPairSlots_valid,
      law.firstStableBulkEventCarriesSixSlotCurrent_valid,
      hstock,
      hdirret,
      hrel,
      hexact,
      hautread,
      hdefect,
      hbundle,
      hbedrock,
      haut,
      hfiber,
      hreadout'⟩

/-- Surface theorem for the local-event exactification/autonomy law. The
selected-bundle surface recovered by the existing two-law package is already a
consequence of this smaller local event/current interface. -/
theorem LocalEventExactificationLaw.surface
    {Index Time Carrier Law : Type}
    (data : LocalEventExactificationLaw Index Time Carrier Law) :
    data.hiddenExactExchangeCurrent ∧
      data.currentLivesOnOrientedPairSlots ∧
      data.firstStableBulkEventCarriesSixSlotCurrent ∧
      data.currentStockConserved ∧
      data.currentDirectReturnCompatible ∧
      data.relabelingEquivariant ∧
      data.localLosslessExactification ∧
      data.visiblePrimitiveReadoutAutonomous ∧
      data.returnedDefectActsAsVisibleResidual ∧
      Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      realized_generator_carries_bedrock_law data.bridge.generator ∧
      AutonomousHorizon
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator ∧
      horizonFiberInvariant
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator ∧
      (∀ role : VisibleCarrierRole,
        ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
          data.readsRoleOnSelectedBundle role observer →
            (data.physicalPrinciple.selectedLaw.selection =
              observer.selection) ∧
            exactVisibleOnCut
              (observer.selection.realization.tower.π observer.selection.horizon)
              (selected_observed_law observer.selection).op ∧
            ForcedContinuumLaw
              observer.continuumClass
              data.physicalPrinciple.selectedLaw.selectedClosureLaw) := by
  obtain ⟨hcurrent, hslots, hsix, hstock, hdirret, _hhidden, _hreturn, _hvis,
    _honly, _hchar, _hcanon, _hsymm, _hcarrier⟩ :=
    data.toLocalEventCurrentLaw.surface
  obtain ⟨_hcurrent', _hstock', _hdirret', hrel, hexact, hautread, hdefect,
    _hhidden', _hreturn', _hvis', _honly', hbundle, hbedrock, haut, hfiber,
    hreadout⟩ := data.toEventExactificationLaw.surface
  exact
    ⟨hcurrent,
      hslots,
      hsix,
      hstock,
      hdirret,
      hrel,
      hexact,
      hautread,
      hdefect,
      hbundle,
      hbedrock,
      haut,
      hfiber,
      hreadout⟩

/-- Detached local-event exactification law together with the intrinsic
non-dictionary sector-generation clauses needed to close the current forcing
seam. -/
structure LocalEventSectorLaw (Index Time Carrier Law : Type)
    extends LocalEventExactificationLaw Index Time Carrier Law where
  canonicalGeneration : SelectedBundle.CanonicalGeneration
  generatedFromIntrinsicChannelAlgebra : Prop
  minimalCompatibleRealizationsOnly : Prop
  generatedFromIntrinsicChannelAlgebra_valid :
    generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly_valid :
    minimalCompatibleRealizationsOnly

/-- The local-event sector law recovers the detached event exactification /
sector law. -/
def LocalEventSectorLaw.toEventExactificationSectorLaw
    {Index Time Carrier Law : Type}
    (data : LocalEventSectorLaw Index Time Carrier Law) :
    EventExactificationSectorLaw Index Time Carrier Law where
  toEventExactificationLaw :=
    data.toLocalEventExactificationLaw.toEventExactificationLaw
  canonicalGeneration := data.canonicalGeneration
  generatedFromIntrinsicChannelAlgebra :=
    data.generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly :=
    data.minimalCompatibleRealizationsOnly
  generatedFromIntrinsicChannelAlgebra_valid :=
    data.generatedFromIntrinsicChannelAlgebra_valid
  minimalCompatibleRealizationsOnly_valid :=
    data.minimalCompatibleRealizationsOnly_valid

/-- One smaller microscopic closure law together with the explicit origin-
closure and intrinsic-sector witnesses recovers the current local-event sector
law exactly. This isolates the remaining upstream theorem target into:
microscopic primitive, origin closure, and non-dictionary sector generation. -/
def MicroscopicClosureLaw.toLocalEventSectorLaw
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (origin : OriginClosureWitness law)
    (sector : SectorOriginWitness law) :
    LocalEventSectorLaw Index Time Carrier Law where
  toLocalEventExactificationLaw := law.toLocalEventExactificationLaw origin
  canonicalGeneration := sector.canonicalGeneration
  generatedFromIntrinsicChannelAlgebra :=
    sector.generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly :=
    sector.minimalCompatibleRealizationsOnly
  generatedFromIntrinsicChannelAlgebra_valid :=
    sector.generatedFromIntrinsicChannelAlgebra_valid
  minimalCompatibleRealizationsOnly_valid :=
    sector.minimalCompatibleRealizationsOnly_valid

/-- The current Step 3 surface is already a consequence of one smaller
microscopic closure law plus explicit origin-closure and sector-generation
witnesses. This is the precise theorem shape needed to replace the present
composite primitive by a genuine origin-closure result. -/
theorem MicroscopicClosureLaw.sectorClosureSurface
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (origin : OriginClosureWitness law)
    (sector : SectorOriginWitness law) :
    law.hiddenExactExchangeCurrent ∧
      law.currentLivesOnOrientedPairSlots ∧
      law.firstStableBulkEventCarriesSixSlotCurrent ∧
      law.currentStockConserved ∧
      law.currentDirectReturnCompatible ∧
      law.relabelingEquivariant ∧
      law.localLosslessExactification ∧
      law.visiblePrimitiveReadoutAutonomous ∧
      law.returnedDefectActsAsVisibleResidual ∧
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
      (∀ role : VisibleCarrierRole,
        ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
          origin.readsRoleOnSelectedBundle role observer →
            (law.physicalPrinciple.selectedLaw.selection =
              observer.selection) ∧
            exactVisibleOnCut
              (observer.selection.realization.tower.π observer.selection.horizon)
              (selected_observed_law observer.selection).op ∧
            ForcedContinuumLaw
              observer.continuumClass
              law.physicalPrinciple.selectedLaw.selectedClosureLaw) ∧
      sector.generatedFromIntrinsicChannelAlgebra ∧
      sector.minimalCompatibleRealizationsOnly ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  obtain ⟨hcurrent, hstock, hdirret, hrel, hexact, hautread, hdefect, hbundle,
    hsector, hbedrock, haut, hfiber, hreadout, hgen, hmin, hprofile⟩ :=
    (law.toLocalEventSectorLaw origin sector).toEventExactificationSectorLaw.surface
  have hreadout' :
      ∀ role : VisibleCarrierRole,
        ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
          origin.readsRoleOnSelectedBundle role observer →
            (law.physicalPrinciple.selectedLaw.selection =
              observer.selection) ∧
            exactVisibleOnCut
              (observer.selection.realization.tower.π observer.selection.horizon)
              (selected_observed_law observer.selection).op ∧
            ForcedContinuumLaw
              observer.continuumClass
              law.physicalPrinciple.selectedLaw.selectedClosureLaw := by
    intro role observer hrole
    exact hreadout role observer hrole
  exact
    ⟨hcurrent,
      law.currentLivesOnOrientedPairSlots_valid,
      law.firstStableBulkEventCarriesSixSlotCurrent_valid,
      hstock,
      hdirret,
      hrel,
      hexact,
      hautread,
      hdefect,
      hbundle,
      hsector,
      hbedrock,
      haut,
      hfiber,
      hreadout',
      hgen,
      hmin,
      hprofile⟩

/-- Surface theorem for the local-event sector law. The smaller local
event/current package plus the intrinsic sector clauses already closes the
current forcing seam. -/
theorem LocalEventSectorLaw.surface
    {Index Time Carrier Law : Type}
    (data : LocalEventSectorLaw Index Time Carrier Law) :
    data.hiddenExactExchangeCurrent ∧
      data.currentLivesOnOrientedPairSlots ∧
      data.firstStableBulkEventCarriesSixSlotCurrent ∧
      data.currentStockConserved ∧
      data.currentDirectReturnCompatible ∧
      data.relabelingEquivariant ∧
      data.localLosslessExactification ∧
      data.visiblePrimitiveReadoutAutonomous ∧
      data.returnedDefectActsAsVisibleResidual ∧
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
      (∀ role : VisibleCarrierRole,
        ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
          data.readsRoleOnSelectedBundle role observer →
            (data.physicalPrinciple.selectedLaw.selection =
              observer.selection) ∧
            exactVisibleOnCut
              (observer.selection.realization.tower.π observer.selection.horizon)
              (selected_observed_law observer.selection).op ∧
            ForcedContinuumLaw
              observer.continuumClass
              data.physicalPrinciple.selectedLaw.selectedClosureLaw) ∧
      data.generatedFromIntrinsicChannelAlgebra ∧
      data.minimalCompatibleRealizationsOnly ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  obtain ⟨hcurrent, hslots, hsix, hstock, hdirret, hrel, hexact, hautread,
    hdefect, hbundle, _hbedrock, haut, hfiber, hreadout⟩ :=
    data.toLocalEventExactificationLaw.surface
  obtain ⟨_hcurrent', _hstock', _hdirret', _hrel', _hexact', _hautread',
    _hdefect', _hbundle', hsector, hbedrock, _haut', _hfiber', _hreadout',
    hgen, hmin, hprofile⟩ := data.toEventExactificationSectorLaw.surface
  exact
    ⟨hcurrent,
      hslots,
      hsix,
      hstock,
      hdirret,
      hrel,
      hexact,
      hautread,
      hdefect,
      hbundle,
      hsector,
      hbedrock,
      haut,
      hfiber,
      hreadout,
      hgen,
      hmin,
      hprofile⟩

end ClosureCurrent

end CoherenceCalculus
