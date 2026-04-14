import CoherenceCalculus.PartIV.ClosureCurrentBridgeCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentForcingCore

Detached forcing interface for the candidate closure-current law.

This file records the exact additional microscopic-law hypotheses that would
be sufficient to build the active Part IV selected-bundle and
intrinsic-sector-generation packages. Nothing here claims those hypotheses are
already forced from the bedrock-certified spine. The point is to make the
remaining upstream work completely explicit:

* `SelectedBundleForcing` is the minimal bundle-readout package sitting above
  the detached closure-current bridge.
* `IntrinsicSectorForcing` adds the non-dictionary intrinsic sector-generation
  hypotheses needed to recover the active Step 3 surface.

The downstream theorem surfaces are then honest constructor-level bridges into
`IntrinsicSelectedBundleExistence` and `IntrinsicSectorGeneration`.
-/

namespace ClosureCurrent

/-- Generic selected-bundle readout for one visible carrier family. The only
microscopic content stored here is that any observer read on the carrier is
already reading the same selected cut as the bridge datum. -/
structure CarrierReadout
    (Time Carrier Law : Type)
    (selection : SelectionDatum Time) where
  readsOnSelectedBundle :
    ObserverSelection.LeastMotion Time Carrier Law → Prop
  sameSelection :
    ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
      readsOnSelectedBundle observer →
        observer.selection = selection

/-- The closure-class inheritance law on one common selected cut. This is the
bundle-level transport statement needed to recover the active carrier closure
readout theorem without reintroducing lane-specific closure hypotheses. -/
structure ClosureClassTransport
    (Time Carrier Law : Type)
    (selection : SelectionDatum Time)
    (endpointClosureClass : ContinuumLimitClass Law) where
  sameSelection :
    ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
      observer.selection = selection →
        endpointClosureClass = observer.continuumClass

/-- Microscopic readout package above one selected cut: four visible carrier
families are read on the same selected bundle, and the induced continuum
closure class transports uniformly along that same selection. -/
structure BundleReadout
    (Time Carrier Law : Type)
    (selection : SelectionDatum Time)
    (endpointClosureClass : ContinuumLimitClass Law) where
  phase : CarrierReadout Time Carrier Law selection
  wave : CarrierReadout Time Carrier Law selection
  gauge : CarrierReadout Time Carrier Law selection
  geometric : CarrierReadout Time Carrier Law selection
  continuumClosure :
    ClosureClassTransport Time Carrier Law selection endpointClosureClass
  bundleArisesIntrinsicallyOnLeastMotionCut : Prop
  noCarrierWiseVisibilityHypotheses : Prop
  bundleArisesIntrinsicallyOnLeastMotionCut_valid :
    bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses_valid :
    noCarrierWiseVisibilityHypotheses

/-- Any observer read from a selected-bundle carrier family inherits the same
selected cut as the bridge datum. -/
theorem CarrierReadout.selection
    {Time Carrier Law : Type}
    {selection : SelectionDatum Time}
    (data : CarrierReadout Time Carrier Law selection)
    (observer : ObserverSelection.LeastMotion Time Carrier Law)
    (hread : data.readsOnSelectedBundle observer) :
    observer.selection = selection := by
  exact data.sameSelection observer hread

/-- The closure-class transport package says exactly that the selected-law
continuum class is inherited by every observer reading the same selected cut. -/
theorem ClosureClassTransport.surface
    {Time Carrier Law : Type}
    {selection : SelectionDatum Time}
    {endpointClosureClass : ContinuumLimitClass Law}
    (data :
      ClosureClassTransport
        Time Carrier Law selection endpointClosureClass)
    (observer : ObserverSelection.LeastMotion Time Carrier Law)
    (hselection : observer.selection = selection) :
    endpointClosureClass = observer.continuumClass := by
  exact data.sameSelection observer hselection

/-- The microscopic bundle-readout package unpacks to the four carrier readout
families together with uniform continuum-closure inheritance on the common
selected cut. -/
theorem BundleReadout.surface
    {Time Carrier Law : Type}
    {selection : SelectionDatum Time}
    {endpointClosureClass : ContinuumLimitClass Law}
    (data : BundleReadout Time Carrier Law selection endpointClosureClass) :
    data.bundleArisesIntrinsicallyOnLeastMotionCut ∧
      data.noCarrierWiseVisibilityHypotheses := by
  exact
    ⟨data.bundleArisesIntrinsicallyOnLeastMotionCut_valid,
      data.noCarrierWiseVisibilityHypotheses_valid⟩

/-- Minimal bundle-readout data above the detached closure-current bridge. This
packages exactly the extra hypotheses needed to recover the active
`IntrinsicSelectedBundleExistence` surface. -/
structure SelectedBundleForcing (Index Time Carrier Law : Type) where
  bridge : BridgeData Index Time Carrier Law
  assembly : SelectedBundle.Assembly Time Carrier Law
  sameSelectedLawAsBridge :
    assembly.physicalPrinciple.selectedLaw.selection =
      bridge.selectedBridge.observer.selection
  readout :
    BundleReadout
      Time Carrier Law
      bridge.selectedBridge.observer.selection
      assembly.physicalPrinciple.selectedLaw.endpointClosureClass

/-- The detached bundle-readout package builds the active
`IntrinsicSelectedBundleExistence` datum with no hidden extra assumptions. -/
def SelectedBundleForcing.toIntrinsicSelectedBundleExistence
    {Index Time Carrier Law : Type}
    (data : SelectedBundleForcing Index Time Carrier Law) :
    IntrinsicSelectedBundleExistence Time Carrier Law :=
  { selectedObservedBundle := data.assembly.selectedObservedBundle
    phaseCarrierSector := data.assembly.phaseCarrierSector
    waveCarrierSector := data.assembly.waveCarrierSector
    kineticCarrierSector := data.assembly.kineticCarrierSector
    gaugeCarrierSector := data.assembly.gaugeCarrierSector
    geometricCarrierSector := data.assembly.geometricCarrierSector
    physicalPrinciple := data.assembly.physicalPrinciple
    bundlePhysicallyRealized := data.assembly.bundlePhysicallyRealized
    bundleSharedByAllCarriers := data.assembly.bundleSharedByAllCarriers
    sameSelectedEffectiveLawOnEachCarrier :=
      data.assembly.sameSelectedEffectiveLawOnEachCarrier
    carrierLevelIdentificationOnlyFinalStep :=
      data.assembly.carrierLevelIdentificationOnlyFinalStep
    selectedObservedBundle_valid := data.assembly.selectedObservedBundle_valid
    phaseCarrierSector_valid := data.assembly.phaseCarrierSector_valid
    waveCarrierSector_valid := data.assembly.waveCarrierSector_valid
    kineticCarrierSector_valid := data.assembly.kineticCarrierSector_valid
    gaugeCarrierSector_valid := data.assembly.gaugeCarrierSector_valid
    geometricCarrierSector_valid := data.assembly.geometricCarrierSector_valid
    bundlePhysicallyRealized_valid := data.assembly.bundlePhysicallyRealized_valid
    bundleSharedByAllCarriers_valid := data.assembly.bundleSharedByAllCarriers_valid
    sameSelectedEffectiveLawOnEachCarrier_valid :=
      data.assembly.sameSelectedEffectiveLawOnEachCarrier_valid
    carrierLevelIdentificationOnlyFinalStep_valid :=
      data.assembly.carrierLevelIdentificationOnlyFinalStep_valid
    Index := Index
    selectedSchurBridge := data.bridge.selectedBridge
    sameSelectedLawAsSchurBridge := data.sameSelectedLawAsBridge
    phaseCarrierReadOnSelectedBundle := data.readout.phase.readsOnSelectedBundle
    waveCarrierReadOnSelectedBundle := data.readout.wave.readsOnSelectedBundle
    gaugeCarrierReadOnSelectedBundle := data.readout.gauge.readsOnSelectedBundle
    geometricCarrierReadOnSelectedBundle :=
      data.readout.geometric.readsOnSelectedBundle
    phaseCarrierReadOnSelectedBundle_sameSelection :=
      data.readout.phase.sameSelection
    waveCarrierReadOnSelectedBundle_sameSelection :=
      data.readout.wave.sameSelection
    gaugeCarrierReadOnSelectedBundle_sameSelection :=
      data.readout.gauge.sameSelection
    geometricCarrierReadOnSelectedBundle_sameSelection :=
      data.readout.geometric.sameSelection
    sameContinuumClosureClassOnSelectedBundle :=
      data.readout.continuumClosure.sameSelection
    bundleArisesIntrinsicallyOnLeastMotionCut :=
      data.readout.bundleArisesIntrinsicallyOnLeastMotionCut
    noCarrierWiseVisibilityHypotheses :=
      data.readout.noCarrierWiseVisibilityHypotheses
    bundleArisesIntrinsicallyOnLeastMotionCut_valid :=
      data.readout.bundleArisesIntrinsicallyOnLeastMotionCut_valid
    noCarrierWiseVisibilityHypotheses_valid :=
      data.readout.noCarrierWiseVisibilityHypotheses_valid }

/-- Any carrier observer read from the detached microscopic selected-bundle
surface already inherits the selected physical law, exact visibility on the
selected cut, and the forced continuum singleton. This is the generic bridge
from the new microscopic readout interface to the active carrier closure
readout theorem. -/
theorem SelectedBundleForcing.carrierClosureReadout
    {Index Time Carrier Law : Type}
    (data : SelectedBundleForcing Index Time Carrier Law)
    (carrier : CarrierReadout
      Time Carrier Law data.bridge.selectedBridge.observer.selection)
    (observer : ObserverSelection.LeastMotion Time Carrier Law)
    (hread : carrier.readsOnSelectedBundle observer) :
    (data.assembly.physicalPrinciple.selectedLaw.selection =
      observer.selection) ∧
      exactVisibleOnCut
        (observer.selection.realization.tower.π observer.selection.horizon)
        (selected_observed_law observer.selection).op ∧
      ForcedContinuumLaw
        observer.continuumClass
        data.assembly.physicalPrinciple.selectedLaw.selectedClosureLaw := by
  have hselection :
      observer.selection = data.bridge.selectedBridge.observer.selection := by
    exact carrier.sameSelection observer hread
  have hphysicalSelection :
      data.assembly.physicalPrinciple.selectedLaw.selection =
        observer.selection := by
    calc
      data.assembly.physicalPrinciple.selectedLaw.selection
          = data.bridge.selectedBridge.observer.selection := data.sameSelectedLawAsBridge
      _ = observer.selection := by
            symm
            exact hselection
  have hclosure :
      data.assembly.physicalPrinciple.selectedLaw.endpointClosureClass =
        observer.continuumClass := by
    exact data.readout.continuumClosure.sameSelection observer hselection
  exact
    SelectedCut.carrierClosureReadout
      { physical := data.assembly.physicalPrinciple
        observer := observer
        sameSelectionDatum := hphysicalSelection
        sameContinuumClosureClass := hclosure }

/-- Phase observers read from the detached microscopic bundle surface inherit
the exact carrier closure readout package automatically. -/
theorem SelectedBundleForcing.phaseClosureReadout
    {Index Time Carrier Law : Type}
    (data : SelectedBundleForcing Index Time Carrier Law)
    (observer : ObserverSelection.LeastMotion Time Carrier Law)
    (hread : data.readout.phase.readsOnSelectedBundle observer) :
    (data.assembly.physicalPrinciple.selectedLaw.selection =
      observer.selection) ∧
      exactVisibleOnCut
        (observer.selection.realization.tower.π observer.selection.horizon)
        (selected_observed_law observer.selection).op ∧
      ForcedContinuumLaw
        observer.continuumClass
        data.assembly.physicalPrinciple.selectedLaw.selectedClosureLaw := by
  exact carrierClosureReadout data data.readout.phase observer hread

/-- Wave observers read from the detached microscopic bundle surface inherit
the exact carrier closure readout package automatically. -/
theorem SelectedBundleForcing.waveClosureReadout
    {Index Time Carrier Law : Type}
    (data : SelectedBundleForcing Index Time Carrier Law)
    (observer : ObserverSelection.LeastMotion Time Carrier Law)
    (hread : data.readout.wave.readsOnSelectedBundle observer) :
    (data.assembly.physicalPrinciple.selectedLaw.selection =
      observer.selection) ∧
      exactVisibleOnCut
        (observer.selection.realization.tower.π observer.selection.horizon)
        (selected_observed_law observer.selection).op ∧
      ForcedContinuumLaw
        observer.continuumClass
        data.assembly.physicalPrinciple.selectedLaw.selectedClosureLaw := by
  exact carrierClosureReadout data data.readout.wave observer hread

/-- Gauge observers read from the detached microscopic bundle surface inherit
the exact carrier closure readout package automatically. -/
theorem SelectedBundleForcing.gaugeClosureReadout
    {Index Time Carrier Law : Type}
    (data : SelectedBundleForcing Index Time Carrier Law)
    (observer : ObserverSelection.LeastMotion Time Carrier Law)
    (hread : data.readout.gauge.readsOnSelectedBundle observer) :
    (data.assembly.physicalPrinciple.selectedLaw.selection =
      observer.selection) ∧
      exactVisibleOnCut
        (observer.selection.realization.tower.π observer.selection.horizon)
        (selected_observed_law observer.selection).op ∧
      ForcedContinuumLaw
        observer.continuumClass
        data.assembly.physicalPrinciple.selectedLaw.selectedClosureLaw := by
  exact carrierClosureReadout data data.readout.gauge observer hread

/-- Geometric observers read from the detached microscopic bundle surface
inherit the exact carrier closure readout package automatically. -/
theorem SelectedBundleForcing.geometricClosureReadout
    {Index Time Carrier Law : Type}
    (data : SelectedBundleForcing Index Time Carrier Law)
    (observer : ObserverSelection.LeastMotion Time Carrier Law)
    (hread : data.readout.geometric.readsOnSelectedBundle observer) :
    (data.assembly.physicalPrinciple.selectedLaw.selection =
      observer.selection) ∧
      exactVisibleOnCut
        (observer.selection.realization.tower.π observer.selection.horizon)
        (selected_observed_law observer.selection).op ∧
      ForcedContinuumLaw
        observer.continuumClass
        data.assembly.physicalPrinciple.selectedLaw.selectedClosureLaw := by
  exact carrierClosureReadout data data.readout.geometric observer hread

/-- The detached microscopic readout package already transports the exact
carrier closure surface uniformly to the four visible carrier families read on
the same selected bundle. -/
theorem SelectedBundleForcing.readoutSurface
    {Index Time Carrier Law : Type}
    (data : SelectedBundleForcing Index Time Carrier Law) :
    (∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
      data.readout.phase.readsOnSelectedBundle observer →
        (data.assembly.physicalPrinciple.selectedLaw.selection =
          observer.selection) ∧
        exactVisibleOnCut
          (observer.selection.realization.tower.π observer.selection.horizon)
          (selected_observed_law observer.selection).op ∧
        ForcedContinuumLaw
          observer.continuumClass
          data.assembly.physicalPrinciple.selectedLaw.selectedClosureLaw) ∧
      (∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
        data.readout.wave.readsOnSelectedBundle observer →
          (data.assembly.physicalPrinciple.selectedLaw.selection =
            observer.selection) ∧
          exactVisibleOnCut
            (observer.selection.realization.tower.π observer.selection.horizon)
            (selected_observed_law observer.selection).op ∧
          ForcedContinuumLaw
            observer.continuumClass
            data.assembly.physicalPrinciple.selectedLaw.selectedClosureLaw) ∧
      (∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
        data.readout.gauge.readsOnSelectedBundle observer →
          (data.assembly.physicalPrinciple.selectedLaw.selection =
            observer.selection) ∧
          exactVisibleOnCut
            (observer.selection.realization.tower.π observer.selection.horizon)
            (selected_observed_law observer.selection).op ∧
          ForcedContinuumLaw
            observer.continuumClass
            data.assembly.physicalPrinciple.selectedLaw.selectedClosureLaw) ∧
      (∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
        data.readout.geometric.readsOnSelectedBundle observer →
          (data.assembly.physicalPrinciple.selectedLaw.selection =
            observer.selection) ∧
          exactVisibleOnCut
            (observer.selection.realization.tower.π observer.selection.horizon)
            (selected_observed_law observer.selection).op ∧
          ForcedContinuumLaw
            observer.continuumClass
            data.assembly.physicalPrinciple.selectedLaw.selectedClosureLaw) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro observer hread
    exact phaseClosureReadout data observer hread
  · intro observer hread
    exact waveClosureReadout data observer hread
  · intro observer hread
    exact gaugeClosureReadout data observer hread
  · intro observer hread
    exact geometricClosureReadout data observer hread

/-- Surface theorem for the detached bundle-readout package: it already yields
the active selected-bundle object together with the autonomy surface furnished
by the matched closure-current bridge. -/
theorem SelectedBundleForcing.surface
    {Index Time Carrier Law : Type}
    (data : SelectedBundleForcing Index Time Carrier Law) :
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
  refine ⟨⟨data.toIntrinsicSelectedBundleExistence⟩, ?_, ?_, ?_⟩
  exact data.bridge.carriesBedrockLaw
  exact selectedHorizonAutonomous data.bridge
  exact selectedHorizonFiberInvariant data.bridge

/-- Intrinsic sector-generation data above the detached selected-bundle forcing
surface. This packages exactly the extra hypotheses needed to recover the
active `IntrinsicSectorGeneration` object. -/
structure IntrinsicSectorForcing (Index Time Carrier Law : Type) where
  selectedBundle : SelectedBundleForcing Index Time Carrier Law
  canonicalGeneration : SelectedBundle.CanonicalGeneration
  generatedFromIntrinsicChannelAlgebra : Prop
  minimalCompatibleRealizationsOnly : Prop
  generatedFromIntrinsicChannelAlgebra_valid :
    generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly_valid :
    minimalCompatibleRealizationsOnly

/-- The detached intrinsic-sector package builds the active
`IntrinsicSectorGeneration` datum with no additional hidden data. -/
def IntrinsicSectorForcing.toIntrinsicSectorGeneration
    {Index Time Carrier Law : Type}
    (data : IntrinsicSectorForcing Index Time Carrier Law) :
    IntrinsicSectorGeneration Time Carrier Law :=
  { toCanonicalGeneration := data.canonicalGeneration
    selectedBundle := data.selectedBundle.toIntrinsicSelectedBundleExistence
    generatedFromIntrinsicChannelAlgebra :=
      data.generatedFromIntrinsicChannelAlgebra
    minimalCompatibleRealizationsOnly :=
      data.minimalCompatibleRealizationsOnly
    generatedFromIntrinsicChannelAlgebra_valid :=
      data.generatedFromIntrinsicChannelAlgebra_valid
    minimalCompatibleRealizationsOnly_valid :=
      data.minimalCompatibleRealizationsOnly_valid }

/-- Surface theorem for the detached intrinsic-sector package: once the bundle
readout and intrinsic generation clauses are supplied, the active Step 3
surface follows exactly. -/
theorem IntrinsicSectorForcing.surface
    {Index Time Carrier Law : Type}
    (data : IntrinsicSectorForcing Index Time Carrier Law) :
    Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
      data.generatedFromIntrinsicChannelAlgebra ∧
      data.minimalCompatibleRealizationsOnly ∧
      closureTypedPromotionFiniteCarrier.finite_carrier_available ∧
      closureTypedPromotionFiniteCarrier.canonical_signature_available ∧
      closureTypedPromotionFiniteCarrier.three_parameter_control ∧
      (natListSum [3, 2, 1] = balancedClosureSlotCount closureStableDimension) ∧
      IsCanonicalLogicalProfile [3, 2, 1] ∧
      data.canonicalGeneration.scalarChannelGeneratesPhase ∧
      data.canonicalGeneration.scalarChannelGeneratesWave ∧
      data.canonicalGeneration.balanceCompatibleCarrierGeneratesKinetic ∧
      data.canonicalGeneration.exactOneFormExchangeGeneratesGauge ∧
      data.canonicalGeneration.symmetricResponseGeneratesGeometry ∧
      data.canonicalGeneration.notPrimitiveDictionary := by
  let sectorData := data.toIntrinsicSectorGeneration
  have hsurface := intrinsic_sector_generation sectorData
  refine ⟨⟨sectorData⟩, ?_⟩
  simpa [sectorData, IntrinsicSectorForcing.toIntrinsicSectorGeneration] using hsurface

/-- Compact upstream forcing theorem. If a microscopic closure-current law
supplies the detached bundle-readout and intrinsic-generation interfaces, then
the active selected-bundle and Step 3 Part IV surfaces are recovered exactly.
-/
theorem forcingSurface
    {Index Time Carrier Law : Type}
    (data : IntrinsicSectorForcing Index Time Carrier Law) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
      realized_generator_carries_bedrock_law data.selectedBundle.bridge.generator ∧
      AutonomousHorizon
        data.selectedBundle.bridge.selectedBridge.observer.selection.realization.tower
        data.selectedBundle.bridge.selectedBridge.observer.selection.horizon
        data.selectedBundle.bridge.generator ∧
      horizonFiberInvariant
        data.selectedBundle.bridge.selectedBridge.observer.selection.realization.tower
        data.selectedBundle.bridge.selectedBridge.observer.selection.horizon
        data.selectedBundle.bridge.generator ∧
      data.generatedFromIntrinsicChannelAlgebra ∧
      data.minimalCompatibleRealizationsOnly ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  obtain ⟨hbundle, hbedrock, haut, hfiber⟩ := data.selectedBundle.surface
  obtain ⟨hsector, hgen, hmin, _hfinite, _hsignature, _hcontrol, _hsum, hprofile,
    _hphase, _hwave, _hkinetic, _hgauge, _hgeom, _hnotDict⟩ := data.surface
  exact ⟨hbundle, hsector, hbedrock, haut, hfiber, hgen, hmin, hprofile⟩

end ClosureCurrent

end CoherenceCalculus
