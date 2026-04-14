import CoherenceCalculus.PartIV.ClosureCurrentContinuumCore
import CoherenceCalculus.PartIV.ClosureCurrentForcingCore
import CoherenceCalculus.PartIV.ClosureCurrentBridgeCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumAttachmentCore

Law-native attachment of the detached continuum law to the active Part IV
selected-cut completion surface.

`ClosureCurrentContinuumCore` forces the detached four-state and reduced hidden
continuum laws from the no-stage local-event four-state law. The remaining
replacement seam is not the continuum limit itself, but the attachment back to
the active Part IV completion layer: the earlier attachment theorem still named
an external `NaturalOperatorCompletion` together with an equality of selected
bridges.

This file closes that seam in the detached lane. The new input is a single
no-stage completion law on one local event:

* one no-stage four-state law on one selected bridge;
* the intrinsic sector-generation clauses on that same bridge;
* the Step 4 endpoint-rigidity clauses, the four endpoint-sensitive canonical
  representative clauses, and the already classified kinetic face on that same
  bridge, from which the full carrier classification is recovered.

From that one detached package we reconstruct the active
`NaturalOperatorCompletion` internally, so the detached continuum law now
attaches back to the active selected-cut completion surface with no external
completion datum and no separate bridge-matching hypothesis. Carrier
classification is not stored as extra detached data here: it is recovered
internally from the reduced representative package carried by the same
no-stage completion law.
-/

namespace ClosureCurrent

/-- Proposition packaging the selected Schur / HFT-2 exact-closure surface on a
single selected datum. This is only a manuscript-facing alias for the existing
active theorem statement. -/
def SelectedSchurHFT2Surface
    {Index Time Carrier Law : Type}
    (bridge : SelectedSchur.Package Index Time Carrier Law) : Prop :=
  exactVisibleOnCut
      (bridge.observer.selection.realization.tower.π
        bridge.observer.selection.horizon)
      (selected_observed_law bridge.observer.selection).op ∧
    bridge.groundedBridge.physicalPrinciple.intrinsicallyClosedOnLeastMotionCut ∧
    bridge.groundedBridge.physicalPrinciple.noExogenousConstitutiveCompletion ∧
    bridge.groundedBridge.physicalPrinciple.apparentConstitutiveTermsAreReturnedResidual ∧
    (returnedResidual (canonicalSelectedResidualReturnField bridge) =
      schurComplement
        (bridge.observer.selection.realization.tower.π
          bridge.observer.selection.horizon)
        (selected_observed_law bridge.observer.selection).op
        (canonicalSelectedShadowPropagator bridge)) ∧
    (∀ x : State,
      (selected_observed_law bridge.observer.selection).op x =
        State.add
          (blockPP
            (bridge.observer.selection.realization.tower.π
              bridge.observer.selection.horizon)
            ((selected_observed_law bridge.observer.selection).op) x)
          (returnedResidual (canonicalSelectedResidualReturnField bridge) x)) ∧
    (∀ x : State,
      canonicalSelectedResidualStock bridge x =
        canonicalSelectedReturnFlux bridge x +
          unrecoveredResidualStock bridge.energyTower x
            (bridge.observer.selection.horizon + 1)) ∧
    (∀ h : Nat, ∀ x : State,
      unrecoveredResidualStock bridge.energyTower x (h + 1) ≤
        unrecoveredResidualStock bridge.energyTower x h) ∧
    (holographicImbalance 3 = SignedCount.ofNat 1) ∧
    IsCanonicalLogicalProfile [3, 2, 1] ∧
    SelectedCutOrthogonality.exactSplit bridge

/-- The active selected Schur / HFT-2 closure theorem exactly supplies the
packaged selected-cut surface above. -/
theorem selectedSchurHFT2Surface
    {Index Time Carrier Law : Type}
    (bridge : SelectedSchur.Package Index Time Carrier Law) :
    SelectedSchurHFT2Surface bridge := by
  exact selectedSchurHFT2ClosureSurface bridge

/-- No-stage local-event completion law. This is the detached law-side package
that refuses any additional microscopic or completion stage between the
four-state closure-current law and the active Part IV endpoint surface: the
intrinsic sector-generation and endpoint-rigidity clauses are carried on the
same selected bridge as the no-stage four-state law itself. -/
structure LocalEventFourStateCompletionLaw
    (Index Time Carrier Law : Type) where
  fourStateLaw : LocalEventFourStateLaw Index Time Carrier Law
  canonicalGeneration : SelectedBundle.CanonicalGeneration
  generatedFromIntrinsicChannelAlgebra : Prop
  minimalCompatibleRealizationsOnly : Prop
  localLawsReduceToFiniteJetOrder : Prop
  generatedSymmetryActsOnJetLevel : Prop
  compatibilityIdentitiesCutJetOperatorSpace : Prop
  admissibleEndpointEquivalenceRelation : Prop
  minimalTruncationProducesFiniteClosureQuotient : Prop
  singletonQuotientForcesUniqueCanonicalRepresentative : Prop
  nonsingletonQuotientForcesCanonicalNormalFormFamily : Prop
  endpointRigidity : EndpointRigidity.Reduction Time Carrier Law
  phaseCanonicalRepresentative : Prop
  waveCanonicalRepresentative : Prop
  kineticRepresentativeClassified : Prop
  gaugeCanonicalRepresentative : Prop
  geometricCanonicalRepresentative : Prop
  generatedFromIntrinsicChannelAlgebra_valid :
    generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly_valid :
    minimalCompatibleRealizationsOnly
  localLawsReduceToFiniteJetOrder_valid :
    localLawsReduceToFiniteJetOrder
  generatedSymmetryActsOnJetLevel_valid :
    generatedSymmetryActsOnJetLevel
  compatibilityIdentitiesCutJetOperatorSpace_valid :
    compatibilityIdentitiesCutJetOperatorSpace
  admissibleEndpointEquivalenceRelation_valid :
    admissibleEndpointEquivalenceRelation
  minimalTruncationProducesFiniteClosureQuotient_valid :
    minimalTruncationProducesFiniteClosureQuotient
  singletonQuotientForcesUniqueCanonicalRepresentative_valid :
    singletonQuotientForcesUniqueCanonicalRepresentative
  nonsingletonQuotientForcesCanonicalNormalFormFamily_valid :
    nonsingletonQuotientForcesCanonicalNormalFormFamily
  phaseCanonicalRepresentative_valid :
    phaseCanonicalRepresentative
  waveCanonicalRepresentative_valid :
    waveCanonicalRepresentative
  kineticRepresentativeClassified_valid :
    kineticRepresentativeClassified
  gaugeCanonicalRepresentative_valid :
    gaugeCanonicalRepresentative
  geometricCanonicalRepresentative_valid :
    geometricCanonicalRepresentative

/-- The no-stage completion law carries the selected-bundle assembly directly
on the same selected bridge as its four-state law. -/
def LocalEventFourStateCompletionLaw.toSelectedBundleAssembly
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    SelectedBundle.Assembly Time Carrier Law where
  selectedObservedBundle :=
    data.fourStateLaw.framed.object.selectedObservedBundle
  phaseCarrierSector :=
    data.fourStateLaw.framed.object.sectors.sector BundleSectorRole.phase
  waveCarrierSector :=
    data.fourStateLaw.framed.object.sectors.sector BundleSectorRole.wave
  kineticCarrierSector :=
    data.fourStateLaw.framed.object.sectors.sector BundleSectorRole.kinetic
  gaugeCarrierSector :=
    data.fourStateLaw.framed.object.sectors.sector BundleSectorRole.gauge
  geometricCarrierSector :=
    data.fourStateLaw.framed.object.sectors.sector BundleSectorRole.geometric
  physicalPrinciple := data.fourStateLaw.framed.object.physicalPrinciple
  bundlePhysicallyRealized :=
    data.fourStateLaw.framed.object.bundlePhysicallyRealized
  bundleSharedByAllCarriers :=
    data.fourStateLaw.framed.object.bundleSharedByAllCarriers
  sameSelectedEffectiveLawOnEachCarrier :=
    data.fourStateLaw.framed.object.sameSelectedEffectiveLawOnEachCarrier
  carrierLevelIdentificationOnlyFinalStep :=
    data.fourStateLaw.framed.object.carrierLevelIdentificationOnlyFinalStep
  selectedObservedBundle_valid :=
    data.fourStateLaw.framed.object.selectedObservedBundle_valid
  phaseCarrierSector_valid :=
    data.fourStateLaw.framed.object.phaseCarrierSector_valid
  waveCarrierSector_valid :=
    data.fourStateLaw.framed.object.waveCarrierSector_valid
  kineticCarrierSector_valid :=
    data.fourStateLaw.framed.object.kineticCarrierSector_valid
  gaugeCarrierSector_valid :=
    data.fourStateLaw.framed.object.gaugeCarrierSector_valid
  geometricCarrierSector_valid :=
    data.fourStateLaw.framed.object.geometricCarrierSector_valid
  bundlePhysicallyRealized_valid :=
    data.fourStateLaw.framed.object.bundlePhysicallyRealized_valid
  bundleSharedByAllCarriers_valid :=
    data.fourStateLaw.framed.object.bundleSharedByAllCarriers_valid
  sameSelectedEffectiveLawOnEachCarrier_valid :=
    data.fourStateLaw.framed.object.sameSelectedEffectiveLawOnEachCarrier_valid
  carrierLevelIdentificationOnlyFinalStep_valid :=
    data.fourStateLaw.framed.object.carrierLevelIdentificationOnlyFinalStep_valid

/-- One visible carrier family read on the same selected bundle as the
four-state law. -/
def LocalEventFourStateCompletionLaw.toCarrierReadout
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law)
    (role : VisibleCarrierRole) :
    CarrierReadout
      Time Carrier Law
      data.fourStateLaw.framed.object.bridge.selectedBridge.observer.selection where
  readsOnSelectedBundle :=
    data.fourStateLaw.framed.object.readsRoleOnSelectedBundle role
  sameSelection :=
    data.fourStateLaw.framed.object.readsRoleOnSelectedBundle_sameSelection role

/-- The no-stage completion law carries the common selected-bundle readout
interface directly on its own selected bridge. -/
def LocalEventFourStateCompletionLaw.toBundleReadout
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    BundleReadout
      Time Carrier Law
      data.fourStateLaw.framed.object.bridge.selectedBridge.observer.selection
      data.fourStateLaw.framed.object.physicalPrinciple.selectedLaw.endpointClosureClass where
  phase := data.toCarrierReadout VisibleCarrierRole.phase
  wave := data.toCarrierReadout VisibleCarrierRole.wave
  gauge := data.toCarrierReadout VisibleCarrierRole.gauge
  geometric := data.toCarrierReadout VisibleCarrierRole.geometric
  continuumClosure := {
    sameSelection :=
      data.fourStateLaw.framed.object.sameContinuumClosureClassOnSelectedBundle
  }
  bundleArisesIntrinsicallyOnLeastMotionCut :=
    data.fourStateLaw.framed.object.bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses :=
    data.fourStateLaw.framed.object.noCarrierWiseVisibilityHypotheses
  bundleArisesIntrinsicallyOnLeastMotionCut_valid :=
    data.fourStateLaw.framed.object.bundleArisesIntrinsicallyOnLeastMotionCut_valid
  noCarrierWiseVisibilityHypotheses_valid :=
    data.fourStateLaw.framed.object.noCarrierWiseVisibilityHypotheses_valid

/-- The no-stage completion law recovers the detached selected-bundle forcing
package on the same selected bridge. -/
def LocalEventFourStateCompletionLaw.toSelectedBundleForcing
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    SelectedBundleForcing Index Time Carrier Law where
  bridge := data.fourStateLaw.framed.object.bridge
  assembly := data.toSelectedBundleAssembly
  sameSelectedLawAsBridge :=
    data.fourStateLaw.framed.object.sameSelectedLawAsBridge
  readout := data.toBundleReadout

/-- The no-stage completion law recovers the detached intrinsic
sector-generation forcing package on the same selected bridge. -/
def LocalEventFourStateCompletionLaw.toIntrinsicSectorForcing
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    IntrinsicSectorForcing Index Time Carrier Law where
  selectedBundle := data.toSelectedBundleForcing
  canonicalGeneration := data.canonicalGeneration
  generatedFromIntrinsicChannelAlgebra :=
    data.generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly :=
    data.minimalCompatibleRealizationsOnly
  generatedFromIntrinsicChannelAlgebra_valid :=
    data.generatedFromIntrinsicChannelAlgebra_valid
  minimalCompatibleRealizationsOnly_valid :=
    data.minimalCompatibleRealizationsOnly_valid

/-- The no-stage completion law therefore determines the active Step 3
intrinsic sector-generation datum internally. -/
def LocalEventFourStateCompletionLaw.toIntrinsicSectorGeneration
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    IntrinsicSectorGeneration Time Carrier Law :=
  data.toIntrinsicSectorForcing.toIntrinsicSectorGeneration

/-- The no-stage completion law also determines the active Step 4
endpoint-rigidity principle internally, on that same selected bridge. -/
def LocalEventFourStateCompletionLaw.toRigidityPrinciple
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    EndpointRigidity.Principle Time Carrier Law where
  sectorGeneration := data.toIntrinsicSectorGeneration
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

/-- Carrier classification is already forced by the canonical representative
package carried by the same no-stage completion law. -/
def LocalEventFourStateCompletionLaw.toClassification
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
  SelectedBundle.CarrierClassification where
  phaseRepresentativeClassified := data.phaseCanonicalRepresentative
  waveRepresentativeClassified := data.waveCanonicalRepresentative
  kineticRepresentativeClassified := data.kineticRepresentativeClassified
  gaugeRepresentativeClassified := data.gaugeCanonicalRepresentative
  geometricRepresentativeClassified := data.geometricCanonicalRepresentative
  phaseRepresentativeClassified_valid :=
    data.phaseCanonicalRepresentative_valid
  waveRepresentativeClassified_valid :=
    data.waveCanonicalRepresentative_valid
  kineticRepresentativeClassified_valid :=
    data.kineticRepresentativeClassified_valid
  gaugeRepresentativeClassified_valid :=
    data.gaugeCanonicalRepresentative_valid
  geometricRepresentativeClassified_valid :=
    data.geometricCanonicalRepresentative_valid

/-- The no-stage completion law reconstructs the active natural-operator
completion object internally. No external completion datum is needed. -/
def LocalEventFourStateCompletionLaw.toNaturalOperatorCompletion
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    NaturalOperatorCompletion Time Carrier Law where
  phaseRepresentativeClassified :=
    data.toClassification.phaseRepresentativeClassified
  waveRepresentativeClassified :=
    data.toClassification.waveRepresentativeClassified
  kineticRepresentativeClassified :=
    data.toClassification.kineticRepresentativeClassified
  gaugeRepresentativeClassified :=
    data.toClassification.gaugeRepresentativeClassified
  geometricRepresentativeClassified :=
    data.toClassification.geometricRepresentativeClassified
  phaseRepresentativeClassified_valid :=
    data.toClassification.phaseRepresentativeClassified_valid
  waveRepresentativeClassified_valid :=
    data.toClassification.waveRepresentativeClassified_valid
  kineticRepresentativeClassified_valid :=
    data.toClassification.kineticRepresentativeClassified_valid
  gaugeRepresentativeClassified_valid :=
    data.toClassification.gaugeRepresentativeClassified_valid
  geometricRepresentativeClassified_valid :=
    data.toClassification.geometricRepresentativeClassified_valid
  sectorGeneration := data.toIntrinsicSectorGeneration
  rigidityPrinciple := data.toRigidityPrinciple
  rigidityPrincipleUsesSameSectorGeneration := rfl
  endpointRigidity := data.endpointRigidity
  phaseCanonicalRepresentative := data.phaseCanonicalRepresentative
  waveCanonicalRepresentative := data.waveCanonicalRepresentative
  gaugeCanonicalRepresentative := data.gaugeCanonicalRepresentative
  geometricCanonicalRepresentative := data.geometricCanonicalRepresentative
  phaseCanonicalRepresentative_valid :=
    data.phaseCanonicalRepresentative_valid
  waveCanonicalRepresentative_valid :=
    data.waveCanonicalRepresentative_valid
  gaugeCanonicalRepresentative_valid :=
    data.gaugeCanonicalRepresentative_valid
  geometricCanonicalRepresentative_valid :=
    data.geometricCanonicalRepresentative_valid

/-- The internally reconstructed natural-operator completion is read on the
same selected Schur bridge as the no-stage four-state law. -/
theorem LocalEventFourStateCompletionLaw.sameSelectedBridge
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    data.toNaturalOperatorCompletion.sectorGeneration.selectedBundle.selectedSchurBridge =
      data.fourStateLaw.framed.object.bridge.selectedBridge := by
  rfl

/-- The law-native no-stage completion package closes the remaining detached
attachment seam. From one no-stage four-state completion law on one selected
bridge, the active selected-bundle, intrinsic-sector, selected Schur / HFT-2,
and full Part IV completion surfaces are all recovered without any external
completion datum or bridge-matching hypothesis. -/
  theorem LocalEventFourStateCompletionLaw.attachedSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
      realized_generator_carries_bedrock_law
        data.fourStateLaw.framed.object.bridge.generator ∧
      AutonomousHorizon
        data.fourStateLaw.framed.object.bridge.selectedBridge.observer.selection.realization.tower
        data.fourStateLaw.framed.object.bridge.selectedBridge.observer.selection.horizon
        data.fourStateLaw.framed.object.bridge.generator ∧
      horizonFiberInvariant
        data.fourStateLaw.framed.object.bridge.selectedBridge.observer.selection.realization.tower
        data.fourStateLaw.framed.object.bridge.selectedBridge.observer.selection.horizon
        data.fourStateLaw.framed.object.bridge.generator ∧
      ForcedContinuumLaw
        data.fourStateLaw.stateDynamics.limitClass
        data.fourStateLaw.stateDynamics.continuumLaw ∧
      ForcedContinuumLaw
        data.fourStateLaw.toLocalEventStateBridge.reducedDynamics.hiddenLimitClass
        data.fourStateLaw.toLocalEventStateBridge.reducedDynamics.hiddenContinuumLaw ∧
      SelectedSchurHFT2Surface
        data.fourStateLaw.framed.object.bridge.selectedBridge ∧
      PartIVLawCompletionStatement data.toNaturalOperatorCompletion := by
  obtain ⟨hbundle, hsector, hbedrock, haut, hfiber, _hgen, _hmin, _hprofile⟩ :=
    forcingSurface data.toIntrinsicSectorForcing
  obtain ⟨_hcurrent, _hdirret, _hautread, _hmin, hstate, hreduced, _hquot, _hobs⟩ :=
    data.fourStateLaw.continuumSurface
  have hcompletion :
      PartIVLawCompletionStatement data.toNaturalOperatorCompletion := by
    exact partIV_law_completion data.toNaturalOperatorCompletion
  exact
    ⟨hbundle,
      hsector,
      hbedrock,
      haut,
      hfiber,
      hstate,
      hreduced,
      by
        simpa [data.sameSelectedBridge] using
          selectedSchurHFT2Surface
            data.toNaturalOperatorCompletion.sectorGeneration.selectedBundle.selectedSchurBridge,
      hcompletion⟩

/-- If the no-stage detached four-state law is matched to the same selected
datum as an active natural-operator completion, then the detached continuum
laws and the active selected Schur / HFT-2 completion surface already live on
that one datum. -/
theorem LocalEventFourStateLaw.attachedSurface
    {Time Carrier Law : Type}
    (completion : NaturalOperatorCompletion Time Carrier Law)
    (data :
      LocalEventFourStateLaw
        completion.sectorGeneration.selectedBundle.Index
        Time
        Carrier
        Law)
    (hsame :
      completion.sectorGeneration.selectedBundle.selectedSchurBridge =
        data.framed.object.bridge.selectedBridge) :
    realized_generator_carries_bedrock_law data.framed.object.bridge.generator ∧
      AutonomousHorizon
        data.framed.object.bridge.selectedBridge.observer.selection.realization.tower
        data.framed.object.bridge.selectedBridge.observer.selection.horizon
        data.framed.object.bridge.generator ∧
      ForcedContinuumLaw
        data.stateDynamics.limitClass
        data.stateDynamics.continuumLaw ∧
      ForcedContinuumLaw
        data.toLocalEventStateBridge.reducedDynamics.hiddenLimitClass
        data.toLocalEventStateBridge.reducedDynamics.hiddenContinuumLaw ∧
      SelectedSchurHFT2Surface
        completion.sectorGeneration.selectedBundle.selectedSchurBridge ∧
      PartIVLawCompletionStatement completion := by
  obtain ⟨_hsame, hbedrock, haut, hcompletion⟩ :=
    completionBridgeSurface completion data.framed.object.bridge hsame
  obtain ⟨_hcurrent, _hdirret, _hreadout, _hmin, hstate, hreduced, _hquot, _hobs⟩ :=
    data.continuumSurface
  exact
    ⟨hbedrock,
      haut,
      hstate,
      hreduced,
      selectedSchurHFT2Surface completion.sectorGeneration.selectedBundle.selectedSchurBridge,
      hcompletion⟩

end ClosureCurrent

end CoherenceCalculus
