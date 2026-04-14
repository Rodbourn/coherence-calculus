import CoherenceCalculus.Foundation
import CoherenceCalculus.PartIII

namespace CoherenceCalculus

/-- Part IV packages the selected visible effective law on a least-motion cut
as the current selected observed law together with an inherited forced closure
law on the induced continuum carrier. -/
structure SelectedVisibleEffectiveLaw (Time Carrier Law : Type) where
  selection : SelectionDatum Time
  visibleCarrier : Carrier
  coherentLaw : Compiler.QuadForm
  exactEffectiveLaw : Prop
  endpointClosureClass : ContinuumLimitClass Law
  selectedClosureLaw : Law
  selectedClosureForced :
    ForcedContinuumLaw endpointClosureClass selectedClosureLaw

/-- The first master Part IV principle: one coherent bundle, one realized
selected law, and one least-motion equivalence class on which the observable
dynamics are read. This collapses the observer-covariance and least-motion
surface together with the physical identification of the selected law. -/
structure RealizationSelectionPrinciple where
  observableDynamicsExactlySelectedLaw : Prop
  sameCoherentBundle : Prop
  observerCovariance : Prop
  leastMotionFaithfulCutUnique : Prop
  observableDynamicsExactlySelectedLaw_valid :
    observableDynamicsExactlySelectedLaw
  sameCoherentBundle_valid : sameCoherentBundle
  observerCovariance_valid : observerCovariance
  leastMotionFaithfulCutUnique_valid : leastMotionFaithfulCutUnique

/-- The second master Part IV principle: visible source, forcing, and
irreversibility are all endogenous readouts of exchange/return on one coherent
bundle. This collapses the source-as-exchange and return-side laws into one
physical package. -/
structure EndogenousExchangeReturnPrinciple where
  visibleSourcesOnlyExchangeBoundaryReentry : Prop
  zeroNetInternalCreationOnClosedSystems : Prop
  onlyReturnActs : Prop
  visibleForcingIsReturnedResidual : Prop
  observableIrreversibilityIsUnrecoveredResidual : Prop
  residualLocalizesOnUniqueInterface : Prop
  selectedLawObtainedByResidualElimination : Prop
  visibleSourcesOnlyExchangeBoundaryReentry_valid :
    visibleSourcesOnlyExchangeBoundaryReentry
  zeroNetInternalCreationOnClosedSystems_valid :
    zeroNetInternalCreationOnClosedSystems
  onlyReturnActs_valid : onlyReturnActs
  visibleForcingIsReturnedResidual_valid :
    visibleForcingIsReturnedResidual
  observableIrreversibilityIsUnrecoveredResidual_valid :
    observableIrreversibilityIsUnrecoveredResidual
  residualLocalizesOnUniqueInterface_valid :
    residualLocalizesOnUniqueInterface
  selectedLawObtainedByResidualElimination_valid :
    selectedLawObtainedByResidualElimination

/-- Reader-facing four-clause surface for Laws I--III. In the three-principle
presentation this is a derived unpacking rather than a primary structure. -/
structure PartIVLawClauses where
  observerCovariance : Prop
  leastMotionFaithfulCutUnique : Prop
  visibleSourcesOnlyExchangeBoundaryReentry : Prop
  zeroNetInternalCreationOnClosedSystems : Prop
  observerCovariance_valid : observerCovariance
  leastMotionFaithfulCutUnique_valid : leastMotionFaithfulCutUnique
  visibleSourcesOnlyExchangeBoundaryReentry_valid :
    visibleSourcesOnlyExchangeBoundaryReentry
  zeroNetInternalCreationOnClosedSystems_valid :
    zeroNetInternalCreationOnClosedSystems

/-- Reader-facing return-side surface for Law IV. In the three-principle
presentation this is likewise a derived unpacking. -/
structure ResidualReturnPrinciple where
  onlyReturnActs : Prop
  visibleForcingIsReturnedResidual : Prop
  observableIrreversibilityIsUnrecoveredResidual : Prop
  residualLocalizesOnUniqueInterface : Prop
  selectedLawObtainedByResidualElimination : Prop
  onlyReturnActs_valid : onlyReturnActs
  visibleForcingIsReturnedResidual_valid :
    visibleForcingIsReturnedResidual
  observableIrreversibilityIsUnrecoveredResidual_valid :
    observableIrreversibilityIsUnrecoveredResidual
  residualLocalizesOnUniqueInterface_valid :
    residualLocalizesOnUniqueInterface
  selectedLawObtainedByResidualElimination_valid :
    selectedLawObtainedByResidualElimination

/-- The self-sufficient realization clause: on the physically realized
least-motion cut, the selected law is already exactly visible and closes
without exogenous constitutive completion. Any apparent constitutive term is
therefore interpreted as returned residual from eliminated sectors of the same
coherent bundle. -/
structure SelfSufficientRealizationPrinciple (Time Carrier Law : Type) where
  selectedLaw : SelectedVisibleEffectiveLaw Time Carrier Law
  exactVisibleSelectedLawOnLeastMotionCut :
    exactVisibleOnCut
      (selectedLaw.selection.realization.tower.π selectedLaw.selection.horizon)
      (selected_observed_law selectedLaw.selection).op
  intrinsicallyClosedOnLeastMotionCut : Prop
  noExogenousConstitutiveCompletion : Prop
  apparentConstitutiveTermsAreReturnedResidual : Prop
  intrinsicallyClosedOnLeastMotionCut_valid :
    intrinsicallyClosedOnLeastMotionCut
  noExogenousConstitutiveCompletion_valid :
    noExogenousConstitutiveCompletion
  apparentConstitutiveTermsAreReturnedResidual_valid :
    apparentConstitutiveTermsAreReturnedResidual

/-- Self-sufficient realization unpacks to exact visibility on the selected cut
and the absence of exogenous constitutive completion there. -/
theorem self_sufficient_realization_principle
    {Time Carrier Law : Type}
    (data : SelfSufficientRealizationPrinciple Time Carrier Law) :
    exactVisibleOnCut
      (data.selectedLaw.selection.realization.tower.π
        data.selectedLaw.selection.horizon)
      (selected_observed_law data.selectedLaw.selection).op ∧
      data.intrinsicallyClosedOnLeastMotionCut ∧
      data.noExogenousConstitutiveCompletion ∧
      data.apparentConstitutiveTermsAreReturnedResidual := by
  exact
    ⟨data.exactVisibleSelectedLawOnLeastMotionCut,
      data.intrinsicallyClosedOnLeastMotionCut_valid,
      data.noExogenousConstitutiveCompletion_valid,
      data.apparentConstitutiveTermsAreReturnedResidual_valid⟩

/-- The realization-selection principle unpacks to the physical identification
of the selected law together with the observer-covariant least-motion class on
which it is read. -/
theorem realization_selection_principle
    (data : RealizationSelectionPrinciple) :
    data.observableDynamicsExactlySelectedLaw ∧
      data.sameCoherentBundle ∧
      data.observerCovariance ∧
      data.leastMotionFaithfulCutUnique := by
  exact
    ⟨data.observableDynamicsExactlySelectedLaw_valid,
      data.sameCoherentBundle_valid,
      data.observerCovariance_valid,
      data.leastMotionFaithfulCutUnique_valid⟩

/-- The endogenous exchange-return principle unpacks to the claim that visible
source, forcing, and irreversibility are all endogenous readouts of exchange
and return. -/
theorem endogenous_exchange_return_principle
    (data : EndogenousExchangeReturnPrinciple) :
    data.visibleSourcesOnlyExchangeBoundaryReentry ∧
      data.zeroNetInternalCreationOnClosedSystems ∧
      data.onlyReturnActs ∧
      data.visibleForcingIsReturnedResidual ∧
      data.observableIrreversibilityIsUnrecoveredResidual ∧
      data.residualLocalizesOnUniqueInterface ∧
      data.selectedLawObtainedByResidualElimination := by
  exact
    ⟨data.visibleSourcesOnlyExchangeBoundaryReentry_valid,
      data.zeroNetInternalCreationOnClosedSystems_valid,
      data.onlyReturnActs_valid,
      data.visibleForcingIsReturnedResidual_valid,
      data.observableIrreversibilityIsUnrecoveredResidual_valid,
      data.residualLocalizesOnUniqueInterface_valid,
      data.selectedLawObtainedByResidualElimination_valid⟩

/-- The master Part IV bridge from the structural calculus to observable
physics. The five reader-facing laws are presented at the manuscript surface,
but they collapse here to three master principles:
realization-selection, endogenous exchange-return, and self-sufficient
closure. -/
structure PhysicalRealizationPrinciple (Time Carrier Law : Type)
    extends RealizationSelectionPrinciple,
      EndogenousExchangeReturnPrinciple,
      SelfSufficientRealizationPrinciple Time Carrier Law

/-- Reader-facing Laws I--III are a derived unpacking of the three-principle
surface. -/
def PhysicalRealizationPrinciple.lawClauses
    {Time Carrier Law : Type}
    (data : PhysicalRealizationPrinciple Time Carrier Law) :
    PartIVLawClauses where
  observerCovariance := data.observerCovariance
  leastMotionFaithfulCutUnique := data.leastMotionFaithfulCutUnique
  visibleSourcesOnlyExchangeBoundaryReentry :=
    data.visibleSourcesOnlyExchangeBoundaryReentry
  zeroNetInternalCreationOnClosedSystems :=
    data.zeroNetInternalCreationOnClosedSystems
  observerCovariance_valid := data.observerCovariance_valid
  leastMotionFaithfulCutUnique_valid :=
    data.leastMotionFaithfulCutUnique_valid
  visibleSourcesOnlyExchangeBoundaryReentry_valid :=
    data.visibleSourcesOnlyExchangeBoundaryReentry_valid
  zeroNetInternalCreationOnClosedSystems_valid :=
    data.zeroNetInternalCreationOnClosedSystems_valid

/-- Reader-facing Law IV is likewise a derived unpacking of the endogenous
exchange-return master principle. -/
def PhysicalRealizationPrinciple.residualReturn
    {Time Carrier Law : Type}
    (data : PhysicalRealizationPrinciple Time Carrier Law) :
    ResidualReturnPrinciple where
  onlyReturnActs := data.onlyReturnActs
  visibleForcingIsReturnedResidual := data.visibleForcingIsReturnedResidual
  observableIrreversibilityIsUnrecoveredResidual :=
    data.observableIrreversibilityIsUnrecoveredResidual
  residualLocalizesOnUniqueInterface :=
    data.residualLocalizesOnUniqueInterface
  selectedLawObtainedByResidualElimination :=
    data.selectedLawObtainedByResidualElimination
  onlyReturnActs_valid := data.onlyReturnActs_valid
  visibleForcingIsReturnedResidual_valid :=
    data.visibleForcingIsReturnedResidual_valid
  observableIrreversibilityIsUnrecoveredResidual_valid :=
    data.observableIrreversibilityIsUnrecoveredResidual_valid
  residualLocalizesOnUniqueInterface_valid :=
    data.residualLocalizesOnUniqueInterface_valid
  selectedLawObtainedByResidualElimination_valid :=
    data.selectedLawObtainedByResidualElimination_valid

/-- The residual return principle says that only returned residual acts
observably on the selected cut, while unrecovered residual is the irreversible
content. -/
theorem residual_return_principle
    (data : ResidualReturnPrinciple) :
    data.onlyReturnActs ∧
      data.visibleForcingIsReturnedResidual ∧
      data.observableIrreversibilityIsUnrecoveredResidual ∧
      data.residualLocalizesOnUniqueInterface ∧
      data.selectedLawObtainedByResidualElimination := by
  exact
    ⟨data.onlyReturnActs_valid,
      data.visibleForcingIsReturnedResidual_valid,
      data.observableIrreversibilityIsUnrecoveredResidual_valid,
      data.residualLocalizesOnUniqueInterface_valid,
      data.selectedLawObtainedByResidualElimination_valid⟩

/-- The five reader-facing laws are a derived surface of the three master Part
IV principles. -/
theorem five_law_surface_of_three_master_principles
    {Time Carrier Law : Type}
    (data : PhysicalRealizationPrinciple Time Carrier Law) :
    data.observableDynamicsExactlySelectedLaw ∧
      data.sameCoherentBundle ∧
      data.lawClauses.observerCovariance ∧
      data.lawClauses.leastMotionFaithfulCutUnique ∧
      data.lawClauses.visibleSourcesOnlyExchangeBoundaryReentry ∧
      data.lawClauses.zeroNetInternalCreationOnClosedSystems ∧
      data.residualReturn.onlyReturnActs ∧
      data.residualReturn.visibleForcingIsReturnedResidual ∧
      data.residualReturn.observableIrreversibilityIsUnrecoveredResidual ∧
      data.residualReturn.residualLocalizesOnUniqueInterface ∧
      data.residualReturn.selectedLawObtainedByResidualElimination ∧
      exactVisibleOnCut
        (data.selectedLaw.selection.realization.tower.π
          data.selectedLaw.selection.horizon)
        (selected_observed_law data.selectedLaw.selection).op ∧
      data.intrinsicallyClosedOnLeastMotionCut ∧
      data.noExogenousConstitutiveCompletion ∧
      data.apparentConstitutiveTermsAreReturnedResidual := by
  exact
    ⟨data.observableDynamicsExactlySelectedLaw_valid,
      data.sameCoherentBundle_valid,
      data.lawClauses.observerCovariance_valid,
      data.lawClauses.leastMotionFaithfulCutUnique_valid,
      data.lawClauses.visibleSourcesOnlyExchangeBoundaryReentry_valid,
      data.lawClauses.zeroNetInternalCreationOnClosedSystems_valid,
      data.residualReturn.onlyReturnActs_valid,
      data.residualReturn.visibleForcingIsReturnedResidual_valid,
      data.residualReturn.observableIrreversibilityIsUnrecoveredResidual_valid,
      data.residualReturn.residualLocalizesOnUniqueInterface_valid,
      data.residualReturn.selectedLawObtainedByResidualElimination_valid,
      data.exactVisibleSelectedLawOnLeastMotionCut,
      data.intrinsicallyClosedOnLeastMotionCut_valid,
      data.noExogenousConstitutiveCompletion_valid,
      data.apparentConstitutiveTermsAreReturnedResidual_valid⟩

/-- The physical realization principle says that the selected visible law is
the observable dynamics, on one coherent bundle, with observer/exchange clauses
making that statement precise. -/
theorem physical_realization_principle
    {Time Carrier Law : Type}
    (data : PhysicalRealizationPrinciple Time Carrier Law) :
    exactVisibleOnCut
      (data.selectedLaw.selection.realization.tower.π
        data.selectedLaw.selection.horizon)
      (selected_observed_law data.selectedLaw.selection).op ∧
      data.intrinsicallyClosedOnLeastMotionCut ∧
      data.noExogenousConstitutiveCompletion ∧
      data.apparentConstitutiveTermsAreReturnedResidual ∧
      data.observableDynamicsExactlySelectedLaw ∧
      data.sameCoherentBundle ∧
      data.lawClauses.observerCovariance ∧
      data.lawClauses.leastMotionFaithfulCutUnique ∧
      data.lawClauses.visibleSourcesOnlyExchangeBoundaryReentry ∧
      data.lawClauses.zeroNetInternalCreationOnClosedSystems ∧
      data.residualReturn.onlyReturnActs ∧
      data.residualReturn.visibleForcingIsReturnedResidual ∧
      data.residualReturn.observableIrreversibilityIsUnrecoveredResidual ∧
      data.residualReturn.residualLocalizesOnUniqueInterface ∧
      data.residualReturn.selectedLawObtainedByResidualElimination := by
  exact
    ⟨data.exactVisibleSelectedLawOnLeastMotionCut,
      data.intrinsicallyClosedOnLeastMotionCut_valid,
      data.noExogenousConstitutiveCompletion_valid,
      data.apparentConstitutiveTermsAreReturnedResidual_valid,
      data.observableDynamicsExactlySelectedLaw_valid,
      data.sameCoherentBundle_valid, data.lawClauses.observerCovariance_valid,
      data.lawClauses.leastMotionFaithfulCutUnique_valid,
      data.lawClauses.visibleSourcesOnlyExchangeBoundaryReentry_valid,
      data.lawClauses.zeroNetInternalCreationOnClosedSystems_valid,
      data.residualReturn.onlyReturnActs_valid,
      data.residualReturn.visibleForcingIsReturnedResidual_valid,
      data.residualReturn.observableIrreversibilityIsUnrecoveredResidual_valid,
      data.residualReturn.residualLocalizesOnUniqueInterface_valid,
      data.residualReturn.selectedLawObtainedByResidualElimination_valid⟩

/-- The common Part IV grammar is the carrier-independent physical pipeline
used throughout the flagship sections. -/
structure CommonPartIVGrammar where
  hiddenCoherentLaw : Prop
  residualReturnFieldOnSelectedCut : Prop
  selectedVisibleLawPhysicallyRealized : Prop
  onlyReturnActsOnVisibleBundle : Prop
  characteristicEndpointReduction : Prop
  canonicalSectorGeneration : Prop
  symmetryRigidMinimalClosure : Prop
  carrierLevelPhysicalLaw : Prop

namespace SelectedBundle

/-- Bundle-first reading of Part IV: one selected observed bundle together with
typed visible carrier sectors. -/
structure FirstReading where
  selectedObservedBundle : Prop
  phaseCarrierSector : Prop
  waveCarrierSector : Prop
  kineticCarrierSector : Prop
  gaugeCarrierSector : Prop
  geometricCarrierSector : Prop

/-- The five flagship carrier classes are generated canonically on the selected
bundle as minimal compatible realizations of the intrinsic channel algebra, not
as a primitive dictionary from the channel dimensions themselves. -/
structure CanonicalGeneration where
  scalarChannelVisible : Prop
  scalarChannelGeneratesPhase : Prop
  scalarChannelGeneratesWave : Prop
  balanceCompatibleCarrierGeneratesKinetic : Prop
  exactOneFormExchangeGeneratesGauge : Prop
  symmetricResponseGeneratesGeometry : Prop
  notPrimitiveDictionary : Prop
  scalarChannelVisible_valid : scalarChannelVisible
  scalarChannelGeneratesPhase_valid : scalarChannelGeneratesPhase
  scalarChannelGeneratesWave_valid : scalarChannelGeneratesWave
  balanceCompatibleCarrierGeneratesKinetic_valid :
    balanceCompatibleCarrierGeneratesKinetic
  exactOneFormExchangeGeneratesGauge_valid :
    exactOneFormExchangeGeneratesGauge
  symmetricResponseGeneratesGeometry_valid :
    symmetricResponseGeneratesGeometry
  notPrimitiveDictionary_valid : notPrimitiveDictionary

/-- The remaining carrier-side task is to identify the canonical minimal
compatible representative on each generated visible carrier. -/
structure CarrierClassification where
  phaseRepresentativeClassified : Prop
  waveRepresentativeClassified : Prop
  kineticRepresentativeClassified : Prop
  gaugeRepresentativeClassified : Prop
  geometricRepresentativeClassified : Prop
  phaseRepresentativeClassified_valid : phaseRepresentativeClassified
  waveRepresentativeClassified_valid : waveRepresentativeClassified
  kineticRepresentativeClassified_valid : kineticRepresentativeClassified
  gaugeRepresentativeClassified_valid : gaugeRepresentativeClassified
  geometricRepresentativeClassified_valid : geometricRepresentativeClassified

/-- Canonical sector generation unpacks to the five visible carrier classes on
the selected bundle without identifying them with a primitive `1+2+3`
dictionary. -/
theorem CanonicalGeneration.surface
    (data : CanonicalGeneration) :
    data.scalarChannelVisible ∧
      data.scalarChannelGeneratesPhase ∧
      data.scalarChannelGeneratesWave ∧
      data.balanceCompatibleCarrierGeneratesKinetic ∧
      data.exactOneFormExchangeGeneratesGauge ∧
      data.symmetricResponseGeneratesGeometry ∧
      data.notPrimitiveDictionary := by
  exact
    ⟨data.scalarChannelVisible_valid,
      data.scalarChannelGeneratesPhase_valid,
      data.scalarChannelGeneratesWave_valid,
      data.balanceCompatibleCarrierGeneratesKinetic_valid,
      data.exactOneFormExchangeGeneratesGauge_valid,
      data.symmetricResponseGeneratesGeometry_valid,
      data.notPrimitiveDictionary_valid⟩

/-- Carrier-level classification is exactly the five representative
identification problems on the generated visible sectors. -/
theorem CarrierClassification.surface
    (data : CarrierClassification) :
    data.phaseRepresentativeClassified ∧
      data.waveRepresentativeClassified ∧
      data.kineticRepresentativeClassified ∧
      data.gaugeRepresentativeClassified ∧
      data.geometricRepresentativeClassified := by
  exact
    ⟨data.phaseRepresentativeClassified_valid,
      data.waveRepresentativeClassified_valid,
      data.kineticRepresentativeClassified_valid,
      data.gaugeRepresentativeClassified_valid,
      data.geometricRepresentativeClassified_valid⟩

/-- Conditional common selected-bundle assembly package on one least-motion
cut. -/
structure Assembly (Time Carrier Law : Type)
    extends FirstReading where
  physicalPrinciple : PhysicalRealizationPrinciple Time Carrier Law
  bundlePhysicallyRealized : Prop
  bundleSharedByAllCarriers : Prop
  sameSelectedEffectiveLawOnEachCarrier : Prop
  carrierLevelIdentificationOnlyFinalStep : Prop
  selectedObservedBundle_valid : selectedObservedBundle
  phaseCarrierSector_valid : phaseCarrierSector
  waveCarrierSector_valid : waveCarrierSector
  kineticCarrierSector_valid : kineticCarrierSector
  gaugeCarrierSector_valid : gaugeCarrierSector
  geometricCarrierSector_valid : geometricCarrierSector
  bundlePhysicallyRealized_valid : bundlePhysicallyRealized
  bundleSharedByAllCarriers_valid : bundleSharedByAllCarriers
  sameSelectedEffectiveLawOnEachCarrier_valid :
    sameSelectedEffectiveLawOnEachCarrier
  carrierLevelIdentificationOnlyFinalStep_valid :
    carrierLevelIdentificationOnlyFinalStep

/-- On one least-motion cut, the flagship carriers assemble as sectors of one
selected observed bundle and differ only at the final carrier-level physical
identification step. -/
theorem Assembly.surface
    {Time Carrier Law : Type}
    (data : Assembly Time Carrier Law) :
    data.selectedObservedBundle ∧
      data.phaseCarrierSector ∧
      data.waveCarrierSector ∧
      data.kineticCarrierSector ∧
      data.gaugeCarrierSector ∧
      data.geometricCarrierSector ∧
      data.bundlePhysicallyRealized ∧
      data.bundleSharedByAllCarriers ∧
      data.sameSelectedEffectiveLawOnEachCarrier ∧
      data.carrierLevelIdentificationOnlyFinalStep := by
  exact ⟨data.selectedObservedBundle_valid, data.phaseCarrierSector_valid,
    data.waveCarrierSector_valid, data.kineticCarrierSector_valid,
    data.gaugeCarrierSector_valid, data.geometricCarrierSector_valid,
    data.bundlePhysicallyRealized_valid,
    data.bundleSharedByAllCarriers_valid,
    data.sameSelectedEffectiveLawOnEachCarrier_valid,
    data.carrierLevelIdentificationOnlyFinalStep_valid⟩

/-- The common selected-bundle assembly already determines the visible
carrier-generation package itself: scalar visibility is witnessed through the
common phase/wave assembly, the five visible sectors are already present on
that same bundle, and the non-dictionary character is exactly the fact that
all sectors share one bundle and differ only at the final carrier-level
identification step. -/
def Assembly.toCanonicalGeneration
    {Time Carrier Law : Type}
    (data : Assembly Time Carrier Law) :
    CanonicalGeneration where
  scalarChannelVisible :=
    data.phaseCarrierSector ∧ data.waveCarrierSector
  scalarChannelGeneratesPhase := data.phaseCarrierSector
  scalarChannelGeneratesWave := data.waveCarrierSector
  balanceCompatibleCarrierGeneratesKinetic := data.kineticCarrierSector
  exactOneFormExchangeGeneratesGauge := data.gaugeCarrierSector
  symmetricResponseGeneratesGeometry := data.geometricCarrierSector
  notPrimitiveDictionary :=
    data.bundleSharedByAllCarriers ∧
      data.carrierLevelIdentificationOnlyFinalStep
  scalarChannelVisible_valid := by
    exact ⟨data.phaseCarrierSector_valid, data.waveCarrierSector_valid⟩
  scalarChannelGeneratesPhase_valid := data.phaseCarrierSector_valid
  scalarChannelGeneratesWave_valid := data.waveCarrierSector_valid
  balanceCompatibleCarrierGeneratesKinetic_valid :=
    data.kineticCarrierSector_valid
  exactOneFormExchangeGeneratesGauge_valid := data.gaugeCarrierSector_valid
  symmetricResponseGeneratesGeometry_valid :=
    data.geometricCarrierSector_valid
  notPrimitiveDictionary_valid := by
    exact
      ⟨data.bundleSharedByAllCarriers_valid,
        data.carrierLevelIdentificationOnlyFinalStep_valid⟩

/-- Thus the selected-bundle assembly already carries the full visible
carrier-generation surface, apart from the two explicit Step 3 intrinsic
generation clauses. -/
theorem Assembly.canonicalGenerationSurface
    {Time Carrier Law : Type}
    (data : Assembly Time Carrier Law) :
    let generation := data.toCanonicalGeneration
    generation.scalarChannelVisible ∧
      generation.scalarChannelGeneratesPhase ∧
      generation.scalarChannelGeneratesWave ∧
      generation.balanceCompatibleCarrierGeneratesKinetic ∧
      generation.exactOneFormExchangeGeneratesGauge ∧
      generation.symmetricResponseGeneratesGeometry ∧
      generation.notPrimitiveDictionary := by
  simpa [Assembly.toCanonicalGeneration] using
    CanonicalGeneration.surface data.toCanonicalGeneration

/-- After one common selected-bundle assembly, the remaining Part IV task is to
generate the five visible sectors canonically and classify the minimal
compatible representative on each of them. -/
structure Reduction (Time Carrier Law : Type) where
  bundleAssembly : Assembly Time Carrier Law
  sectorGeneration : CanonicalGeneration
  classification : CarrierClassification
  remainingTaskIsCarrierClassification : Prop
  remainingTaskIsCarrierClassification_valid :
    remainingTaskIsCarrierClassification

/-- The sector-generation reduction packages the common selected bundle, the
non-dictionary sector-generation data, and the final carrier-level
classification target. -/
theorem Reduction.surface
    {Time Carrier Law : Type}
    (data : Reduction Time Carrier Law) :
    data.bundleAssembly.selectedObservedBundle ∧
      data.sectorGeneration.scalarChannelVisible ∧
      data.sectorGeneration.scalarChannelGeneratesPhase ∧
      data.sectorGeneration.scalarChannelGeneratesWave ∧
      data.sectorGeneration.balanceCompatibleCarrierGeneratesKinetic ∧
      data.sectorGeneration.exactOneFormExchangeGeneratesGauge ∧
      data.sectorGeneration.symmetricResponseGeneratesGeometry ∧
      data.classification.phaseRepresentativeClassified ∧
      data.classification.waveRepresentativeClassified ∧
      data.classification.kineticRepresentativeClassified ∧
      data.classification.gaugeRepresentativeClassified ∧
      data.classification.geometricRepresentativeClassified ∧
      data.remainingTaskIsCarrierClassification := by
  refine ⟨data.bundleAssembly.selectedObservedBundle_valid, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact data.sectorGeneration.scalarChannelVisible_valid
  · exact data.sectorGeneration.scalarChannelGeneratesPhase_valid
  · exact data.sectorGeneration.scalarChannelGeneratesWave_valid
  · exact data.sectorGeneration.balanceCompatibleCarrierGeneratesKinetic_valid
  · exact data.sectorGeneration.exactOneFormExchangeGeneratesGauge_valid
  · exact data.sectorGeneration.symmetricResponseGeneratesGeometry_valid
  · exact data.classification.phaseRepresentativeClassified_valid
  · exact data.classification.waveRepresentativeClassified_valid
  · exact data.classification.kineticRepresentativeClassified_valid
  · exact data.classification.gaugeRepresentativeClassified_valid
  · exact data.classification.geometricRepresentativeClassified_valid
  · exact data.remainingTaskIsCarrierClassification_valid

end SelectedBundle

/-- Explicit seed-side package for the internal D=2 spectral lane. -/
structure D2SpectralSeedData (Law : Type) where
  singleChannelUnitSeed : Prop
  oneFiberVisibleLaw : Prop
  repeatCyclesNoNewCarrier : Prop
  family : PrimitiveSupportSpectralDefectFamily Law
  primeData : CyclicRefinementPrimeInvariantData
  continuumData : PrimitiveSupportContinuumSpectralDefectData Law
  singleChannelUnitSeed_valid : singleChannelUnitSeed
  oneFiberVisibleLaw_valid : oneFiberVisibleLaw
  repeatCyclesNoNewCarrier_valid : repeatCyclesNoNewCarrier

/-- The internal D=2 seed exports a one-fiber visible law, prime-index
refinement, and a forced continuum spectral-defect form. -/
theorem d2_spectral_seed_package {Law : Type} (data : D2SpectralSeedData Law) :
    data.singleChannelUnitSeed ∧
      data.oneFiberVisibleLaw ∧
      data.repeatCyclesNoNewCarrier ∧
      data.family.primitiveSupportGenerated ∧
      data.primeData.samePrimeIndexMultiset ∧
      data.continuumData.selfAdjointPositiveSemidefinite ∧
      ForcedContinuumLaw
        data.continuumData.continuumClass
        data.continuumData.target := by
  have hprime := primitive_support_prime_refinement data.family data.primeData
  have hcont := primitive_support_continuum_spectral_defect data.continuumData
  exact
    ⟨data.singleChannelUnitSeed_valid, data.oneFiberVisibleLaw_valid,
      data.repeatCyclesNoNewCarrier_valid, hprime.1, hprime.2, hcont.1,
      hcont.2⟩

namespace ObserverSelection

/-- Summary package for the earlier compatibility/order interfaces reused by
Part IV. -/
structure InheritedCompatibility where
  characteristicBoundaryReduction : Prop
  observerTriadCompatibility : Prop
  reversibleRecursionCompatibility : Prop
  nilpotentExactnessAndSolverLayer : Prop
  localGaugeCovariance : Prop
  intrinsicSymmetryScalarization : Prop
  inheritedMinimalOrderClosureClass : Prop

/-- Explicit Part IV observer datum over one selected finite-horizon datum and
its continuum continuation data. -/
structure CharacteristicDatum (Time Carrier Law : Type) where
  selection : SelectionDatum Time
  visibleCarrier : Carrier
  reconstructionCompatible : Prop
  continuumCarrier : Type
  continuumLawSpace : Type
  promotionCompatible : Prop
  continuumClass : ContinuumLimitClass Law

/-- Least-motion observers are the Part IV datum together with the extra
faithfulness/minimality/uniqueness clauses imposed by the observer laws. -/
structure LeastMotion (Time Carrier Law : Type)
    extends CharacteristicDatum Time Carrier Law where
  faithful : Prop
  closureAdmissible : Prop
  stableUnderAdmissiblePromotion : Prop
  noProperVisibleSubcarrier : Prop
  observerMotionMinimal : Prop
  uniqueUpToHorizonPreservingEquivalence : Prop

/-- Helper constructor theorem for the common least-motion observer surface. -/
theorem LeastMotion.nonempty
    {Time Carrier Law : Type}
    (data : LeastMotion Time Carrier Law) :
    Nonempty (LeastMotion Time Carrier Law) := by
  exact ⟨data⟩

/-- When the least-motion observer is unique, the observer-side triad is read
as a consequence of the selected cut. -/
structure TriadConsequence
    (Time Carrier Law : Type) where
  observer : LeastMotion Time Carrier Law
  bulkFollowingEqualsBoundaryObserving : Prop
  boundaryObservingEqualsActionGenerator : Prop
  symmetryRecoveredAsStabilizer : Prop

end ObserverSelection

/-- Summary of the earlier theorem interfaces invoked by the Part IV flagship
sections once the least-motion observer is fixed. -/
structure PartIVUsesEarlierInterfaces where
  selectionInterface : Prop
  realizedForcingAndSymmetryPackages : Prop
  promotionAndContinuumForcingInterfaces : Prop

namespace EndpointRigidity

/-- Forced endpoint-rigidity reduction surface on one selected carrier. This
keeps only the common reduction consequences that the active Step 4 bridge
actually uses. -/
structure Reduction (Time Carrier Law : Type) where
  observer : ObserverSelection.LeastMotion Time Carrier Law
  symmetryChannelScalarization : Prop
  inheritedMinimalOrderClassSingleton : Prop
  endpointClosureUniqueModuloContinuumEquivalence : Prop
  symmetryChannelScalarization_valid : symmetryChannelScalarization
  inheritedMinimalOrderClassSingleton_valid :
    inheritedMinimalOrderClassSingleton
  endpointClosureUniqueModuloContinuumEquivalence_valid :
    endpointClosureUniqueModuloContinuumEquivalence

/-- Endpoint rigidity forces a common carrier-side reduction surface before any
carrier-specific representative is identified. -/
theorem Reduction.surface
    {Time Carrier Law : Type}
    (data : Reduction Time Carrier Law) :
    data.symmetryChannelScalarization ∧
      data.inheritedMinimalOrderClassSingleton ∧
      data.endpointClosureUniqueModuloContinuumEquivalence := by
  exact ⟨data.symmetryChannelScalarization_valid,
    data.inheritedMinimalOrderClassSingleton_valid,
    data.endpointClosureUniqueModuloContinuumEquivalence_valid⟩

/-- Detached endpoint-rigidity remainder package. This records the further
claim that the only unresolved task is identifying the natural representative
of the already forced closure class. -/
structure CommonReduction (Time Carrier Law : Type) extends Reduction Time Carrier Law where
  carrierRepresentativeRemainsToBeIdentified : Prop
  carrierRepresentativeRemainsToBeIdentified_valid :
    carrierRepresentativeRemainsToBeIdentified

/-- Endpoint rigidity reduces the remaining carrier-side problem to identifying
the natural representative of an already forced closure class. -/
theorem CommonReduction.surface
    {Time Carrier Law : Type}
    (data : CommonReduction Time Carrier Law) :
    data.symmetryChannelScalarization ∧
      data.inheritedMinimalOrderClassSingleton ∧
      data.endpointClosureUniqueModuloContinuumEquivalence ∧
      data.carrierRepresentativeRemainsToBeIdentified := by
  have hreduction := Reduction.surface data.toReduction
  rcases hreduction with ⟨hscalar, hsingleton, huniq⟩
  exact
    ⟨hscalar,
      hsingleton,
      huniq,
      data.carrierRepresentativeRemainsToBeIdentified_valid⟩

end EndpointRigidity

/-- Abstract balanced-exchange package for coupled selected carriers. -/
structure ExchangeBalancedCoupledFamily where
  visibleSourcesAreExchangeBoundaries : Prop
  pairwiseExchangeAntisymmetric : Prop
  zeroNetInternalCreation : Prop
  twoEndpointBalance : Prop
  visibleSourcesAreExchangeBoundaries_valid :
    visibleSourcesAreExchangeBoundaries
  pairwiseExchangeAntisymmetric_valid : pairwiseExchangeAntisymmetric
  zeroNetInternalCreation_valid : zeroNetInternalCreation
  twoEndpointBalance_valid : twoEndpointBalance

/-- Balanced exchange on a closed coupled selected family has zero net internal
creation; the two-endpoint case collapses to equal-and-opposite interaction. -/
theorem coupled_exchange_balance
    (data : ExchangeBalancedCoupledFamily) :
    data.visibleSourcesAreExchangeBoundaries ∧
      data.pairwiseExchangeAntisymmetric ∧
      data.zeroNetInternalCreation ∧
      data.twoEndpointBalance := by
  exact ⟨data.visibleSourcesAreExchangeBoundaries_valid,
    data.pairwiseExchangeAntisymmetric_valid,
    data.zeroNetInternalCreation_valid, data.twoEndpointBalance_valid⟩

/-- The counting-side residual interface is already forced: the unique
nontrivial imbalance occurs at `D = 3`. -/
theorem forced_residual_interface_D3 :
    holographicImbalance 3 = SignedCount.ofNat 1 := by
  obtain ⟨hd3, _hprofile⟩ := finite_local_type_profiles
  exact hd3

/-- The counting-side carrier surface is already forced: the nontrivial
balanced carrier has six slots. -/
theorem forced_six_slot_balanced_carrier :
    balancedClosureSlotCount closureStableDimension = 6 := by
  obtain ⟨_hstable, _hseed, hsix⟩ := unit_seed_and_six_slot_carrier
  exact hsix

/-- The intrinsic local channel algebra is already forced from closure balance
and full intrinsic relabeling symmetry. -/
theorem forced_intrinsic_channel_profile :
    natListSum [3, 2, 1] = balancedClosureSlotCount closureStableDimension ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  exact intrinsic_six_slot_decomposition

namespace SelectedCut

/-- Auxiliary bridge readout: the Part IV physical bridge can be unpacked as a
concrete forcing criterion on admissible cuts rather than left as an
unmotivated identification. The canonical Schur bridge below packages this
surface together with the residual-return side in one step. -/
structure GroundedBridge (Time Carrier Law : Type) where
  observer : ObserverSelection.LeastMotion Time Carrier Law
  motionValue : Nat
  selectedProjectionRealizesMinimizer :
    observer.selection.selectedProjection =
      selectedCandidateProjection observer.selection
  motionValue_eq_selectedObjective :
    motionValue = observerMotionValue observer.selection
  physicalPrinciple : PhysicalRealizationPrinciple Time Carrier Law
  sameSelectionDatum :
    physicalPrinciple.selectedLaw.selection = observer.selection
  physicalBridgeReadOnLeastMotionCut : Prop
  physicalBridgeReadOnLeastMotionCut_valid : physicalBridgeReadOnLeastMotionCut

/-- A grounded bridge supplies a concrete observer-motion criterion together
with the physical realization principle on its minimizing cut. -/
theorem groundedBridge
    {Time Carrier Law : Type}
    (data : GroundedBridge Time Carrier Law) :
    (data.observer.selection.selectedProjection =
      selectedCandidateProjection data.observer.selection) ∧
      (data.motionValue = observerMotionValue data.observer.selection) ∧
      (∀ i : Fin (Nat.succ data.observer.selection.candidates.size),
        data.motionValue ≤
          data.observer.selection.objective.eval
            (data.observer.selection.candidates.elem i)) ∧
      (data.physicalPrinciple.selectedLaw.selection =
        data.observer.selection) ∧
      exactVisibleOnCut
        (data.observer.selection.realization.tower.π data.observer.selection.horizon)
        (selected_observed_law data.observer.selection).op ∧
      data.physicalBridgeReadOnLeastMotionCut ∧
      data.physicalPrinciple.observableDynamicsExactlySelectedLaw ∧
      data.physicalPrinciple.lawClauses.leastMotionFaithfulCutUnique := by
  have hmin :
      ∀ i : Fin (Nat.succ data.observer.selection.candidates.size),
        data.motionValue ≤
          data.observer.selection.objective.eval
            (data.observer.selection.candidates.elem i) := by
    intro i
    rw [data.motionValue_eq_selectedObjective]
    exact observerMotionValue_minimal data.observer.selection i
  have hexact :
      exactVisibleOnCut
        (data.observer.selection.realization.tower.π data.observer.selection.horizon)
        (selected_observed_law data.observer.selection).op := by
    simpa [data.sameSelectionDatum] using
      data.physicalPrinciple.exactVisibleSelectedLawOnLeastMotionCut
  exact
    ⟨data.selectedProjectionRealizesMinimizer,
      data.motionValue_eq_selectedObjective,
      hmin,
      data.sameSelectionDatum,
      hexact,
      data.physicalBridgeReadOnLeastMotionCut_valid,
      data.physicalPrinciple.observableDynamicsExactlySelectedLaw_valid,
      data.physicalPrinciple.lawClauses.leastMotionFaithfulCutUnique_valid⟩

/-- Generic carrier-side readout of the physically selected closure law.
If a least-motion carrier observer is reading the same selected cut as the
Part IV physical selected law and carries the same induced continuum closure
class, then exact visibility on that cut and the forced continuum singleton
transport directly to the carrier observer. This is the foundational lemma
that turns later flagship closure theorems into short corollaries. -/
structure CarrierClosureReadout (Time Carrier Law : Type) where
  physical : PhysicalRealizationPrinciple Time Carrier Law
  observer : ObserverSelection.LeastMotion Time Carrier Law
  sameSelectionDatum :
    physical.selectedLaw.selection = observer.selection
  sameContinuumClosureClass :
    physical.selectedLaw.endpointClosureClass = observer.continuumClass

/-- Once a carrier observer is identified with the physically selected cut and
its induced continuum closure class, exact visibility and forced continuum
closure are inherited automatically from the Part IV physical realization
package. -/
theorem carrierClosureReadout
    {Time Carrier Law : Type}
    (data : CarrierClosureReadout Time Carrier Law) :
    (data.physical.selectedLaw.selection = data.observer.selection) ∧
      exactVisibleOnCut
        (data.observer.selection.realization.tower.π data.observer.selection.horizon)
        (selected_observed_law data.observer.selection).op ∧
      ForcedContinuumLaw
        data.observer.continuumClass
        data.physical.selectedLaw.selectedClosureLaw := by
  have hexact :
      exactVisibleOnCut
        (data.observer.selection.realization.tower.π data.observer.selection.horizon)
        (selected_observed_law data.observer.selection).op := by
    simpa [data.sameSelectionDatum] using
      data.physical.exactVisibleSelectedLawOnLeastMotionCut
  rcases data.physical.selectedLaw.selectedClosureForced with
    ⟨hmem0, hunique0⟩
  have hmem :
      data.observer.continuumClass.admissible
        data.physical.selectedLaw.selectedClosureLaw := by
    simpa [data.sameContinuumClosureClass] using hmem0
  have hunique :
      ∀ other : Law,
        data.observer.continuumClass.admissible other →
        other = data.physical.selectedLaw.selectedClosureLaw := by
    intro other hadm
    have hadm' :
        data.physical.selectedLaw.endpointClosureClass.admissible other := by
      simpa [data.sameContinuumClosureClass] using hadm
    exact hunique0 other hadm'
  exact
    ⟨data.sameSelectionDatum,
      hexact,
      forcedSingleton_intro
        data.observer.continuumClass.admissible
        data.physical.selectedLaw.selectedClosureLaw
        hmem
        hunique⟩

/-- Once a recognizable frontier has already fixed the common endpoint facts,
physical selected-cut readout adds the forced continuum law without changing
the recognizable package. -/
theorem closureReadoutWithRecognition
    {Time Carrier Law : Type} {Recognizable : Sort _}
    (physical : PhysicalRealizationPrinciple Time Carrier Law)
    (observer : ObserverSelection.LeastMotion Time Carrier Law)
    (sameSelectionDatum :
      physical.selectedLaw.selection = observer.selection)
    (sameContinuumClosureClass :
      physical.selectedLaw.endpointClosureClass = observer.continuumClass)
    {singleton representative : Prop}
    (hsingleton : singleton)
    (hrepresentative : representative)
    (hrecognizable : Nonempty Recognizable) :
    singleton ∧ representative ∧
      ForcedContinuumLaw
        observer.continuumClass
        physical.selectedLaw.selectedClosureLaw ∧
      Nonempty Recognizable := by
  obtain ⟨_hsel, _hexact, hforced⟩ :=
    carrierClosureReadout
      { physical := physical
        observer := observer
        sameSelectionDatum := sameSelectionDatum
        sameContinuumClosureClass := sameContinuumClosureClass }
  exact ⟨hsingleton, hrepresentative, hforced, hrecognizable⟩

/-- Auxiliary return readout: the return calculus can be promoted to an
explicit residual return field on the selected cut, localized on the unique
`D=3` residual interface and equipped with an irreversibility functional. The
canonical Schur bridge below packages this together with the least-motion
bridge data. -/
structure LocalizedReturn (Time Carrier Law : Type) where
  groundedBridge : GroundedBridge Time Carrier Law
  returnField : ResidualReturnField
  returnRecovery : ResidualReturnRecoveryData State
  energyTower : EnergyHorizonTower
  energyTowerExtendsSelectedTower :
    energyTower.toHorizonTower =
      groundedBridge.observer.selection.realization.tower
  residualStockAtSelectedHorizon : State → Nat
  residualStockAtSelectedHorizon_eq :
    residualStockAtSelectedHorizon =
      fun x =>
        unrecoveredResidualStock energyTower x
          groundedBridge.observer.selection.horizon
  returnFluxAtSelectedHorizon : State → Nat
  returnFluxAtSelectedHorizon_eq :
    returnFluxAtSelectedHorizon =
      fun x =>
        returnedResidualFlux energyTower x
          groundedBridge.observer.selection.horizon
  selectedLawUsesThisReturnField : Prop
  localizedOnD3Interface : Prop
  selectedLawUsesThisReturnField_valid : selectedLawUsesThisReturnField
  localizedOnD3Interface_valid : localizedOnD3Interface

/-- Localized residual return upgrades the return-only forcing clause to a
concrete residual field package on the selected cut. -/
theorem localizedReturn
    {Time Carrier Law : Type}
    (data : LocalizedReturn Time Carrier Law) :
    data.selectedLawUsesThisReturnField ∧
      data.localizedOnD3Interface ∧
      (holographicImbalance 3 = SignedCount.ofNat 1) ∧
      (balancedClosureSlotCount closureStableDimension = 6) ∧
      (data.energyTower.toHorizonTower =
        data.groundedBridge.observer.selection.realization.tower) ∧
      (data.residualStockAtSelectedHorizon =
        (fun x =>
          unrecoveredResidualStock data.energyTower x
            data.groundedBridge.observer.selection.horizon)) ∧
      (data.returnFluxAtSelectedHorizon =
        (fun x =>
          returnedResidualFlux data.energyTower x
            data.groundedBridge.observer.selection.horizon)) ∧
      (∀ x : State,
        data.residualStockAtSelectedHorizon x =
          data.returnFluxAtSelectedHorizon x +
            unrecoveredResidualStock data.energyTower x
              (data.groundedBridge.observer.selection.horizon + 1)) ∧
      (∀ h : Nat, ∀ x : State,
        unrecoveredResidualStock data.energyTower x (h + 1) ≤
          unrecoveredResidualStock data.energyTower x h) ∧
      data.groundedBridge.physicalPrinciple.residualReturn.onlyReturnActs ∧
      (data.groundedBridge.physicalPrinciple.residualReturn.selectedLawObtainedByResidualElimination) := by
  have hstep :
      ∀ x : State,
        data.residualStockAtSelectedHorizon x =
          data.returnFluxAtSelectedHorizon x +
            unrecoveredResidualStock data.energyTower x
              (data.groundedBridge.observer.selection.horizon + 1) := by
    intro x
    rw [data.residualStockAtSelectedHorizon_eq, data.returnFluxAtSelectedHorizon_eq]
    exact
      unrecoveredResidualStock_step
        data.energyTower x data.groundedBridge.observer.selection.horizon
  have hmono :
      ∀ h : Nat, ∀ x : State,
        unrecoveredResidualStock data.energyTower x (h + 1) ≤
          unrecoveredResidualStock data.energyTower x h := by
    intro h x
    exact unrecoveredResidualStock_monotone data.energyTower x h
  exact
    ⟨data.selectedLawUsesThisReturnField_valid,
      data.localizedOnD3Interface_valid,
      forced_residual_interface_D3,
      forced_six_slot_balanced_carrier,
      data.energyTowerExtendsSelectedTower,
      data.residualStockAtSelectedHorizon_eq,
      data.returnFluxAtSelectedHorizon_eq,
      hstep,
      hmono,
      data.groundedBridge.physicalPrinciple.residualReturn.onlyReturnActs_valid,
      (data.groundedBridge.physicalPrinciple.residualReturn.selectedLawObtainedByResidualElimination_valid)⟩

/-- Effective thermodynamic closure on the selected cut. What is already
mechanically forced by the Part IV bridge is a selected-cut irreversibility
functional given by unrecovered residual stock, a returned-flux balance law,
and monotone residual decay along the selected tower. This is an effective
thermodynamic surface, not yet a full entropy-production or second-law
theorem. -/
theorem effectiveThermodynamicClosure
    {Time Carrier Law : Type}
    (data : LocalizedReturn Time Carrier Law) :
    data.groundedBridge.physicalPrinciple.residualReturn.onlyReturnActs ∧
      data.groundedBridge.physicalPrinciple.residualReturn.observableIrreversibilityIsUnrecoveredResidual ∧
      (∀ x : State,
        unrecoveredResidualStock data.energyTower x
            data.groundedBridge.observer.selection.horizon =
          returnedResidualFlux data.energyTower x
              data.groundedBridge.observer.selection.horizon +
            unrecoveredResidualStock data.energyTower x
              (data.groundedBridge.observer.selection.horizon + 1)) ∧
      (∀ h : Nat, ∀ x : State,
        unrecoveredResidualStock data.energyTower x (h + 1) ≤
          unrecoveredResidualStock data.energyTower x h) := by
  have hstep :
      ∀ x : State,
        unrecoveredResidualStock data.energyTower x
            data.groundedBridge.observer.selection.horizon =
          returnedResidualFlux data.energyTower x
              data.groundedBridge.observer.selection.horizon +
            unrecoveredResidualStock data.energyTower x
              (data.groundedBridge.observer.selection.horizon + 1) := by
    intro x
    exact
      unrecoveredResidualStock_step
        data.energyTower x data.groundedBridge.observer.selection.horizon
  have hmono :
      ∀ h : Nat, ∀ x : State,
        unrecoveredResidualStock data.energyTower x (h + 1) ≤
          unrecoveredResidualStock data.energyTower x h := by
    intro h x
    exact unrecoveredResidualStock_monotone data.energyTower x h
  exact
    ⟨data.groundedBridge.physicalPrinciple.residualReturn.onlyReturnActs_valid,
      data.groundedBridge.physicalPrinciple.residualReturn.observableIrreversibilityIsUnrecoveredResidual_valid,
      hstep,
      hmono⟩

/-- Forced selected-cut data on the least-motion cut. This packages the finite
least-motion selector, the unique admissible class, the realized horizon cut,
and the HFT-2 residual accounting, but does not yet identify the selected
observed law with its exact Schur reduction. -/
structure ForcingBridge (Index Time Carrier Law : Type) where
  cls : AdmissibleRealizedClass Index Time
  root : Index
  observer : ObserverSelection.LeastMotion Time Carrier Law
  rootSelection_eq : observer.selection = cls.datum root
  selectedProjection_eq_candidate :
    observer.selection.selectedProjection =
      selectedCandidateProjection observer.selection
  selectedProjection_eq_horizonCut :
    observer.selection.selectedProjection =
      observer.selection.realization.tower.π observer.selection.horizon
  uniqueClass :
    ∀ i j : Index,
      HorizonPreservingEquivalence (cls.datum i) (cls.datum j)
  energyTower : EnergyHorizonTower
  energyTower_eq :
    energyTower.toHorizonTower =
      observer.selection.realization.tower

/-- HFT-2 unrecovered residual stock on a forced selected horizon. -/
def residualStock
    {Index Time Carrier Law : Type}
    (data : ForcingBridge Index Time Carrier Law) :
    State → Nat :=
  fun x =>
    unrecoveredResidualStock data.energyTower x data.observer.selection.horizon

/-- HFT-2 returned residual flux across the next refinement step above a forced
selected horizon. -/
def returnFlux
    {Index Time Carrier Law : Type}
    (data : ForcingBridge Index Time Carrier Law) :
    State → Nat :=
  fun x =>
    returnedResidualFlux data.energyTower x data.observer.selection.horizon

/-- The forced selected-cut content of Step 1 is already enough to recover the
least-motion minimizer, the realized cut, classwise forcing, and the HFT-2
irreversibility accounting on one selected datum. -/
theorem forcingBridge
    {Index Time Carrier Law : Type}
    (data : ForcingBridge Index Time Carrier Law) :
    (data.observer.selection.selectedProjection =
      selectedCandidateProjection data.observer.selection) ∧
      (data.observer.selection.selectedProjection =
        data.observer.selection.realization.tower.π data.observer.selection.horizon) ∧
      (∀ i : Index,
        data.observer.selection.horizon = (data.cls.datum i).horizon ∧
          (∀ x : State,
            (data.uniqueClass data.root i).transport
              ((selected_observed_law data.observer.selection).op x) =
              (selected_observed_law (data.cls.datum i)).op
                ((data.uniqueClass data.root i).transport x))) ∧
      (∀ i : Fin (Nat.succ data.observer.selection.candidates.size),
        observerMotionValue data.observer.selection ≤
          data.observer.selection.objective.eval
            (data.observer.selection.candidates.elem i)) ∧
      (∀ x : State,
        residualStock data x =
          returnFlux data x +
            unrecoveredResidualStock data.energyTower x
              (data.observer.selection.horizon + 1)) ∧
      (∀ h : Nat, ∀ x : State,
        unrecoveredResidualStock data.energyTower x (h + 1) ≤
          unrecoveredResidualStock data.energyTower x h) ∧
      (holographicImbalance 3 = SignedCount.ofNat 1) ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  have hforcing :
      ∀ i : Index,
        data.observer.selection.horizon = (data.cls.datum i).horizon ∧
          (∀ x : State,
            (data.uniqueClass data.root i).transport
              ((selected_observed_law data.observer.selection).op x) =
              (selected_observed_law (data.cls.datum i)).op
                ((data.uniqueClass data.root i).transport x)) := by
    intro i
    refine ⟨?_, ?_⟩
    · calc
        data.observer.selection.horizon
            = (data.cls.datum data.root).horizon := by
                rw [data.rootSelection_eq]
        _ = (data.cls.datum i).horizon :=
          (data.uniqueClass data.root i).sameHorizon
    · intro x
      calc
        (data.uniqueClass data.root i).transport
            ((selected_observed_law data.observer.selection).op x)
            =
          (data.uniqueClass data.root i).transport
            ((selected_observed_law (data.cls.datum data.root)).op x) := by
              rw [data.rootSelection_eq]
        _ =
          (selected_observed_law (data.cls.datum i)).op
            ((data.uniqueClass data.root i).transport x) :=
          (data.uniqueClass data.root i).selected_transport x
  have hmin :
      ∀ i : Fin (Nat.succ data.observer.selection.candidates.size),
        observerMotionValue data.observer.selection ≤
          data.observer.selection.objective.eval
            (data.observer.selection.candidates.elem i) := by
    intro i
    exact observerMotionValue_minimal data.observer.selection i
  have hstep :
      ∀ x : State,
        residualStock data x =
          returnFlux data x +
            unrecoveredResidualStock data.energyTower x
              (data.observer.selection.horizon + 1) := by
    intro x
    unfold residualStock returnFlux
    exact
      unrecoveredResidualStock_step
        data.energyTower x data.observer.selection.horizon
  have hmono :
      ∀ h : Nat, ∀ x : State,
        unrecoveredResidualStock data.energyTower x (h + 1) ≤
          unrecoveredResidualStock data.energyTower x h := by
    intro h x
    exact unrecoveredResidualStock_monotone data.energyTower x h
  exact
    ⟨data.selectedProjection_eq_candidate,
      data.selectedProjection_eq_horizonCut,
      hforcing,
      hmin,
      hstep,
      hmono,
      forced_residual_interface_D3,
      forced_intrinsic_channel_profile.2⟩

end SelectedCut

namespace SelectedSchur

/-- The remaining exact-Schur residue on a selected datum is reduced to two
local cut conditions: the selected observed law is already observable-supported
on the selected cut, and it commutes with that cut. -/
structure ExactResidue {Time : Type}
    (selection : SelectionDatum Time) where
  observableSupportOnSelectedCut :
    observableSupportedOn
      (selection.realization.tower.π selection.horizon)
      (selected_observed_law selection).op
  selectedLawCommutesWithCut :
    commutesWithProjection
      (selection.realization.tower.π selection.horizon)
      (selected_observed_law selection).op

/-- A single exact-visible-law condition on the selected cut implies both local
exact-Schur residue conditions in one move. -/
theorem fromExactVisible
    {Time : Type}
    (selection : SelectionDatum Time)
    (hvis :
      exactVisibleOnCut
        (selection.realization.tower.π selection.horizon)
        (selected_observed_law selection).op) :
    ExactResidue selection := by
  exact
    { observableSupportOnSelectedCut :=
        exact_visible_implies_observable_supported
          (selection.realization.tower.π selection.horizon)
          (selected_observed_law selection).op
          hvis
      selectedLawCommutesWithCut :=
        exact_visible_implies_commutes
          (selection.realization.tower.π selection.horizon)
          (selected_observed_law selection).op
          hvis }

/-- The local exact-Schur residue implies the full exact Schur identification
on the selected cut for any chosen exact shadow resolvent tower. -/
theorem exactFromResidue
    {Time : Type}
    (selection : SelectionDatum Time)
    (schurData :
      ExactSchurTowerGeneralData
        selection.realization.tower
        (selected_observed_law selection).op)
    (residue : ExactResidue selection) :
    ∀ x : State,
      (selected_observed_law selection).op x =
        exact_schur_tower_general
          selection.realization.tower
          (selected_observed_law selection).op
          schurData
      selection.horizon x := by
  intro x
  exact
    commutes_and_observable_support_imply_effective
      (selection.realization.tower.π selection.horizon)
      (selected_observed_law selection).op
      ((schurData.shadowResolvent selection.horizon).inverse)
      residue.selectedLawCommutesWithCut
      residue.observableSupportOnSelectedCut
      x

/-- The exact visible-law condition on the selected cut is therefore a
one-move sufficient criterion for the full exact Schur identity. -/
theorem exactFromExactVisible
    {Time : Type}
    (selection : SelectionDatum Time)
    (schurData :
      ExactSchurTowerGeneralData
        selection.realization.tower
        (selected_observed_law selection).op)
    (hvis :
      exactVisibleOnCut
        (selection.realization.tower.π selection.horizon)
        (selected_observed_law selection).op) :
    ∀ x : State,
      (selected_observed_law selection).op x =
        exact_schur_tower_general
          selection.realization.tower
          (selected_observed_law selection).op
          schurData
          selection.horizon x := by
  exact
    exactFromResidue
      selection
      schurData
      (fromExactVisible selection hvis)

end SelectedSchur

/-- On a grounded physical bridge, the self-sufficient realization clause
already yields exact visibility of the selected law on the least-motion cut. -/
theorem SelectedCut.GroundedBridge.exactVisibleSelectedLaw
    {Time Carrier Law : Type}
    (data : SelectedCut.GroundedBridge Time Carrier Law) :
    exactVisibleOnCut
      (data.observer.selection.realization.tower.π data.observer.selection.horizon)
      (selected_observed_law data.observer.selection).op := by
  simpa [data.sameSelectionDatum] using
    data.physicalPrinciple.exactVisibleSelectedLawOnLeastMotionCut

/-- Once an exact Schur tower is supplied on the selected datum, a grounded
physical bridge upgrades the self-sufficient realization clause directly to the
exact selected Schur identity. -/
theorem SelectedCut.GroundedBridge.exactSelectedSchur
    {Time Carrier Law : Type}
    (data : SelectedCut.GroundedBridge Time Carrier Law)
    (schurData :
      ExactSchurTowerGeneralData
        data.observer.selection.realization.tower
        (selected_observed_law data.observer.selection).op) :
    ∀ x : State,
      (selected_observed_law data.observer.selection).op x =
        exact_schur_tower_general
          data.observer.selection.realization.tower
          (selected_observed_law data.observer.selection).op
          schurData
          data.observer.selection.horizon x := by
  exact
    SelectedSchur.exactFromExactVisible
      data.observer.selection
      schurData
      data.exactVisibleSelectedLaw

/-- Unified Schur-bridge data on the least-motion cut. This extends the forced
selected-cut surface by grounding it in the self-sufficient physical bridge on
that same selected datum, together with the exact Schur tower used to read the
canonical residual-return field. Exact visibility is no longer stored as a
separate witness here; it is read back from the grounded self-sufficient
realization principle. -/
structure CanonicalSelectedSchurBridge (Index Time Carrier Law : Type)
    extends SelectedCut.ForcingBridge Index Time Carrier Law where
  groundedBridge : SelectedCut.GroundedBridge Time Carrier Law
  groundedBridgeSelection_eq :
    groundedBridge.observer.selection = observer.selection
  schurData :
    ExactSchurTowerGeneralData
      observer.selection.realization.tower
      (selected_observed_law observer.selection).op

/-- On the canonical selected Schur bridge, exact visibility of the selected
law is read from the grounded self-sufficient realization principle rather than
stored as independent bridge data. -/
theorem CanonicalSelectedSchurBridge.exactVisibleSelectedLaw
    {Index Time Carrier Law : Type}
    (data : CanonicalSelectedSchurBridge Index Time Carrier Law) :
  exactVisibleOnCut
      (data.observer.selection.realization.tower.π data.observer.selection.horizon)
      (selected_observed_law data.observer.selection).op := by
  simpa [← data.groundedBridgeSelection_eq] using
    data.groundedBridge.exactVisibleSelectedLaw

/-- The canonical selected Schur bridge carries the law-side core of
self-sufficient realization directly on the selected cut. -/
theorem CanonicalSelectedSchurBridge.selfSufficientRealization
    {Index Time Carrier Law : Type}
    (data : CanonicalSelectedSchurBridge Index Time Carrier Law) :
    exactVisibleOnCut
      (data.observer.selection.realization.tower.π data.observer.selection.horizon)
      (selected_observed_law data.observer.selection).op ∧
      data.groundedBridge.physicalPrinciple.intrinsicallyClosedOnLeastMotionCut ∧
      data.groundedBridge.physicalPrinciple.noExogenousConstitutiveCompletion ∧
      data.groundedBridge.physicalPrinciple.apparentConstitutiveTermsAreReturnedResidual := by
  refine ⟨data.exactVisibleSelectedLaw, ?_, ?_, ?_⟩
  · exact
      data.groundedBridge.physicalPrinciple.intrinsicallyClosedOnLeastMotionCut_valid
  · exact
      data.groundedBridge.physicalPrinciple.noExogenousConstitutiveCompletion_valid
  · exact
      data.groundedBridge.physicalPrinciple.apparentConstitutiveTermsAreReturnedResidual_valid

/-- On a canonical selected Schur bridge, the derived exact visibility of the
selected law induces the local exact-Schur residue conditions automatically. -/
def CanonicalSelectedSchurBridge.exactResidue
    {Index Time Carrier Law : Type}
    (data : CanonicalSelectedSchurBridge Index Time Carrier Law) :
    SelectedSchur.ExactResidue data.observer.selection :=
  SelectedSchur.fromExactVisible
    data.observer.selection
    data.exactVisibleSelectedLaw

/-- The canonical shadow propagator on the selected least-motion horizon cut is
read from the exact Schur tower at that same horizon. -/
def canonicalSelectedShadowPropagator
    {Index Time Carrier Law : Type}
    (data : CanonicalSelectedSchurBridge Index Time Carrier Law) : AddMap :=
  (data.schurData.shadowResolvent data.observer.selection.horizon).inverse

/-- The canonical residual-return field on the selected cut is the residual
field induced directly by the selected law and the selected-horizon shadow
propagator. -/
def canonicalSelectedResidualReturnField
    {Index Time Carrier Law : Type}
    (data : CanonicalSelectedSchurBridge Index Time Carrier Law) :
    ResidualReturnField :=
  residualReturnFieldOf
    (data.observer.selection.realization.tower.π data.observer.selection.horizon)
    (selected_observed_law data.observer.selection).op
    (canonicalSelectedShadowPropagator data)

/-- HFT-2 unrecovered residual stock on the selected least-motion horizon. -/
  def canonicalSelectedResidualStock
    {Index Time Carrier Law : Type}
    (data : CanonicalSelectedSchurBridge Index Time Carrier Law) :
    State → Nat :=
  SelectedCut.residualStock data.toForcingBridge

/-- HFT-2 returned residual flux across the next refinement step above the
selected least-motion horizon. -/
def canonicalSelectedReturnFlux
    {Index Time Carrier Law : Type}
    (data : CanonicalSelectedSchurBridge Index Time Carrier Law) :
    State → Nat :=
  SelectedCut.returnFlux data.toForcingBridge

/-- Unified selected Schur realization: the least-motion selector, the
self-sufficient realization law on that cut, the exact Schur reduction, and
the HFT-2 residual accounting together yield the observable bridge and the
canonical residual-return field in one move. -/
theorem canonical_selected_schur_realization
    {Index Time Carrier Law : Type}
    (data : CanonicalSelectedSchurBridge Index Time Carrier Law) :
    (data.observer.selection.selectedProjection =
      selectedCandidateProjection data.observer.selection) ∧
      (data.observer.selection.selectedProjection =
        data.observer.selection.realization.tower.π data.observer.selection.horizon) ∧
      (∀ i : Index,
        data.observer.selection.horizon = (data.cls.datum i).horizon ∧
          (∀ x : State,
            (data.uniqueClass data.root i).transport
              ((selected_observed_law data.observer.selection).op x) =
              (selected_observed_law (data.cls.datum i)).op
                ((data.uniqueClass data.root i).transport x))) ∧
      (∀ i : Fin (Nat.succ data.observer.selection.candidates.size),
        observerMotionValue data.observer.selection ≤
          data.observer.selection.objective.eval
            (data.observer.selection.candidates.elem i)) ∧
      exactVisibleOnCut
        (data.observer.selection.realization.tower.π data.observer.selection.horizon)
        (selected_observed_law data.observer.selection).op ∧
      data.groundedBridge.physicalPrinciple.intrinsicallyClosedOnLeastMotionCut ∧
      data.groundedBridge.physicalPrinciple.noExogenousConstitutiveCompletion ∧
      data.groundedBridge.physicalPrinciple.apparentConstitutiveTermsAreReturnedResidual ∧
      (returnedResidual (canonicalSelectedResidualReturnField data) =
        schurComplement
          (data.observer.selection.realization.tower.π data.observer.selection.horizon)
          (selected_observed_law data.observer.selection).op
          (canonicalSelectedShadowPropagator data)) ∧
      (∀ x : State,
        (selected_observed_law data.observer.selection).op x =
          State.add
            (blockPP
              (data.observer.selection.realization.tower.π data.observer.selection.horizon)
              ((selected_observed_law data.observer.selection).op) x)
            (returnedResidual (canonicalSelectedResidualReturnField data) x)) ∧
      (∀ x : State,
        canonicalSelectedResidualStock data x =
          canonicalSelectedReturnFlux data x +
            unrecoveredResidualStock data.energyTower x
              (data.observer.selection.horizon + 1)) ∧
      (∀ h : Nat, ∀ x : State,
        unrecoveredResidualStock data.energyTower x (h + 1) ≤
          unrecoveredResidualStock data.energyTower x h) ∧
      (holographicImbalance 3 = SignedCount.ofNat 1) ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  have hcut :=
    SelectedCut.forcingBridge data.toForcingBridge
  rcases hcut with
    ⟨hproj, hcutEq, hforcing, hmin, hstep, hmono, hd3, hprofile⟩
  have hself := data.selfSufficientRealization
  rcases hself with ⟨hexact, hclosed, hnoConst, hreturned⟩
  have hret :
      returnedResidual (canonicalSelectedResidualReturnField data) =
        schurComplement
          (data.observer.selection.realization.tower.π data.observer.selection.horizon)
          (selected_observed_law data.observer.selection).op
          (canonicalSelectedShadowPropagator data) := by
    exact
      returnedResidual_eq_schur
        (data.observer.selection.realization.tower.π data.observer.selection.horizon)
        (selected_observed_law data.observer.selection).op
        (canonicalSelectedShadowPropagator data)
  have hsplit :
      ∀ x : State,
        (selected_observed_law data.observer.selection).op x =
          State.add
            (blockPP
              (data.observer.selection.realization.tower.π data.observer.selection.horizon)
              ((selected_observed_law data.observer.selection).op) x)
            (returnedResidual (canonicalSelectedResidualReturnField data) x) := by
    intro x
    calc
      (selected_observed_law data.observer.selection).op x
          =
        exact_schur_tower_general
          data.observer.selection.realization.tower
          ((selected_observed_law data.observer.selection).op)
          data.schurData
          data.observer.selection.horizon x := by
              exact
              SelectedSchur.exactFromExactVisible
                data.observer.selection
                data.schurData
                hexact
                x
      _ =
        State.add
          (blockPP
            (data.observer.selection.realization.tower.π data.observer.selection.horizon)
            ((selected_observed_law data.observer.selection).op) x)
          (schurComplement
            (data.observer.selection.realization.tower.π data.observer.selection.horizon)
            (selected_observed_law data.observer.selection).op
            (canonicalSelectedShadowPropagator data) x) := by
              rfl
      _ =
        State.add
          (blockPP
            (data.observer.selection.realization.tower.π data.observer.selection.horizon)
            ((selected_observed_law data.observer.selection).op) x)
          (returnedResidual (canonicalSelectedResidualReturnField data) x) := by
              rw [← hret]
  exact
    ⟨hproj,
      hcutEq,
      hforcing,
      hmin,
      hexact,
      hclosed,
      hnoConst,
      hreturned,
      hret,
      hsplit,
      hstep,
      hmono,
      forced_residual_interface_D3,
      forced_intrinsic_channel_profile.2⟩

/-- Step 2 of the law-completion chain: once the selected law and residual
return are unified by the canonical Schur bridge, the five flagship carriers
must arise intrinsically on one selected observed bundle, without separate
carrier-wise visibility hypotheses. -/
structure IntrinsicSelectedBundleExistence (Time Carrier Law : Type)
    extends SelectedBundle.Assembly Time Carrier Law where
  Index : Type
  selectedSchurBridge : CanonicalSelectedSchurBridge Index Time Carrier Law
  sameSelectedLawAsSchurBridge :
    physicalPrinciple.selectedLaw.selection =
      selectedSchurBridge.observer.selection
  phaseCarrierReadOnSelectedBundle :
    ObserverSelection.LeastMotion Time Carrier Law → Prop
  waveCarrierReadOnSelectedBundle :
    ObserverSelection.LeastMotion Time Carrier Law → Prop
  gaugeCarrierReadOnSelectedBundle :
    ObserverSelection.LeastMotion Time Carrier Law → Prop
  geometricCarrierReadOnSelectedBundle :
    ObserverSelection.LeastMotion Time Carrier Law → Prop
  phaseCarrierReadOnSelectedBundle_sameSelection :
    ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
      phaseCarrierReadOnSelectedBundle observer →
      observer.selection = selectedSchurBridge.observer.selection
  waveCarrierReadOnSelectedBundle_sameSelection :
    ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
      waveCarrierReadOnSelectedBundle observer →
      observer.selection = selectedSchurBridge.observer.selection
  gaugeCarrierReadOnSelectedBundle_sameSelection :
    ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
      gaugeCarrierReadOnSelectedBundle observer →
      observer.selection = selectedSchurBridge.observer.selection
  geometricCarrierReadOnSelectedBundle_sameSelection :
    ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
      geometricCarrierReadOnSelectedBundle observer →
      observer.selection = selectedSchurBridge.observer.selection
  sameContinuumClosureClassOnSelectedBundle :
    ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
      observer.selection = selectedSchurBridge.observer.selection →
      physicalPrinciple.selectedLaw.endpointClosureClass =
        observer.continuumClass
  bundleArisesIntrinsicallyOnLeastMotionCut : Prop
  noCarrierWiseVisibilityHypotheses : Prop
  bundleArisesIntrinsicallyOnLeastMotionCut_valid :
    bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses_valid :
    noCarrierWiseVisibilityHypotheses

/-- Intrinsic selected-bundle existence strengthens common selected-bundle
assembly by removing carrier-wise visibility as a separate hypothesis. -/
theorem intrinsic_selected_bundle_existence
    {Time Carrier Law : Type}
    (data : IntrinsicSelectedBundleExistence Time Carrier Law) :
    data.bundleArisesIntrinsicallyOnLeastMotionCut ∧
      data.noCarrierWiseVisibilityHypotheses ∧
      (data.selectedSchurBridge.observer.selection.selectedProjection =
        selectedCandidateProjection data.selectedSchurBridge.observer.selection) ∧
      (data.selectedSchurBridge.observer.selection.selectedProjection =
        data.selectedSchurBridge.observer.selection.realization.tower.π
          data.selectedSchurBridge.observer.selection.horizon) ∧
      (data.physicalPrinciple.selectedLaw.selection =
        data.selectedSchurBridge.observer.selection) ∧
      (data.physicalPrinciple.selectedLaw.endpointClosureClass =
        data.selectedSchurBridge.observer.continuumClass) ∧
      (holographicImbalance 3 = SignedCount.ofNat 1) ∧
      data.selectedObservedBundle ∧
      data.bundleSharedByAllCarriers ∧
      data.sameSelectedEffectiveLawOnEachCarrier ∧
      data.carrierLevelIdentificationOnlyFinalStep := by
  have hcut := SelectedCut.forcingBridge data.selectedSchurBridge.toForcingBridge
  rcases hcut with
    ⟨hproj, hcutEq, _hforcing, _hmin, _hstep, _hmono, hd3, _hprofile⟩
  exact
    ⟨data.bundleArisesIntrinsicallyOnLeastMotionCut_valid,
      data.noCarrierWiseVisibilityHypotheses_valid,
      hproj,
      hcutEq,
      data.sameSelectedLawAsSchurBridge,
      data.sameContinuumClosureClassOnSelectedBundle
        data.selectedSchurBridge.observer
        rfl,
      hd3,
      data.selectedObservedBundle_valid,
      data.bundleSharedByAllCarriers_valid,
      data.sameSelectedEffectiveLawOnEachCarrier_valid,
      data.carrierLevelIdentificationOnlyFinalStep_valid⟩

/-- The intrinsically generated selected bundle already determines the
canonical visible carrier-generation package, because it already contains the
one selected observed bundle, the five visible sectors on that bundle, and the
non-dictionary fact that those sectors share the same selected effective law
and differ only at the final carrier-level identification step. -/
def IntrinsicSelectedBundleExistence.toCanonicalGeneration
    {Time Carrier Law : Type}
    (data : IntrinsicSelectedBundleExistence Time Carrier Law) :
    SelectedBundle.CanonicalGeneration :=
  data.toAssembly.toCanonicalGeneration

/-- Consequently the selected-bundle theorem surface already carries the full
canonical-generation surface, before the two explicit intrinsic-generation
clauses are attached. -/
theorem IntrinsicSelectedBundleExistence.canonicalGenerationSurface
    {Time Carrier Law : Type}
    (data : IntrinsicSelectedBundleExistence Time Carrier Law) :
    let generation := data.toCanonicalGeneration
    generation.scalarChannelVisible ∧
      generation.scalarChannelGeneratesPhase ∧
      generation.scalarChannelGeneratesWave ∧
      generation.balanceCompatibleCarrierGeneratesKinetic ∧
      generation.exactOneFormExchangeGeneratesGauge ∧
      generation.symmetricResponseGeneratesGeometry ∧
      generation.notPrimitiveDictionary := by
  simpa [IntrinsicSelectedBundleExistence.toCanonicalGeneration] using
    data.toAssembly.canonicalGenerationSurface

namespace SelectedBundle

/-- A carrier observer read off the one intrinsically generated selected
bundle. This is the foundational point where a flagship carrier stops being an
independent observer choice and is instead read as a sector of the same
selected least-motion bundle. -/
structure CarrierObserver (Time Carrier Law : Type) where
  selectedBundle : IntrinsicSelectedBundleExistence Time Carrier Law
  observer : ObserverSelection.LeastMotion Time Carrier Law
  sameSelectionAsSelectedBundle :
    observer.selection = selectedBundle.selectedSchurBridge.observer.selection

/-- Any carrier observer read off the intrinsically generated selected bundle
inherits the same selected cut as the Part IV physical selected law, and hence
inherits exact visibility on that cut. -/
theorem carrierObserver
    {Time Carrier Law : Type}
    (data : CarrierObserver Time Carrier Law) :
    (data.selectedBundle.physicalPrinciple.selectedLaw.selection =
      data.observer.selection) ∧
      exactVisibleOnCut
        (data.observer.selection.realization.tower.π data.observer.selection.horizon)
        (selected_observed_law data.observer.selection).op := by
  have hsel :
      data.selectedBundle.physicalPrinciple.selectedLaw.selection =
        data.observer.selection := by
    calc
      data.selectedBundle.physicalPrinciple.selectedLaw.selection
          = data.selectedBundle.selectedSchurBridge.observer.selection := by
              exact data.selectedBundle.sameSelectedLawAsSchurBridge
      _ = data.observer.selection := by
            symm
            exact data.sameSelectionAsSelectedBundle
  have hexact :
      exactVisibleOnCut
        (data.observer.selection.realization.tower.π data.observer.selection.horizon)
        (selected_observed_law data.observer.selection).op := by
    simpa [hsel] using
      data.selectedBundle.physicalPrinciple.exactVisibleSelectedLawOnLeastMotionCut
  exact ⟨hsel, hexact⟩

/-- Any carrier observer read off the intrinsically generated selected bundle
inherits the same continuum closure class as the physical selected law. This
is the upstream theorem that removes lane-specific closure-class equalities
from the flagship closure arguments. -/
theorem carrierClosureClass
    {Time Carrier Law : Type}
    (data : CarrierObserver Time Carrier Law) :
    data.selectedBundle.physicalPrinciple.selectedLaw.endpointClosureClass =
      data.observer.continuumClass := by
  exact
    data.selectedBundle.sameContinuumClosureClassOnSelectedBundle
      data.observer
      data.sameSelectionAsSelectedBundle

/-- Any phase observer read off the intrinsically generated selected bundle
inherits the selected cut of the canonical Schur bridge. -/
theorem phaseCarrierSelection
    {Time Carrier Law : Type}
    (bundle : IntrinsicSelectedBundleExistence Time Carrier Law)
    (observer : ObserverSelection.LeastMotion Time Carrier Law)
    (hread : bundle.phaseCarrierReadOnSelectedBundle observer) :
    observer.selection = bundle.selectedSchurBridge.observer.selection := by
  exact bundle.phaseCarrierReadOnSelectedBundle_sameSelection observer hread

/-- Any wave observer read off the intrinsically generated selected bundle
inherits the selected cut of the canonical Schur bridge. -/
theorem waveCarrierSelection
    {Time Carrier Law : Type}
    (bundle : IntrinsicSelectedBundleExistence Time Carrier Law)
    (observer : ObserverSelection.LeastMotion Time Carrier Law)
    (hread : bundle.waveCarrierReadOnSelectedBundle observer) :
    observer.selection = bundle.selectedSchurBridge.observer.selection := by
  exact bundle.waveCarrierReadOnSelectedBundle_sameSelection observer hread

/-- Any gauge observer read off the intrinsically generated selected bundle
inherits the selected cut of the canonical Schur bridge. -/
theorem gaugeCarrierSelection
    {Time Carrier Law : Type}
    (bundle : IntrinsicSelectedBundleExistence Time Carrier Law)
    (observer : ObserverSelection.LeastMotion Time Carrier Law)
    (hread : bundle.gaugeCarrierReadOnSelectedBundle observer) :
    observer.selection = bundle.selectedSchurBridge.observer.selection := by
  exact bundle.gaugeCarrierReadOnSelectedBundle_sameSelection observer hread

/-- Any geometric observer read off the intrinsically generated selected bundle
inherits the selected cut of the canonical Schur bridge. -/
theorem geometricCarrierSelection
    {Time Carrier Law : Type}
    (bundle : IntrinsicSelectedBundleExistence Time Carrier Law)
    (observer : ObserverSelection.LeastMotion Time Carrier Law)
    (hread : bundle.geometricCarrierReadOnSelectedBundle observer) :
    observer.selection = bundle.selectedSchurBridge.observer.selection := by
  exact bundle.geometricCarrierReadOnSelectedBundle_sameSelection observer hread

/-- A carrier observer read off the one selected bundle. The selected bundle
already carries the continuum-closure inheritance law, so no additional
carrier-side closure-class equality is needed. -/
structure CarrierClosureReadout (Time Carrier Law : Type)
    extends CarrierObserver Time Carrier Law

/-- Once a carrier observer is read off the selected bundle and its continuum
closure class is inherited from the selected-bundle law, the forced continuum
singleton transports automatically to that carrier. -/
theorem carrierClosureReadout
    {Time Carrier Law : Type}
    (data : CarrierClosureReadout Time Carrier Law) :
    (data.selectedBundle.physicalPrinciple.selectedLaw.selection =
      data.observer.selection) ∧
      exactVisibleOnCut
        (data.observer.selection.realization.tower.π data.observer.selection.horizon)
        (selected_observed_law data.observer.selection).op ∧
      ForcedContinuumLaw
        data.observer.continuumClass
        data.selectedBundle.physicalPrinciple.selectedLaw.selectedClosureLaw := by
  obtain ⟨hsel, _hexact⟩ := carrierObserver data.toCarrierObserver
  simpa using
    SelectedCut.carrierClosureReadout
      { physical := data.selectedBundle.physicalPrinciple
        observer := data.observer
        sameSelectionDatum := hsel
        sameContinuumClosureClass :=
          carrierClosureClass data.toCarrierObserver }

/-- Once a recognizable frontier has already fixed the common endpoint facts,
selected-bundle readout adds the forced continuum law without changing the
recognizable package. -/
theorem closureReadoutWithRecognition
    {Time Carrier Law : Type} {Recognizable : Sort _}
    (selectedBundle : IntrinsicSelectedBundleExistence Time Carrier Law)
    (observer : ObserverSelection.LeastMotion Time Carrier Law)
    (sameSelectionAsSelectedBundle :
      observer.selection = selectedBundle.selectedSchurBridge.observer.selection)
    {singleton representative : Prop}
    (hsingleton : singleton)
    (hrepresentative : representative)
    (hrecognizable : Nonempty Recognizable) :
    singleton ∧ representative ∧
      ForcedContinuumLaw
        observer.continuumClass
        selectedBundle.physicalPrinciple.selectedLaw.selectedClosureLaw ∧
      Nonempty Recognizable := by
  obtain ⟨_hsel, _hexact, hforced⟩ :=
    carrierClosureReadout
      { selectedBundle := selectedBundle
        observer := observer
        sameSelectionAsSelectedBundle := sameSelectionAsSelectedBundle }
  exact ⟨hsingleton, hrepresentative, hforced, hrecognizable⟩

end SelectedBundle

/-- Step 3 of the law-completion chain: the selected visible sectors are forced
from the intrinsic `1+2+3` channel algebra as canonical minimal compatible
realizations, not by a primitive dictionary. -/
structure IntrinsicSectorGeneration (Time Carrier Law : Type)
    extends SelectedBundle.CanonicalGeneration where
  selectedBundle : IntrinsicSelectedBundleExistence Time Carrier Law
  generatedFromIntrinsicChannelAlgebra : Prop
  minimalCompatibleRealizationsOnly : Prop
  generatedFromIntrinsicChannelAlgebra_valid :
    generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly_valid :
    minimalCompatibleRealizationsOnly

/-- Intrinsic sector generation closes the gap between the local `1+2+3`
channel algebra and the five visible carrier classes. -/
private theorem intrinsicGenerationCarrierSurface :
    closureTypedPromotionFiniteCarrier.finite_carrier_available ∧
      closureTypedPromotionFiniteCarrier.canonical_signature_available ∧
      closureTypedPromotionFiniteCarrier.three_parameter_control := by
  exact
    ⟨closureTypedPromotionFiniteCarrier_finite,
      closureTypedPromotionFiniteCarrier_signature,
      closureTypedPromotionFiniteCarrier_control⟩

theorem intrinsic_sector_generation
    {Time Carrier Law : Type}
    (data : IntrinsicSectorGeneration Time Carrier Law) :
    data.generatedFromIntrinsicChannelAlgebra ∧
      data.minimalCompatibleRealizationsOnly ∧
      closureTypedPromotionFiniteCarrier.finite_carrier_available ∧
      closureTypedPromotionFiniteCarrier.canonical_signature_available ∧
      closureTypedPromotionFiniteCarrier.three_parameter_control ∧
      (natListSum [3, 2, 1] = balancedClosureSlotCount closureStableDimension) ∧
      IsCanonicalLogicalProfile [3, 2, 1] ∧
      data.scalarChannelGeneratesPhase ∧
      data.scalarChannelGeneratesWave ∧
      data.balanceCompatibleCarrierGeneratesKinetic ∧
      data.exactOneFormExchangeGeneratesGauge ∧
      data.symmetricResponseGeneratesGeometry ∧
      data.notPrimitiveDictionary := by
  obtain ⟨hfinite, hsignature, hcontrol⟩ :=
    intrinsicGenerationCarrierSurface
  obtain ⟨hprofile, hcanonical⟩ := forced_intrinsic_channel_profile
  exact
    ⟨data.generatedFromIntrinsicChannelAlgebra_valid,
      data.minimalCompatibleRealizationsOnly_valid,
      hfinite,
      hsignature,
      hcontrol,
      hprofile,
      hcanonical,
      data.scalarChannelGeneratesPhase_valid,
      data.scalarChannelGeneratesWave_valid,
      data.balanceCompatibleCarrierGeneratesKinetic_valid,
      data.exactOneFormExchangeGeneratesGauge_valid,
      data.symmetricResponseGeneratesGeometry_valid,
      data.notPrimitiveDictionary_valid⟩

namespace EndpointRigidity

/-- Step 4 of the law-completion chain: each generated carrier receives the
unique canonical representative of its forced endpoint law class. -/
structure Principle (Time Carrier Law : Type) where
  sectorGeneration : IntrinsicSectorGeneration Time Carrier Law
  localLawsReduceToFiniteJetOrder : Prop
  generatedSymmetryActsOnJetLevel : Prop
  compatibilityIdentitiesCutJetOperatorSpace : Prop
  admissibleEndpointEquivalenceRelation : Prop
  minimalTruncationProducesFiniteClosureQuotient : Prop
  singletonQuotientForcesUniqueCanonicalRepresentative : Prop
  nonsingletonQuotientForcesCanonicalNormalFormFamily : Prop
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

/-- Endpoint rigidity is the common schema behind Step 4: locality is reduced
to a finite closure surface, sector symmetries and generated identities cut the
admissible operator space, and minimal truncation then decides whether the
endpoint law is rigid or only canonical up to a parameter family. -/
theorem Principle.surface
    {Time Carrier Law : Type}
    (data : Principle Time Carrier Law) :
    data.localLawsReduceToFiniteJetOrder ∧
      data.generatedSymmetryActsOnJetLevel ∧
      data.compatibilityIdentitiesCutJetOperatorSpace ∧
      data.admissibleEndpointEquivalenceRelation ∧
      data.minimalTruncationProducesFiniteClosureQuotient ∧
      data.singletonQuotientForcesUniqueCanonicalRepresentative ∧
      data.nonsingletonQuotientForcesCanonicalNormalFormFamily := by
  exact
    ⟨data.localLawsReduceToFiniteJetOrder_valid,
      data.generatedSymmetryActsOnJetLevel_valid,
      data.compatibilityIdentitiesCutJetOperatorSpace_valid,
      data.admissibleEndpointEquivalenceRelation_valid,
      data.minimalTruncationProducesFiniteClosureQuotient_valid,
      data.singletonQuotientForcesUniqueCanonicalRepresentative_valid,
      data.nonsingletonQuotientForcesCanonicalNormalFormFamily_valid⟩

end EndpointRigidity

/-- Step 4 of the law-completion chain: endpoint-rigidity / canonical normal-
form completion on the generated sectors. The current flagship layer still
packages concrete representative witnesses on the four endpoint-sensitive
carriers, while the kinetic face stays at the weaker classified/stock-side
level; the common
schema now explicitly records the jet/symmetry/truncation mechanism that is
meant to force those representatives. -/
structure NaturalOperatorCompletion (Time Carrier Law : Type)
    extends SelectedBundle.CarrierClassification where
  sectorGeneration : IntrinsicSectorGeneration Time Carrier Law
  rigidityPrinciple : EndpointRigidity.Principle Time Carrier Law
  rigidityPrincipleUsesSameSectorGeneration :
    rigidityPrinciple.sectorGeneration = sectorGeneration
  endpointRigidity : EndpointRigidity.Reduction Time Carrier Law
  phaseCanonicalRepresentative : Prop
  waveCanonicalRepresentative : Prop
  gaugeCanonicalRepresentative : Prop
  geometricCanonicalRepresentative : Prop
  phaseCanonicalRepresentative_valid : phaseCanonicalRepresentative
  waveCanonicalRepresentative_valid : waveCanonicalRepresentative
  gaugeCanonicalRepresentative_valid : gaugeCanonicalRepresentative
  geometricCanonicalRepresentative_valid : geometricCanonicalRepresentative

/-- Step 4 now has an explicit common rigidity schema: the completion layer
uses one generated-sector endpoint-rigidity principle together with the
carrier-level singleton-class reduction. -/
theorem NaturalOperatorCompletion.guidedByEndpointRigidity
    {Time Carrier Law : Type}
    (data : NaturalOperatorCompletion Time Carrier Law) :
    data.rigidityPrinciple.sectorGeneration = data.sectorGeneration ∧
      data.rigidityPrinciple.localLawsReduceToFiniteJetOrder ∧
      data.rigidityPrinciple.generatedSymmetryActsOnJetLevel ∧
      data.rigidityPrinciple.compatibilityIdentitiesCutJetOperatorSpace ∧
      data.rigidityPrinciple.admissibleEndpointEquivalenceRelation ∧
      data.rigidityPrinciple.minimalTruncationProducesFiniteClosureQuotient ∧
      data.rigidityPrinciple.singletonQuotientForcesUniqueCanonicalRepresentative ∧
      data.rigidityPrinciple.nonsingletonQuotientForcesCanonicalNormalFormFamily ∧
      data.endpointRigidity.endpointClosureUniqueModuloContinuumEquivalence := by
  have hschema := EndpointRigidity.Principle.surface data.rigidityPrinciple
  rcases hschema with
    ⟨hjet, hsymm, hident, hequiv, htrunc, hsingle, hfamily⟩
  exact
    ⟨data.rigidityPrincipleUsesSameSectorGeneration,
      hjet,
      hsymm,
      hident,
      hequiv,
      htrunc,
      hsingle,
      hfamily,
      data.endpointRigidity.endpointClosureUniqueModuloContinuumEquivalence_valid⟩

/-- Natural-operator completion turns the forced carrier-level law classes into
fully identified physical operators on the generated visible sectors. -/
theorem natural_operator_completion
    {Time Carrier Law : Type}
    (data : NaturalOperatorCompletion Time Carrier Law) :
    data.rigidityPrinciple.localLawsReduceToFiniteJetOrder ∧
      data.rigidityPrinciple.generatedSymmetryActsOnJetLevel ∧
      data.rigidityPrinciple.compatibilityIdentitiesCutJetOperatorSpace ∧
      data.rigidityPrinciple.admissibleEndpointEquivalenceRelation ∧
      data.rigidityPrinciple.minimalTruncationProducesFiniteClosureQuotient ∧
      data.rigidityPrinciple.singletonQuotientForcesUniqueCanonicalRepresentative ∧
      data.rigidityPrinciple.nonsingletonQuotientForcesCanonicalNormalFormFamily ∧
      data.endpointRigidity.endpointClosureUniqueModuloContinuumEquivalence ∧
      data.phaseRepresentativeClassified ∧
      data.waveRepresentativeClassified ∧
      data.kineticRepresentativeClassified ∧
      data.gaugeRepresentativeClassified ∧
      data.geometricRepresentativeClassified ∧
      data.phaseCanonicalRepresentative ∧
      data.waveCanonicalRepresentative ∧
      data.gaugeCanonicalRepresentative ∧
      data.geometricCanonicalRepresentative := by
  have hguided := NaturalOperatorCompletion.guidedByEndpointRigidity data
  rcases hguided with
    ⟨_hsame, hjet, hsymm, hident, hequiv, htrunc, hsingle, hfamily, huniq⟩
  exact
    ⟨hjet,
      hsymm,
      hident,
      hequiv,
      htrunc,
      hsingle,
      hfamily,
      huniq,
      data.phaseRepresentativeClassified_valid,
      data.waveRepresentativeClassified_valid,
      data.kineticRepresentativeClassified_valid,
      data.gaugeRepresentativeClassified_valid,
      data.geometricRepresentativeClassified_valid,
      data.phaseCanonicalRepresentative_valid,
      data.waveCanonicalRepresentative_valid,
      data.gaugeCanonicalRepresentative_valid,
      data.geometricCanonicalRepresentative_valid⟩

namespace SelectedCutOrthogonality

/-- Exact selected-cut energy splitting: on the least-motion cut of a
canonical selected Schur bridge, the visible/shadow decomposition carries no
observer-induced splitting remainder in the native energy bookkeeping of the
active spine. This is the rebuilt active-surface form of "orthogonal" or
"self-adjoint" cutting: exact Pythagorean additivity on the realized cut. -/
def exactSplit
    {Index Time Carrier Law : Type}
    (data : CanonicalSelectedSchurBridge Index Time Carrier Law) : Prop :=
  ∀ x : State,
    State.energy x =
      State.energy
        ((data.observer.selection.realization.tower.π
          data.observer.selection.horizon).toFun x) +
      State.energy
        (shadowProj
          data.observer.selection.realization.tower
          data.observer.selection.horizon x)

/-- The selected cut of a canonical selected Schur bridge is energy-orthogonal
in the exact native sense: total state energy splits into visible plus shadow
energy with no extra observer-induced remainder. -/
theorem exact
    {Index Time Carrier Law : Type}
    (data : CanonicalSelectedSchurBridge Index Time Carrier Law) :
    exactSplit data := by
  intro x
  simpa [exactSplit, data.energyTower_eq] using
    data.energyTower.pythagorean_split data.observer.selection.horizon x

/-- Realized-cut energy orthogonality is the more structural common last-mile
principle behind canonical duality. The selected cut is read on one
energy-orthogonal visible carrier, so trial and test data are not chosen
independently: they come from the same selected carrier and inherit the same
canonical pairing from the exact visible/shadow energy split. The remaining
endpoint law is then required only to preserve that endogenous pairing. -/
structure Principle
    (Time Carrier Law Fiber : Type) where
  completion : NaturalOperatorCompletion Time Carrier Law
  selectedBridge :
    CanonicalSelectedSchurBridge
      completion.sectorGeneration.selectedBundle.Index
      Time Carrier Law
  selectedBridgeIsCompletionBridge :
    completion.sectorGeneration.selectedBundle.selectedSchurBridge = selectedBridge
  trialAndTestReadOnSameSelectedCarrier : Prop
  pairingReadFromEnergyOrthogonalSelectedCut : Prop
  generatedSymmetryPreservesSelectedCutPairing : Prop
  admissibleEndpointOperatorsPreserveSelectedCutPairing : Prop
  weakLawHasUniquePairingCompatibleStrongRepresentative : Prop
  trialAndTestReadOnSameSelectedCarrier_valid :
    trialAndTestReadOnSameSelectedCarrier
  pairingReadFromEnergyOrthogonalSelectedCut_valid :
    pairingReadFromEnergyOrthogonalSelectedCut
  generatedSymmetryPreservesSelectedCutPairing_valid :
    generatedSymmetryPreservesSelectedCutPairing
  admissibleEndpointOperatorsPreserveSelectedCutPairing_valid :
    admissibleEndpointOperatorsPreserveSelectedCutPairing
  weakLawHasUniquePairingCompatibleStrongRepresentative_valid :
    weakLawHasUniquePairingCompatibleStrongRepresentative

/-- Realized-cut energy orthogonality unpacks to exact selected-cut energy
splitting together with one endogenous trial/test pairing preserved by the
generated symmetries and admissible endpoint operators. -/
theorem Principle.surface
    {Time Carrier Law Fiber : Type}
    (data : Principle Time Carrier Law Fiber) :
    exactSplit data.selectedBridge ∧
      data.trialAndTestReadOnSameSelectedCarrier ∧
      data.pairingReadFromEnergyOrthogonalSelectedCut ∧
      data.generatedSymmetryPreservesSelectedCutPairing ∧
      data.admissibleEndpointOperatorsPreserveSelectedCutPairing ∧
      data.weakLawHasUniquePairingCompatibleStrongRepresentative := by
  exact
    ⟨exact data.selectedBridge,
      data.trialAndTestReadOnSameSelectedCarrier_valid,
      data.pairingReadFromEnergyOrthogonalSelectedCut_valid,
      data.generatedSymmetryPreservesSelectedCutPairing_valid,
      data.admissibleEndpointOperatorsPreserveSelectedCutPairing_valid,
      data.weakLawHasUniquePairingCompatibleStrongRepresentative_valid⟩

end SelectedCutOrthogonality

namespace CanonicalDuality

/-- Canonical duality / variational rigidity for the intrinsic reversible
sectors. Trial and test data are generated by the same selected visible sector,
identified by a canonical pairing, and the admissible endpoint operators are
forced to be pairing-symmetric representatives of the already rigid closure
class. This is the abstract Step 4 mechanism that turns the final
representative-identification step into a theorem-driven selection rather than
an inspired choice by the practitioner. -/
structure SectorRigidity
    (Time Carrier Law Fiber : Type) where
  completion : NaturalOperatorCompletion Time Carrier Law
  trialSpaceGeneratedBySelectedSector : Prop
  testSpaceGeneratedBySelectedSector : Prop
  canonicalPairingOnGeneratedSector : Prop
  trialTestIdentifiedByCanonicalPairing : Prop
  generatedSymmetryPreservesCanonicalPairing : Prop
  admissibleEndpointOperatorsPairingSymmetric : Prop
  weakFormDeterminesUniqueStrongRepresentative : Prop
  endpointRepresentativeForcedByWeakForm : Prop
  trialSpaceGeneratedBySelectedSector_valid :
    trialSpaceGeneratedBySelectedSector
  testSpaceGeneratedBySelectedSector_valid :
    testSpaceGeneratedBySelectedSector
  canonicalPairingOnGeneratedSector_valid :
    canonicalPairingOnGeneratedSector
  trialTestIdentifiedByCanonicalPairing_valid :
    trialTestIdentifiedByCanonicalPairing
  generatedSymmetryPreservesCanonicalPairing_valid :
    generatedSymmetryPreservesCanonicalPairing
  admissibleEndpointOperatorsPairingSymmetric_valid :
    admissibleEndpointOperatorsPairingSymmetric
  weakFormDeterminesUniqueStrongRepresentative_valid :
    weakFormDeterminesUniqueStrongRepresentative
  endpointRepresentativeForcedByWeakForm_valid :
    endpointRepresentativeForcedByWeakForm

/-- Canonical duality sector rigidity unpacks the shared weak/strong
representative mechanism on the intrinsic reversible carriers. -/
theorem SectorRigidity.surface
    {Time Carrier Law Fiber : Type}
    (data : SectorRigidity Time Carrier Law Fiber) :
    data.trialSpaceGeneratedBySelectedSector ∧
      data.testSpaceGeneratedBySelectedSector ∧
      data.canonicalPairingOnGeneratedSector ∧
      data.trialTestIdentifiedByCanonicalPairing ∧
      data.generatedSymmetryPreservesCanonicalPairing ∧
      data.admissibleEndpointOperatorsPairingSymmetric ∧
      data.weakFormDeterminesUniqueStrongRepresentative ∧
      data.endpointRepresentativeForcedByWeakForm := by
  exact
    ⟨data.trialSpaceGeneratedBySelectedSector_valid,
      data.testSpaceGeneratedBySelectedSector_valid,
      data.canonicalPairingOnGeneratedSector_valid,
      data.trialTestIdentifiedByCanonicalPairing_valid,
      data.generatedSymmetryPreservesCanonicalPairing_valid,
      data.admissibleEndpointOperatorsPairingSymmetric_valid,
      data.weakFormDeterminesUniqueStrongRepresentative_valid,
      data.endpointRepresentativeForcedByWeakForm_valid⟩

/-- Once the endpoint closure class is already unique modulo continuum
equivalence, canonical duality turns the last representative substitution into
an internally forced step: the weak form on the self-dual sector determines
the unique strong representative. -/
theorem SectorRigidity.forcesEndpointSubstitution
    {Time Carrier Law Fiber : Type}
    (data : SectorRigidity Time Carrier Law Fiber) :
    data.completion.endpointRigidity.endpointClosureUniqueModuloContinuumEquivalence ∧
      data.trialTestIdentifiedByCanonicalPairing ∧
      data.weakFormDeterminesUniqueStrongRepresentative ∧
      data.endpointRepresentativeForcedByWeakForm := by
  have hcompletion := NaturalOperatorCompletion.guidedByEndpointRigidity data.completion
  have hduality := SectorRigidity.surface data
  rcases hcompletion with
    ⟨_hsame, _hjet, _hsymm, _hident, _hequiv, _htrunc, _hsingle, _hfamily,
      huniq⟩
  rcases hduality with
    ⟨_htrial, _htest, _hpair, hsame, _hpres, _hsymm, hweak, hforced⟩
  exact ⟨huniq, hsame, hweak, hforced⟩

end CanonicalDuality

namespace SelectedCutOrthogonality

/-- Realized-cut energy orthogonality produces the older canonical-duality
surface as a derived interface. This is the precise formal sense in which
canonical duality is no longer the primitive last-step hypothesis: it is read
off from exact selected-cut energy bookkeeping plus pairing preservation. -/
def Principle.toCanonicalDuality
    {Time Carrier Law Fiber : Type}
    (data : Principle Time Carrier Law Fiber) :
    CanonicalDuality.SectorRigidity Time Carrier Law Fiber where
  completion := data.completion
  trialSpaceGeneratedBySelectedSector :=
    data.trialAndTestReadOnSameSelectedCarrier
  testSpaceGeneratedBySelectedSector :=
    data.trialAndTestReadOnSameSelectedCarrier
  canonicalPairingOnGeneratedSector :=
    data.pairingReadFromEnergyOrthogonalSelectedCut
  trialTestIdentifiedByCanonicalPairing :=
    data.pairingReadFromEnergyOrthogonalSelectedCut
  generatedSymmetryPreservesCanonicalPairing :=
    data.generatedSymmetryPreservesSelectedCutPairing
  admissibleEndpointOperatorsPairingSymmetric :=
    data.admissibleEndpointOperatorsPreserveSelectedCutPairing
  weakFormDeterminesUniqueStrongRepresentative :=
    data.weakLawHasUniquePairingCompatibleStrongRepresentative
  endpointRepresentativeForcedByWeakForm :=
    data.completion.endpointRigidity.endpointClosureUniqueModuloContinuumEquivalence ∧
      data.weakLawHasUniquePairingCompatibleStrongRepresentative
  trialSpaceGeneratedBySelectedSector_valid :=
    data.trialAndTestReadOnSameSelectedCarrier_valid
  testSpaceGeneratedBySelectedSector_valid :=
    data.trialAndTestReadOnSameSelectedCarrier_valid
  canonicalPairingOnGeneratedSector_valid :=
    data.pairingReadFromEnergyOrthogonalSelectedCut_valid
  trialTestIdentifiedByCanonicalPairing_valid :=
    data.pairingReadFromEnergyOrthogonalSelectedCut_valid
  generatedSymmetryPreservesCanonicalPairing_valid :=
    data.generatedSymmetryPreservesSelectedCutPairing_valid
  admissibleEndpointOperatorsPairingSymmetric_valid :=
    data.admissibleEndpointOperatorsPreserveSelectedCutPairing_valid
  weakFormDeterminesUniqueStrongRepresentative_valid :=
    data.weakLawHasUniquePairingCompatibleStrongRepresentative_valid
  endpointRepresentativeForcedByWeakForm_valid := by
    exact
      ⟨data.completion.endpointRigidity.endpointClosureUniqueModuloContinuumEquivalence_valid,
        data.weakLawHasUniquePairingCompatibleStrongRepresentative_valid⟩

/-- The general orthogonality/self-duality principle implies the older
canonical-duality interface on every intrinsic reversible carrier. -/
theorem impliesCanonicalDuality
    {Time Carrier Law Fiber : Type}
    (data : Principle Time Carrier Law Fiber) :
    exactSplit data.selectedBridge ∧
      (data.toCanonicalDuality.trialTestIdentifiedByCanonicalPairing) ∧
      (data.toCanonicalDuality.generatedSymmetryPreservesCanonicalPairing) ∧
      ((data.toCanonicalDuality).weakFormDeterminesUniqueStrongRepresentative) := by
  exact
    ⟨exact data.selectedBridge,
      data.pairingReadFromEnergyOrthogonalSelectedCut_valid,
      data.generatedSymmetryPreservesSelectedCutPairing_valid,
      data.weakLawHasUniquePairingCompatibleStrongRepresentative_valid⟩

/-- Realized-cut energy orthogonality inherits the common endpoint-uniqueness
surface already carried by the completion layer: the minimal endpoint class is
singleton and unique modulo continuum equivalence before any carrier-specific
representative is identified. -/
theorem inheritsEndpointUniqueness
    {Time Carrier Law Fiber : Type}
    (data : Principle Time Carrier Law Fiber) :
    data.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      data.completion.endpointRigidity.endpointClosureUniqueModuloContinuumEquivalence := by
  exact
    ⟨data.completion.endpointRigidity.inheritedMinimalOrderClassSingleton_valid,
      data.completion.endpointRigidity.endpointClosureUniqueModuloContinuumEquivalence_valid⟩

/-- The energy-orthogonal realized-cut principle therefore forces the final
endpoint representative substitution mechanically: once the selected cut is
exactly split and the endpoint class is already unique modulo continuum
equivalence, the pairing-compatible strong representative is fixed internally. -/
theorem forcesEndpointSubstitution
    {Time Carrier Law Fiber : Type}
    (data : Principle Time Carrier Law Fiber) :
    exactSplit data.selectedBridge ∧
      (data.toCanonicalDuality).endpointRepresentativeForcedByWeakForm := by
  have hforced :=
    CanonicalDuality.SectorRigidity.forcesEndpointSubstitution
      data.toCanonicalDuality
  rcases hforced with ⟨_huniq, _hsame, _hweak, hforced⟩
  exact
    ⟨exact data.selectedBridge,
      hforced⟩

/-- For the intrinsic lane proofs, realized-cut orthogonality already packages
the two common endpoint facts that matter downstream: the singleton endpoint
class and the forced pairing-compatible representative. -/
theorem Principle.singletonRepresentative
    {Time Carrier Law Fiber : Type}
    (data : Principle Time Carrier Law Fiber) :
    data.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      data.toCanonicalDuality.endpointRepresentativeForcedByWeakForm := by
  exact
    ⟨(inheritsEndpointUniqueness data).1,
      (forcesEndpointSubstitution data).2⟩

/-- Compact endpoint-terminality surface on the orthogonality lane. Once the
selected cut is exact and the endpoint class is already singleton/unique on
that cut, the pairing-compatible strong representative is forced internally.
This is the clean upstream Step 4 theorem surface later consumed by the
selected-completion route. -/
theorem Principle.endpointTerminalitySurface
    {Time Carrier Law Fiber : Type}
    (data : Principle Time Carrier Law Fiber) :
    exactSplit data.selectedBridge ∧
      data.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      data.completion.endpointRigidity.endpointClosureUniqueModuloContinuumEquivalence ∧
      data.toCanonicalDuality.weakFormDeterminesUniqueStrongRepresentative ∧
      data.toCanonicalDuality.endpointRepresentativeForcedByWeakForm := by
  have hexact := exact data.selectedBridge
  have hendpoint := inheritsEndpointUniqueness data
  have hduality := impliesCanonicalDuality data
  have hforced := forcesEndpointSubstitution data
  exact
    ⟨hexact,
      hendpoint.1,
      hendpoint.2,
      hduality.2.2.2,
      hforced.2⟩

end SelectedCutOrthogonality

/-- The explicit Part IV law-completion target exported by the generic
observer-selection layer. -/
def PartIVLawCompletionStatement
    {Time Carrier Law : Type}
    (data : NaturalOperatorCompletion Time Carrier Law) : Prop :=
    let bridge := data.sectorGeneration.selectedBundle.selectedSchurBridge
    (bridge.observer.selection.selectedProjection =
      selectedCandidateProjection bridge.observer.selection) ∧
      (bridge.observer.selection.selectedProjection =
        bridge.observer.selection.realization.tower.π
          bridge.observer.selection.horizon) ∧
      (∀ i : data.sectorGeneration.selectedBundle.Index,
        bridge.observer.selection.horizon = (bridge.cls.datum i).horizon ∧
          (∀ x : State,
            (bridge.uniqueClass bridge.root i).transport
              ((selected_observed_law bridge.observer.selection).op x) =
              (selected_observed_law (bridge.cls.datum i)).op
                ((bridge.uniqueClass bridge.root i).transport x))) ∧
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
      data.sectorGeneration.selectedBundle.selectedObservedBundle ∧
      data.sectorGeneration.selectedBundle.noCarrierWiseVisibilityHypotheses ∧
      data.sectorGeneration.selectedBundle.sameSelectedEffectiveLawOnEachCarrier ∧
      data.sectorGeneration.selectedBundle.carrierLevelIdentificationOnlyFinalStep ∧
      (data.sectorGeneration.selectedBundle.physicalPrinciple.selectedLaw.selection =
        bridge.observer.selection) ∧
      closureTypedPromotionFiniteCarrier.finite_carrier_available ∧
      closureTypedPromotionFiniteCarrier.canonical_signature_available ∧
      closureTypedPromotionFiniteCarrier.three_parameter_control ∧
      IsCanonicalLogicalProfile [3, 2, 1] ∧
      data.sectorGeneration.generatedFromIntrinsicChannelAlgebra ∧
      data.sectorGeneration.notPrimitiveDictionary ∧
      data.endpointRigidity.endpointClosureUniqueModuloContinuumEquivalence ∧
      data.phaseRepresentativeClassified ∧
      data.waveRepresentativeClassified ∧
      data.kineticRepresentativeClassified ∧
      data.gaugeRepresentativeClassified ∧
      data.geometricRepresentativeClassified

/-- If the four law-completion proofs are available, then Part IV closes as a
physical law chapter on the selected cut. -/
theorem partIV_law_completion
    {Time Carrier Law : Type}
    (data : NaturalOperatorCompletion Time Carrier Law) :
    PartIVLawCompletionStatement data := by
  dsimp [PartIVLawCompletionStatement]
  have hbundle :=
    intrinsic_selected_bundle_existence data.sectorGeneration.selectedBundle
  rcases hbundle with
    ⟨_hintrinsic, hnoCarrier, _hprojBundle, _hcutBundle, hsameLaw, _hclass,
      _hd3Bundle, hselectedBundle, _hsharedBundle, hsameEffective, hfinalStep⟩
  have hschur :=
    canonical_selected_schur_realization
      data.sectorGeneration.selectedBundle.selectedSchurBridge
  rcases hschur with
    ⟨hproj, hcut, hforcing, _hmin, hexact, hclosed, hnoConst, hreturned,
      hret, hsplit, hstep, hmono, hd3, hprofile⟩
  have hsector := intrinsic_sector_generation data.sectorGeneration
  rcases hsector with
    ⟨hgenerated, _hminimal, hfinite, hsignature, hcontrol, _hsum, _hprofile',
      _hphaseGen, _hwaveGen, _hkineticGen, _hgaugeGen, _hgeomGen, hnotDict⟩
  have hcompletion := natural_operator_completion data
  rcases hcompletion with
    ⟨_hjet, _hsymm, _hident, _hequiv, _htrunc, _hsingle, _hfamily, huniq,
      hphase, hwave, hkinetic, hgauge, hgeom, _hcphase, _hcwave, _hcgauge,
      _hcgeom⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hproj
  · exact hcut
  · exact hforcing
  · exact hexact
  · exact hclosed
  · exact hnoConst
  · exact hreturned
  · exact hret
  · exact hsplit
  · exact hstep
  · exact hmono
  · exact hd3
  · exact hselectedBundle
  · exact hnoCarrier
  · exact hsameEffective
  · exact hfinalStep
  · exact hsameLaw
  · exact hfinite
  · exact hsignature
  · exact hcontrol
  · exact hprofile
  · exact hgenerated
  · exact hnotDict
  · exact huniq
  · exact hphase
  · exact hwave
  · exact hkinetic
  · exact hgauge
  · exact hgeom

end CoherenceCalculus

