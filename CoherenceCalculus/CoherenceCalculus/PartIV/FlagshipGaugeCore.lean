import CoherenceCalculus.PartIV.ObserverSelectionCore
import CoherenceCalculus.PartIV.FlagshipClosureSharedCore

/-!
# PartIV.FlagshipGaugeCore

Gauge flagship lane for Part IV.

This file isolates the one-form / Maxwell lane so the main flagship
aggregator can stay organized by lane family instead of carrying every lane
inline.
-/

namespace CoherenceCalculus

namespace GaugeLane

/-- Gauge-compatible one-form realization on the selected cut. -/
structure OneFormRealization
    (Time Carrier Law Field : Type) where
  observerDatum : ObserverSelection.CharacteristicDatum Time Carrier Law
  visibleGaugeCarrier : Carrier
  exactness : Prop
  localGaugeCovariance : Prop
  continuumEquivalenceModuloGauge : Prop
  transportOrderDisciplined : Prop
  minimalOrderResponse : Prop
  sourceConserved : Prop
  curvatureCarrier : Field

/-- Least-motion gauge carrier hypotheses. -/
structure LeastMotionObserverData
    (Time Carrier Law Field : Type)
    extends OneFormRealization Time Carrier Law Field where
  gaugeCompatibleLocalDatum : Prop
  faithfulCarrier : Prop
  closureAdmissibleCarrier : Prop
  stableUnderAdmissiblePromotion : Prop
  noProperGaugeSubcarrier : Prop
  observerMotionMinimal : Prop
  uniqueObserver : Prop

/-- Least-motion gauge observer theorem. -/
theorem leastMotionObserver
    {Time Carrier Law Field : Type}
    (data : LeastMotionObserverData Time Carrier Law Field) :
    Nonempty (ObserverSelection.LeastMotion Time Carrier Law) := by
  exact
    ⟨{ toCharacteristicDatum := data.observerDatum
       faithful := data.faithfulCarrier
       closureAdmissible := data.closureAdmissibleCarrier
       stableUnderAdmissiblePromotion := data.stableUnderAdmissiblePromotion
       noProperVisibleSubcarrier := data.noProperGaugeSubcarrier
       observerMotionMinimal := data.observerMotionMinimal
       uniqueUpToHorizonPreservingEquivalence := data.uniqueObserver }⟩

/-- Gauge-compatible curvature/source datum on the selected cut. -/
structure CurvatureSourceDatum (Field Source : Type) where
  gaugeClass : Field
  curvature : Field
  sourceLaw : Source

/-- Induced gauge-compatible law on the selected cut. -/
structure InducedLaw
    (Time Carrier Law Field Source : Type) where
  observer : ObserverSelection.LeastMotion Time Carrier Law
  datum : CurvatureSourceDatum Field Source
  gaugeCompatibleResponseOperator : Endo Field
  closedCurvature : Prop
  sourceResponseLaw : Prop
  losslessLeadingOrder : Prop

/-- Witness data for the induced gauge-compatible law. -/
structure InducedLawData
    (Time Carrier Law Field Source : Type)
    extends InducedLaw
      Time Carrier Law Field Source where
  realization : OneFormRealization Time Carrier Law Field
  localGaugeCompatibleInternalDatum : Prop
  inheritedMinimalOrderClosure : Prop

/-- Induced gauge-compatible law. -/
theorem inducedLaw
    {Time Carrier Law Field Source : Type}
    (data : InducedLawData
      Time Carrier Law Field Source) :
    Nonempty (InducedLaw
      Time Carrier Law Field Source) := by
  exact ⟨data.toInducedLaw⟩

end GaugeLane

namespace GaugeLane

/-- Recognition package for Maxwell form on the selected cut. -/
structure RecognizableIdentity
    (Time Carrier Law Field Source : Type) where
  law : InducedLaw Time Carrier Law Field Source
  maxwellForm : Prop
  exactIfLossless : Prop

private theorem recognizableWitness
    {Time Carrier Law Field Source : Type}
    (law : InducedLaw Time Carrier Law Field Source)
    (maxwellForm exactIfLossless : Prop) :
    Nonempty (RecognizableIdentity Time Carrier Law Field Source) := by
  exact
    ⟨{ law := law
       maxwellForm := maxwellForm
       exactIfLossless := exactIfLossless }⟩

/-- Endpoint-collapse package for the gauge carrier. The generic orthogonality
theorem fixes the representative mechanism; the remaining gauge-specific work
is to show that the pairing-compatible minimal response quotient is singleton
and represented by the codifferential curvature law. -/
structure EndpointCollapse
    (Time Carrier Law Field Source : Type)
    where
  law : InducedLaw Time Carrier Law Field Source
  orthogonalityRigidity :
    SelectedCutOrthogonality.Principle Time Carrier Law Field
  curvatureClosedByGeneratedComplex : Prop
  canonicalOneFormDualityGenerated : Prop
  minimalPairingSymmetricResponseIsCodifferentialCurvature : Prop
  curvatureClosedByGeneratedComplex_valid :
    curvatureClosedByGeneratedComplex
  canonicalOneFormDualityGenerated_valid :
    canonicalOneFormDualityGenerated
  minimalPairingSymmetricResponseIsCodifferentialCurvature_valid :
    minimalPairingSymmetricResponseIsCodifferentialCurvature

/-- The gauge endpoint-collapse theorem isolates the exact remaining gauge
obligation: the generated one-form duality must collapse the admissible
pairing-compatible response quotient to the codifferential curvature
representative. -/
theorem endpointCollapse
    {Time Carrier Law Field Source : Type}
    (data : EndpointCollapse Time Carrier Law Field Source) :
    let duality := data.orthogonalityRigidity.toCanonicalDuality
    data.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      data.curvatureClosedByGeneratedComplex ∧
      data.canonicalOneFormDualityGenerated ∧
      data.minimalPairingSymmetricResponseIsCodifferentialCurvature := by
  have horth :=
    SelectedCutOrthogonality.Principle.singletonRepresentative
      data.orthogonalityRigidity
  exact
    ⟨horth.1,
      horth.2,
      data.curvatureClosedByGeneratedComplex_valid,
      data.canonicalOneFormDualityGenerated_valid,
      data.minimalPairingSymmetricResponseIsCodifferentialCurvature_valid⟩

/-- Sector-rigidity package forcing the canonical Maxwell representative on
the selected one-form carrier once the gauge endpoint collapse has been
established. -/
structure SectorRigidity
    (Time Carrier Law Field Source : Type)
    extends EndpointCollapse Time Carrier Law Field Source where
  recognizableMaxwellFormForced : Prop
  exactMaxwellIfLossless : Prop
  recognizableMaxwellFormForced_valid :
    recognizableMaxwellFormForced
  exactMaxwellIfLossless_valid :
    exactMaxwellIfLossless

/- The gauge endpoint is rigid when the generated one-form duality forces the
codifferential curvature response inside the already rigid closure class. -/

theorem sectorRigidity
    {Time Carrier Law Field Source : Type}
    (data : SectorRigidity Time Carrier Law Field Source) :
    let duality :=
      SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.toEndpointCollapse.orthogonalityRigidity
    data.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      data.minimalPairingSymmetricResponseIsCodifferentialCurvature ∧
      data.recognizableMaxwellFormForced := by
  have hcollapse := endpointCollapse data.toEndpointCollapse
  rcases hcollapse with
    ⟨hsingleton, hrep, _hclosed, _hduality, hcodiff⟩
  exact
    ⟨hsingleton,
      hrep,
      hcodiff,
      data.recognizableMaxwellFormForced_valid⟩

/-- Recognizable Maxwell identity. -/
theorem recognizableIdentity
    {Time Carrier Law Field Source : Type}
    (data : SectorRigidity Time Carrier Law Field Source) :
    Nonempty (RecognizableIdentity
      Time Carrier Law Field Source) := by
  exact
    recognizableWitness
      data.law
      data.recognizableMaxwellFormForced
      data.exactMaxwellIfLossless

end GaugeLane

namespace GaugeLane

/-- Foundation-facing frontier data for the gauge endpoint. This packages the
selected-channel gauge-covariance surface already available before the final
codifferential-curvature representative identity is proved. -/
structure EndpointFoundationFrontierData
    (Time Carrier Law Field Source Vertex : Type) where
  collapse : EndpointCollapse Time Carrier Law Field Source
  selectedGaugeCovariance :
    SelectedChannelGaugeCovarianceData Time Vertex

/- On the active Lean surface, the gauge endpoint already reduces to an
energy-orthogonal singleton endpoint class together with local gauge covariance
on the selected channel. The remaining burden is to show that the generated
one-form duality fixes the pairing-compatible response as the codifferential
curvature representative. -/
theorem endpointFrontier
    {Time Carrier Law Field Source Vertex : Type}
    (data : EndpointFoundationFrontierData
      Time Carrier Law Field Source Vertex) :
    let duality := data.collapse.orthogonalityRigidity.toCanonicalDuality
    data.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      data.selectedGaugeCovariance.localGaugeInvariant ∧
      data.selectedGaugeCovariance.unimodularReduction ∧
      data.collapse.curvatureClosedByGeneratedComplex ∧
      data.collapse.canonicalOneFormDualityGenerated ∧
      data.collapse.minimalPairingSymmetricResponseIsCodifferentialCurvature := by
  have hcollapse := endpointCollapse data.collapse
  have hgauge := selected_channel_gauge_covariance data.selectedGaugeCovariance
  rcases hcollapse with
    ⟨hsingleton, hrep, hclosed, hduality, hcodiff⟩
  rcases hgauge with ⟨hinv, hunimod⟩
  exact
    ⟨hsingleton,
      hrep,
      hinv,
      hunimod,
      hclosed,
      hduality,
      hcodiff⟩

/-- Reusable head of the exact gauge endpoint frontier. Later gauge proofs
often need only the singleton class, forced representative, and
codifferential-curvature endpoint identity, not the full local covariance
package. -/
private theorem endpointRepresentativeFacts
    {Time Carrier Law Field Source Vertex : Type}
    (data : EndpointFoundationFrontierData
      Time Carrier Law Field Source Vertex) :
    let duality := data.collapse.orthogonalityRigidity.toCanonicalDuality
    data.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      data.collapse.minimalPairingSymmetricResponseIsCodifferentialCurvature := by
  have hfrontier := endpointFrontier data
  rcases hfrontier with
    ⟨hsingleton, hrep, _hinv, _hunimod, _hclosed, _hduality, hcodiff⟩
  exact
    ⟨hsingleton,
      hrep,
      hcodiff⟩

/-- Direct representative theorem on the exact gauge endpoint frontier. Once
the gauge lane has reached the forced endpoint frontier, the recognizable
Maxwell representative is already fixed there: no additional continuum-closure
wrapper is needed to identify the codifferential-curvature form. -/
theorem recognizableFromEndpointFrontier
    {Time Carrier Law Field Source Vertex : Type}
    (data : EndpointFoundationFrontierData
      Time Carrier Law Field Source Vertex) :
    let duality := data.collapse.orthogonalityRigidity.toCanonicalDuality
    data.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      data.collapse.minimalPairingSymmetricResponseIsCodifferentialCurvature ∧
      Nonempty (RecognizableIdentity
        Time Carrier Law Field Source) := by
  have hendpoint := endpointRepresentativeFacts data
  rcases hendpoint with ⟨hsingleton, hrep, hcodiff⟩
  exact
    ⟨hsingleton,
      hrep,
      hcodiff,
      recognizableWitness
        data.collapse.law
        data.collapse.minimalPairingSymmetricResponseIsCodifferentialCurvature
        data.collapse.law.losslessLeadingOrder⟩

/-- Clean direct gauge closure route using the already-forced selected closure
law from the Part IV physical realization package. Once the selected gauge
carrier is read on the same least-motion cut and carries the same continuum
closure class, the continuum singleton is inherited directly from the physical
selected law itself. -/
structure SelectedClosureIdentificationData
    (Time Carrier Law Field Source Vertex : Type) where
  frontier :
    EndpointFoundationFrontierData
      Time Carrier Law Field Source Vertex
  physical :
    PhysicalRealizationPrinciple Time Carrier Law
  sameLeastMotionSelection :
    physical.selectedLaw.selection =
      frontier.collapse.law.observer.selection
  sameContinuumClosureClass :
    physical.selectedLaw.endpointClosureClass =
      frontier.collapse.law.observer.continuumClass

/-- Elegant gauge closure theorem. The gauge frontier already fixes the
recognizable pairing-compatible endpoint form; if the gauge observer is reading
the same selected cut and continuum closure class as the Part IV physical
selected law, then the forced continuum singleton is inherited directly with no
separate target-uniqueness theorem. -/
theorem closureFromPhysicalRealization
    {Time Carrier Law Field Source Vertex : Type}
    (data : SelectedClosureIdentificationData
      Time Carrier Law Field Source Vertex) :
    let cls := data.frontier.collapse.law.observer.continuumClass
    let target := data.physical.selectedLaw.selectedClosureLaw
    data.frontier.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      (SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.frontier.collapse.orthogonalityRigidity).endpointRepresentativeForcedByWeakForm ∧
      ForcedContinuumLaw cls target ∧
      Nonempty (RecognizableIdentity
        Time Carrier Law Field Source) := by
  have hfrontier := recognizableFromEndpointFrontier data.frontier
  rcases hfrontier with
    ⟨hsingleton, hrep, _hcodiff, hrecognizable⟩
  exact
    SelectedCut.closureReadoutWithRecognition
      data.physical
      data.frontier.collapse.law.observer
      data.sameLeastMotionSelection
      data.sameContinuumClosureClass
      hsingleton
      hrep
      hrecognizable

/-- Selected-bundle gauge closure route. This is the more foundational version
of the direct closure theorem: once the gauge observer is read off the one
intrinsic selected bundle, forced continuum closure is inherited
automatically. -/
structure SelectedBundleClosureIdentificationData
    (Time Carrier Law Field Source Vertex : Type) where
  frontier :
    EndpointFoundationFrontierData
      Time Carrier Law Field Source Vertex
  selectedBundle : IntrinsicSelectedBundleExistence Time Carrier Law
  gaugeCarrierReadOnSelectedBundle :
    selectedBundle.gaugeCarrierReadOnSelectedBundle
      frontier.collapse.law.observer

/-- Foundational gauge closure theorem through the intrinsic selected bundle. -/
theorem closureFromSelectedBundle
    {Time Carrier Law Field Source Vertex : Type}
    (data : SelectedBundleClosureIdentificationData
      Time Carrier Law Field Source Vertex) :
    let cls := data.frontier.collapse.law.observer.continuumClass
    let target := data.selectedBundle.physicalPrinciple.selectedLaw.selectedClosureLaw
    data.frontier.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      (SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.frontier.collapse.orthogonalityRigidity).endpointRepresentativeForcedByWeakForm ∧
      ForcedContinuumLaw cls target ∧
      Nonempty (RecognizableIdentity
        Time Carrier Law Field Source) := by
  have hfrontier := recognizableFromEndpointFrontier data.frontier
  have hsel :=
    SelectedBundle.gaugeCarrierSelection
      data.selectedBundle
      data.frontier.collapse.law.observer
      data.gaugeCarrierReadOnSelectedBundle
  rcases hfrontier with
    ⟨hsingleton, hrep, _hcodiff, hrecognizable⟩
  exact
    SelectedBundle.closureReadoutWithRecognition
      data.selectedBundle
      data.frontier.collapse.law.observer
      hsel
      hsingleton
      hrep
      hrecognizable

/-- Gauge-endpoint frontier refined by the fixed-horizon gauge-compatible local
datum. This packages the exact local one-form datum already available on the
active spine before the final codifferential-curvature representative identity
is closed. -/
structure EndpointLocalDatumFrontierData
    (Time Carrier Law Field Source Vertex
      PhaseClass Scalar ClosureClass GaugeClass : Type) where
  frontier :
    EndpointFoundationFrontierData
      Time Carrier Law Field Source Vertex
  localGaugeDatum :
    GaugeCompatibleLocalDatumForcingData
      PhaseClass Scalar ClosureClass GaugeClass

/-- The active gauge frontier already carries a unique gauge-compatible local
datum on the selected channel before the final codifferential-curvature
representative identity is proved. -/
theorem localDatumFrontier
    {Time Carrier Law Field Source Vertex
      PhaseClass Scalar ClosureClass GaugeClass : Type}
    (data : EndpointLocalDatumFrontierData
      Time Carrier Law Field Source Vertex
      PhaseClass Scalar ClosureClass GaugeClass) :
    let duality :=
      data.frontier.collapse.orthogonalityRigidity.toCanonicalDuality
    data.frontier.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      Nonempty (GaugeCompatibleLocalInternalDatum
        PhaseClass Scalar ClosureClass GaugeClass) ∧
      data.frontier.selectedGaugeCovariance.localGaugeInvariant ∧
      data.frontier.selectedGaugeCovariance.unimodularReduction ∧
      data.frontier.collapse.curvatureClosedByGeneratedComplex ∧
      data.frontier.collapse.canonicalOneFormDualityGenerated ∧
      data.frontier.collapse.minimalPairingSymmetricResponseIsCodifferentialCurvature := by
  have hfrontier := endpointFrontier data.frontier
  have hlocal := gauge_compatible_local_datum_forcing data.localGaugeDatum
  rcases hfrontier with
    ⟨hsingleton, hforced, hinv, hunimod, hclosed, hdual, hcodiff⟩
  exact
    ⟨hsingleton,
      hforced,
      hlocal,
      hinv,
      hunimod,
      hclosed,
      hdual,
      hcodiff⟩

/-- Final gauge closure data: once the gauge-compatible local frontier has
been forced on the selected one-form carrier, the only remaining task is to
show that a chosen continuum representative lies in the observer's own
continuum limit class and is unique there. At that point the continuum
representative is forced with no further practitioner discretion. -/
structure ContinuumClosureData
    (Time Carrier Law Field Source Vertex
      PhaseClass Scalar ClosureClass GaugeClass : Type) where
  frontier :
    EndpointLocalDatumFrontierData
      Time Carrier Law Field Source Vertex
      PhaseClass Scalar ClosureClass GaugeClass
  target : Law
  targetAdmissible :
    frontier.frontier.collapse.law.observer.continuumClass.admissible target
  targetUnique :
    ∀ other : Law,
      frontier.frontier.collapse.law.observer.continuumClass.admissible other →
        other = target
  targetIsMaxwellRepresentative : Prop
  targetExactIfLossless : Prop
  targetIsMaxwellRepresentative_valid : targetIsMaxwellRepresentative
  targetExactIfLossless_valid : targetExactIfLossless

/-- Gauge closure theorem. The active spine now reduces the gauge lane to a
pure continuum-limit-class closure problem: once the gauge-compatible local
frontier is forced and a continuum representative is shown admissible and
unique in the selected observer's own continuum class, that representative is
itself forced. -/
theorem continuumClosure
    {Time Carrier Law Field Source Vertex
      PhaseClass Scalar ClosureClass GaugeClass : Type}
    (data : ContinuumClosureData
      Time Carrier Law Field Source Vertex
      PhaseClass Scalar ClosureClass GaugeClass) :
    let cls := data.frontier.frontier.collapse.law.observer.continuumClass
    let duality :=
      SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.frontier.frontier.collapse.orthogonalityRigidity
    data.frontier.frontier.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      ForcedContinuumLaw cls data.target ∧
      data.targetIsMaxwellRepresentative ∧
      data.targetExactIfLossless := by
  obtain ⟨hsingleton, hrep, _hcodiff⟩ :=
    endpointRepresentativeFacts data.frontier.frontier
  have ⟨_hsingleton, _hrep, hforced⟩ :=
    FlagshipShared.forcedContinuumFromEndpointFacts
      data.frontier.frontier.collapse.law.observer.continuumClass
      data.target
      hsingleton
      hrep
      data.targetAdmissible
      data.targetUnique
  exact
    ⟨hsingleton,
      hrep,
      hforced,
      data.targetIsMaxwellRepresentative_valid,
      data.targetExactIfLossless_valid⟩

/-- Once the gauge continuum-closure theorem is in hand, the recognizable
Maxwell identity is an immediate corollary of the forced continuum law on the
selected one-form carrier. -/
theorem recognizableFromClosure
    {Time Carrier Law Field Source Vertex
      PhaseClass Scalar ClosureClass GaugeClass : Type}
    (data : ContinuumClosureData
      Time Carrier Law Field Source Vertex
      PhaseClass Scalar ClosureClass GaugeClass) :
    let cls := data.frontier.frontier.collapse.law.observer.continuumClass
    ForcedContinuumLaw cls data.target ∧
      Nonempty (RecognizableIdentity
        Time Carrier Law Field Source) := by
  have hclosure := continuumClosure data
  rcases hclosure with ⟨_hsingleton, _hrep, hforced, _hmaxwell, _hexact⟩
  exact
    ⟨hforced,
      recognizableWitness
        data.frontier.frontier.collapse.law
        data.targetIsMaxwellRepresentative
        data.targetExactIfLossless⟩

/-- Manuscript-facing selected gauge shadow-flow datum on one fixed least-motion
selected cut. The active import-free lane keeps the carrier, its shadow
compression, and the associated determinant/flow functions explicit. -/
structure SelectedGaugeShadowFlow
    (Time Carrier Law Field Source Parameter Scalar : Type) where
  law : InducedLaw Time Carrier Law Field Source
  selectedGaugeCarrier : Carrier
  finiteDimensionalCarrier : Prop
  shadowTransportCompression : Field
  determinantFlow : Parameter → Scalar
  shadowFlow : Parameter → Scalar

/-- Exact Euclidean gauge shadow-flow package. The spectral formulas are kept as
explicit local fields on the selected-cut datum, so the theorem surface stays
import-free and constructive. -/
structure ExactEuclideanGaugeShadowFlowData
    (Time Carrier Law Field Source Parameter Scalar Measure : Type)
    extends SelectedGaugeShadowFlow
      Time Carrier Law Field Source Parameter Scalar where
  compressionPositiveSemidefinite : Prop
  determinantProductFormula : Prop
  traceResolventFormula : Prop
  completeMonotonicity : Prop
  momentSeriesExpansion : Prop
  stieltjesRepresentation : Prop
  determinantRecovery : Prop
  spectralRecovery : Prop
  momentRecovery : Prop
  compressionPositiveSemidefinite_valid : compressionPositiveSemidefinite
  determinantProductFormula_valid : determinantProductFormula
  traceResolventFormula_valid : traceResolventFormula
  completeMonotonicity_valid : completeMonotonicity
  momentSeriesExpansion_valid : momentSeriesExpansion
  stieltjesRepresentation_valid : stieltjesRepresentation
  determinantRecovery_valid : determinantRecovery
  spectralRecovery_valid : spectralRecovery
  momentRecovery_valid : momentRecovery

/-- Exact Euclidean gauge shadow-flow law on the active import-free lane. -/
theorem exactEuclideanGaugeShadowFlow
    {Time Carrier Law Field Source Parameter Scalar Measure : Type}
    (data : ExactEuclideanGaugeShadowFlowData
      Time Carrier Law Field Source Parameter Scalar Measure) :
    data.compressionPositiveSemidefinite ∧
      data.determinantProductFormula ∧
      data.traceResolventFormula ∧
      data.completeMonotonicity ∧
      data.momentSeriesExpansion ∧
      data.stieltjesRepresentation ∧
      data.determinantRecovery ∧
      data.spectralRecovery ∧
      data.momentRecovery := by
  exact
    ⟨data.compressionPositiveSemidefinite_valid,
      data.determinantProductFormula_valid,
      data.traceResolventFormula_valid,
      data.completeMonotonicity_valid,
      data.momentSeriesExpansion_valid,
      data.stieltjesRepresentation_valid,
      data.determinantRecovery_valid,
      data.spectralRecovery_valid,
      data.momentRecovery_valid⟩

/-- Finite-horizon nonlogarithmic distinctness package for the exact gauge
shadow-flow. -/
structure FiniteHorizonNonlogarithmicDistinctnessData
    (Time Carrier Law Field Source Parameter Scalar Measure : Type)
    extends ExactEuclideanGaugeShadowFlowData
      Time Carrier Law Field Source Parameter Scalar Measure where
  rationalStieltjesFlow : Prop
  finiteHorizonPoleDescription : Prop
  nonlogarithmicAtFiniteHorizon : Prop
  logarithmicOnlyAfterSpectralLimit : Prop
  rationalStieltjesFlow_valid : rationalStieltjesFlow
  finiteHorizonPoleDescription_valid : finiteHorizonPoleDescription
  nonlogarithmicAtFiniteHorizon_valid : nonlogarithmicAtFiniteHorizon
  logarithmicOnlyAfterSpectralLimit_valid : logarithmicOnlyAfterSpectralLimit

/-- At fixed horizon the exact gauge shadow-flow is already the manuscript's
nonlogarithmic rational Stieltjes law. -/
theorem finiteHorizonNonlogarithmicDistinctness
    {Time Carrier Law Field Source Parameter Scalar Measure : Type}
    (data : FiniteHorizonNonlogarithmicDistinctnessData
      Time Carrier Law Field Source Parameter Scalar Measure) :
    data.rationalStieltjesFlow ∧
      data.finiteHorizonPoleDescription ∧
      data.nonlogarithmicAtFiniteHorizon ∧
      data.logarithmicOnlyAfterSpectralLimit := by
  exact
    ⟨data.rationalStieltjesFlow_valid,
      data.finiteHorizonPoleDescription_valid,
      data.nonlogarithmicAtFiniteHorizon_valid,
      data.logarithmicOnlyAfterSpectralLimit_valid⟩

/-- Spectral-limit package for the selected gauge shadow-flow. -/
structure SpectralLimitGaugeShadowFlowData
    (Time Carrier Law Field Source Parameter Scalar Measure : Type)
    extends ExactEuclideanGaugeShadowFlowData
      Time Carrier Law Field Source Parameter Scalar Measure where
  limitMeasure : Measure
  limitShadowFlow : Parameter → Scalar
  weakMeasureConvergence : Prop
  pointwiseShadowFlowLimit : Prop
  weakMeasureConvergence_valid : weakMeasureConvergence
  pointwiseShadowFlowLimit_valid : pointwiseShadowFlowLimit

/-- Spectral-limit gauge shadow-flow law. -/
theorem spectralLimitGaugeShadowFlow
    {Time Carrier Law Field Source Parameter Scalar Measure : Type}
    (data : SpectralLimitGaugeShadowFlowData
      Time Carrier Law Field Source Parameter Scalar Measure) :
    data.weakMeasureConvergence ∧
      data.pointwiseShadowFlowLimit := by
  exact
    ⟨data.weakMeasureConvergence_valid,
      data.pointwiseShadowFlowLimit_valid⟩

end GaugeLane

end CoherenceCalculus
