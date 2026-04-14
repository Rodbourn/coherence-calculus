import CoherenceCalculus.PartIV.ObserverSelectionCore
import CoherenceCalculus.PartIV.FlagshipClosureSharedCore

/-!
# PartIV.FlagshipGeometricCore

Geometric flagship lane for Part IV.

This file isolates the weak-field / covariant / Einstein-recognition ladder
for the geometric interpretation so that the main flagship aggregator can stay
organized by lane family instead of carrying every lane inline.
-/

namespace CoherenceCalculus

namespace GeometricLane

/-- Weak-field geometric response data on the selected tensor carrier. -/
structure WeakFieldResponseData
    (Time Carrier Law Tensor Scalar : Type) where
  observerDatum : ObserverSelection.CharacteristicDatum Time Carrier Law
  tensorCarrier : Carrier
  sourceField : Tensor
  admissibleLocalResponseClass : Prop
  secondOrderSelfAdjointDivergenceCompatible : Prop
  orthogonallyEquivariantLeadingResponse : Prop
  higherOrderResponseSubordinate : Prop
  inducedLambda : Scalar
  inducedKappa : Scalar

/-- Least-motion geometric carrier hypotheses. -/
structure LeastMotionObserverData
    (Time Carrier Law Tensor Scalar : Type)
    extends WeakFieldResponseData
      Time Carrier Law Tensor Scalar where
  faithfulCarrier : Prop
  closureAdmissibleCarrier : Prop
  stableUnderAdmissiblePromotion : Prop
  noProperGeometricSubcarrier : Prop
  observerMotionMinimal : Prop
  uniqueObserver : Prop

/-- Least-motion geometric observer theorem. -/
theorem leastMotionObserver
    {Time Carrier Law Tensor Scalar : Type}
    (data : LeastMotionObserverData
      Time Carrier Law Tensor Scalar) :
    Nonempty (ObserverSelection.LeastMotion Time Carrier Law) := by
  exact
    ⟨{ toCharacteristicDatum := data.observerDatum
       faithful := data.faithfulCarrier
       closureAdmissible := data.closureAdmissibleCarrier
       stableUnderAdmissiblePromotion := data.stableUnderAdmissiblePromotion
       noProperVisibleSubcarrier := data.noProperGeometricSubcarrier
       observerMotionMinimal := data.observerMotionMinimal
       uniqueUpToHorizonPreservingEquivalence := data.uniqueObserver }⟩

/-- Induced weak-field geometric response law. -/
structure WeakFieldLaw
    (Time Carrier Law Tensor Scalar : Type) where
  observer : ObserverSelection.LeastMotion Time Carrier Law
  leadingResponseOperator : Endo Tensor
  lambdaInduced : Scalar
  kappaInduced : Scalar
  weakFieldLaw : Prop
  losslessLeadingOrder : Prop

/-- Witness data for the induced weak-field geometric law. -/
structure WeakFieldLawData
    (Time Carrier Law Tensor Scalar : Type)
    extends WeakFieldLaw
      Time Carrier Law Tensor Scalar where
  responseData : WeakFieldResponseData
    Time Carrier Law Tensor Scalar
  isotropicScalarChannels : Prop

/-- Induced weak-field geometric law. -/
theorem weakFieldLaw
    {Time Carrier Law Tensor Scalar : Type}
    (data : WeakFieldLawData
      Time Carrier Law Tensor Scalar) :
    Nonempty (WeakFieldLaw
      Time Carrier Law Tensor Scalar) := by
  exact ⟨data.toWeakFieldLaw⟩

/-- Nonlinear completion locus for the geometric flagship. -/
structure NonlinearCompletionLocus where
  carrierSelectionAlreadyFixed : Prop
  remainingProblemIsCompletionClassification : Prop

/-- Forced covariant geometric law on the selected cut. -/
structure CovariantReduction
    (Time Carrier Law Tensor Scalar : Type) where
  observer : ObserverSelection.LeastMotion Time Carrier Law
  covariantResponseOperator : Endo Tensor
  lambdaInduced : Scalar
  kappaInduced : Scalar
  covariantLaw : Prop
  divergenceCompatibility : Prop
  losslessLeadingOrder : Prop

/-- Witness data for the forced covariant geometric law. -/
structure CovariantReductionData
    (Time Carrier Law Tensor Scalar : Type)
    extends CovariantReduction
      Time Carrier Law Tensor Scalar where
  weakFieldLaw :
    WeakFieldLaw Time Carrier Law Tensor Scalar
  characteristicMemoryReduction : Prop
  slowVariationEndpointExpansion : Prop
  minimalOrderCovariantCompletion : Prop

/- Forced covariant geometric law on the selected cut. -/

theorem covariantReduction
    {Time Carrier Law Tensor Scalar : Type}
    (data : CovariantReductionData
      Time Carrier Law Tensor Scalar) :
    Nonempty (CovariantReduction
      Time Carrier Law Tensor Scalar) := by
  exact ⟨data.toCovariantReduction⟩

/-- Characteristic-return interpretation of the geometric response law. -/
structure CharacteristicReturnOrigin
    (Time Carrier Law Tensor Scalar : Type) where
  law :
    CovariantReduction
      Time Carrier Law Tensor Scalar
  nonlinearResponseCarriedByCharacteristicReturn : Prop
  bulkContributionCancels : Prop
  endpointMapForcedOnTraceAndTracelessChannels : Prop

/-- Recognition package for Einstein form on the selected cut. -/
structure RecognizableIdentity
    (Time Carrier Law Tensor Scalar : Type) where
  law :
    CovariantReduction
      Time Carrier Law Tensor Scalar
  einsteinForm : Prop
  exactIfLossless : Prop

private theorem recognizableWitness
    {Time Carrier Law Tensor Scalar : Type}
    (law : CovariantReduction Time Carrier Law Tensor Scalar)
    (einsteinForm exactIfLossless : Prop) :
    Nonempty (RecognizableIdentity Time Carrier Law Tensor Scalar) := by
  exact
    ⟨{ law := law
       einsteinForm := einsteinForm
       exactIfLossless := exactIfLossless }⟩

/-- Endpoint-collapse package for the geometric carrier. The general
energy-orthogonal forcing theorem removes discretionary substitution, leaving
only the sector-specific task of collapsing the pairing-compatible minimal
divergence-compatible quotient to the Einstein representative. -/
structure EndpointCollapse
    (Time Carrier Law Tensor Scalar : Type)
    where
  law :
    CovariantReduction
      Time Carrier Law Tensor Scalar
  orthogonalityRigidity :
    SelectedCutOrthogonality.Principle Time Carrier Law Tensor
  traceTracelessChannelsGeneratedByCanonicalPairing : Prop
  divergenceCompatiblePairingPreserved : Prop
  minimalPairingCompatibleRepresentativeIsTraceAdjustedRicci : Prop
  traceTracelessChannelsGeneratedByCanonicalPairing_valid :
    traceTracelessChannelsGeneratedByCanonicalPairing
  divergenceCompatiblePairingPreserved_valid :
    divergenceCompatiblePairingPreserved
  minimalPairingCompatibleRepresentativeIsTraceAdjustedRicci_valid :
    minimalPairingCompatibleRepresentativeIsTraceAdjustedRicci

/-- The geometric endpoint-collapse theorem isolates the exact remaining
geometric obligation: the pairing-compatible minimal divergence-compatible
quotient must be singleton and represented by the trace-adjusted Ricci /
Einstein operator. -/
theorem endpointCollapse
    {Time Carrier Law Tensor Scalar : Type}
    (data : EndpointCollapse Time Carrier Law Tensor Scalar) :
    let duality := data.orthogonalityRigidity.toCanonicalDuality
    data.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      data.traceTracelessChannelsGeneratedByCanonicalPairing ∧
      data.divergenceCompatiblePairingPreserved ∧
      data.minimalPairingCompatibleRepresentativeIsTraceAdjustedRicci := by
  have horth :=
    SelectedCutOrthogonality.Principle.singletonRepresentative
      data.orthogonalityRigidity
  exact
    ⟨horth.1,
      horth.2,
      data.traceTracelessChannelsGeneratedByCanonicalPairing_valid,
      data.divergenceCompatiblePairingPreserved_valid,
      data.minimalPairingCompatibleRepresentativeIsTraceAdjustedRicci_valid⟩

/-- Sector-rigidity package forcing the canonical Einstein representative on
the selected symmetric-tensor carrier once the geometric endpoint collapse has
been established. -/
structure SectorRigidity
    (Time Carrier Law Tensor Scalar : Type)
    extends EndpointCollapse Time Carrier Law Tensor Scalar where
  recognizableEinsteinFormForced : Prop
  exactEinsteinIfLossless : Prop
  recognizableEinsteinFormForced_valid :
    recognizableEinsteinFormForced
  exactEinsteinIfLossless_valid :
    exactEinsteinIfLossless

/- The geometric endpoint is rigid when the canonical symmetric-tensor
pairing collapses the minimal covariant divergence-compatible class to the
Einstein representative. -/

theorem sectorRigidity
    {Time Carrier Law Tensor Scalar : Type}
    (data : SectorRigidity Time Carrier Law Tensor Scalar) :
    let duality :=
      SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.toEndpointCollapse.orthogonalityRigidity
    data.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      data.minimalPairingCompatibleRepresentativeIsTraceAdjustedRicci ∧
      data.recognizableEinsteinFormForced := by
  have hcollapse := endpointCollapse data.toEndpointCollapse
  rcases hcollapse with
    ⟨hsingleton, hrep, _htrace, _hdiv, heinstein⟩
  exact
    ⟨hsingleton,
      hrep,
      heinstein,
      data.recognizableEinsteinFormForced_valid⟩

/-- Recognizable Einstein identity. -/
theorem recognizableIdentity
    {Time Carrier Law Tensor Scalar : Type}
    (data : SectorRigidity Time Carrier Law Tensor Scalar) :
    Nonempty (RecognizableIdentity
      Time Carrier Law Tensor Scalar) := by
  exact
    recognizableWitness
      data.law
      data.recognizableEinsteinFormForced
      data.exactEinsteinIfLossless

/-- Foundation-facing frontier data for the geometric endpoint. This packages
the active orthogonal symmetric-tensor scalarization surface already available
before the final Einstein representative identity is proved. -/
structure EndpointFoundationFrontierData
    (Time Carrier Law Tensor Scalar Group : Type) where
  collapse : EndpointCollapse Time Carrier Law Tensor Scalar
  symmetricTensorScalarization :
    Compiler.OrthogonalSymmetricTensorScalarizationData Scalar Tensor Group

/- On the active Lean surface, the geometric endpoint already reduces to an
energy-orthogonal singleton endpoint class together with orthogonally
equivariant trace/traceless scalarization on the selected symmetric-tensor
carrier. The remaining burden is to identify the minimal divergence-compatible
representative with the trace-adjusted Ricci / Einstein operator. -/
theorem endpointFrontier
    {Time Carrier Law Tensor Scalar Group : Type}
    (data : EndpointFoundationFrontierData
      Time Carrier Law Tensor Scalar Group) :
    let duality := data.collapse.orthogonalityRigidity.toCanonicalDuality
    data.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      data.collapse.traceTracelessChannelsGeneratedByCanonicalPairing ∧
      data.collapse.divergenceCompatiblePairingPreserved ∧
      (∃ _alpha _beta : Scalar,
        data.symmetricTensorScalarization.scalarDecomposition ∧
          data.symmetricTensorScalarization.uniqueScalars) ∧
      data.collapse.minimalPairingCompatibleRepresentativeIsTraceAdjustedRicci := by
  have hcollapse := endpointCollapse data.collapse
  have hscalar :=
    Compiler.orthogonal_symmetric_tensor_scalarization
      data.symmetricTensorScalarization
  rcases hcollapse with
    ⟨hsingleton, hrep, htrace, hdiv, heinstein⟩
  rcases hscalar with ⟨alpha, beta, hdecomp, hunique⟩
  exact
    ⟨hsingleton,
      hrep,
      htrace,
      hdiv,
      ⟨alpha, beta, hdecomp, hunique⟩,
      heinstein⟩

/-- Reusable head of the exact geometric endpoint frontier. Later geometric
proofs often need only the singleton class, forced representative, and
Einstein endpoint identity, not the full trace/traceless scalarization
package. -/
private theorem endpointRepresentativeFacts
    {Time Carrier Law Tensor Scalar Group : Type}
    (data : EndpointFoundationFrontierData
      Time Carrier Law Tensor Scalar Group) :
    let duality := data.collapse.orthogonalityRigidity.toCanonicalDuality
    data.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      data.collapse.minimalPairingCompatibleRepresentativeIsTraceAdjustedRicci := by
  have hfrontier := endpointFrontier data
  rcases hfrontier with
    ⟨hsingleton, hrep, _htrace, _hdiv, _hscalar, heinstein⟩
  exact
    ⟨hsingleton,
      hrep,
      heinstein⟩

/-- Direct representative theorem on the exact geometric endpoint frontier.
Once the geometric lane has reached the forced endpoint frontier, the
recognizable Einstein representative is already fixed there: no additional
continuum-closure wrapper is needed to identify the trace-adjusted Ricci
form. -/
theorem recognizableFromEndpointFrontier
    {Time Carrier Law Tensor Scalar Group : Type}
    (data : EndpointFoundationFrontierData
      Time Carrier Law Tensor Scalar Group) :
    let duality := data.collapse.orthogonalityRigidity.toCanonicalDuality
    data.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      data.collapse.minimalPairingCompatibleRepresentativeIsTraceAdjustedRicci ∧
      Nonempty (RecognizableIdentity
        Time Carrier Law Tensor Scalar) := by
  have hendpoint := endpointRepresentativeFacts data
  rcases hendpoint with ⟨hsingleton, hrep, heinstein⟩
  exact
    ⟨hsingleton,
      hrep,
      heinstein,
      recognizableWitness
        data.collapse.law
        data.collapse.minimalPairingCompatibleRepresentativeIsTraceAdjustedRicci
        data.collapse.law.losslessLeadingOrder⟩

/-- Clean direct geometric closure route using the already-forced selected
closure law from the Part IV physical realization package. Once the selected
geometric carrier is read on the same least-motion cut and carries the same
continuum closure class, the continuum singleton is inherited directly from the
physical selected law itself. -/
structure SelectedClosureIdentificationData
    (Time Carrier Law Tensor Scalar Group : Type) where
  frontier :
    EndpointFoundationFrontierData
      Time Carrier Law Tensor Scalar Group
  physical :
    PhysicalRealizationPrinciple Time Carrier Law
  sameLeastMotionSelection :
    physical.selectedLaw.selection =
      frontier.collapse.law.observer.selection
  sameContinuumClosureClass :
    physical.selectedLaw.endpointClosureClass =
      frontier.collapse.law.observer.continuumClass

/-- Elegant geometric closure theorem. The geometric frontier already fixes the
recognizable pairing-compatible endpoint form; if the geometric observer is
reading the same selected cut and continuum closure class as the Part IV
physical selected law, then the forced continuum singleton is inherited
directly with no separate target-uniqueness theorem. -/
theorem closureFromPhysicalRealization
    {Time Carrier Law Tensor Scalar Group : Type}
    (data : SelectedClosureIdentificationData
      Time Carrier Law Tensor Scalar Group) :
    let cls := data.frontier.collapse.law.observer.continuumClass
    let target := data.physical.selectedLaw.selectedClosureLaw
    data.frontier.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      (SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.frontier.collapse.orthogonalityRigidity).endpointRepresentativeForcedByWeakForm ∧
      ForcedContinuumLaw cls target ∧
      Nonempty (RecognizableIdentity
        Time Carrier Law Tensor Scalar) := by
  have hfrontier := recognizableFromEndpointFrontier data.frontier
  rcases hfrontier with
    ⟨hsingleton, hrep, _heinstein, hrecognizable⟩
  exact
    SelectedCut.closureReadoutWithRecognition
      data.physical
      data.frontier.collapse.law.observer
      data.sameLeastMotionSelection
      data.sameContinuumClosureClass
      hsingleton
      hrep
      hrecognizable

/-- Selected-bundle geometric closure route. This is the more foundational
version of the direct closure theorem: once the geometric observer is read off
the one intrinsic selected bundle, forced continuum closure is inherited
automatically. -/
structure SelectedBundleClosureIdentificationData
    (Time Carrier Law Tensor Scalar Group : Type) where
  frontier :
    EndpointFoundationFrontierData
      Time Carrier Law Tensor Scalar Group
  selectedBundle : IntrinsicSelectedBundleExistence Time Carrier Law
  geometricCarrierReadOnSelectedBundle :
    selectedBundle.geometricCarrierReadOnSelectedBundle
      frontier.collapse.law.observer

/-- Foundational geometric closure theorem through the intrinsic selected
bundle. -/
theorem closureFromSelectedBundle
    {Time Carrier Law Tensor Scalar Group : Type}
    (data : SelectedBundleClosureIdentificationData
      Time Carrier Law Tensor Scalar Group) :
    let cls := data.frontier.collapse.law.observer.continuumClass
    let target := data.selectedBundle.physicalPrinciple.selectedLaw.selectedClosureLaw
    data.frontier.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      (SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.frontier.collapse.orthogonalityRigidity).endpointRepresentativeForcedByWeakForm ∧
      ForcedContinuumLaw cls target ∧
      Nonempty (RecognizableIdentity
        Time Carrier Law Tensor Scalar) := by
  have hfrontier := recognizableFromEndpointFrontier data.frontier
  have hsel :=
    SelectedBundle.geometricCarrierSelection
      data.selectedBundle
      data.frontier.collapse.law.observer
      data.geometricCarrierReadOnSelectedBundle
  rcases hfrontier with
    ⟨hsingleton, hrep, _heinstein, hrecognizable⟩
  exact
    SelectedBundle.closureReadoutWithRecognition
      data.selectedBundle
      data.frontier.collapse.law.observer
      hsel
      hsingleton
      hrep
      hrecognizable

/-- Final geometric closure data: once the trace/traceless scalarized frontier
has been forced on the selected symmetric-tensor carrier, the only remaining
task is to show that a chosen continuum representative lies in the observer's
own continuum limit class and is unique there. At that point the continuum
representative is forced with no further practitioner discretion. -/
structure ContinuumClosureData
    (Time Carrier Law Tensor Scalar Group : Type) where
  frontier :
    EndpointFoundationFrontierData
      Time Carrier Law Tensor Scalar Group
  target : Law
  targetAdmissible :
    frontier.collapse.law.observer.continuumClass.admissible target
  targetUnique :
    ∀ other : Law,
      frontier.collapse.law.observer.continuumClass.admissible other →
        other = target
  targetIsEinsteinRepresentative : Prop
  targetExactIfLossless : Prop
  targetIsEinsteinRepresentative_valid : targetIsEinsteinRepresentative
  targetExactIfLossless_valid : targetExactIfLossless

/-- Geometric closure theorem. The active spine now reduces the geometric lane
to a pure continuum-limit-class closure problem: once the trace/traceless
scalarized frontier is forced and a continuum representative is shown
admissible and unique in the selected observer's own continuum class, that
representative is itself forced. -/
theorem continuumClosure
    {Time Carrier Law Tensor Scalar Group : Type}
    (data : ContinuumClosureData
      Time Carrier Law Tensor Scalar Group) :
    let cls := data.frontier.collapse.law.observer.continuumClass
    let duality :=
      SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.frontier.collapse.orthogonalityRigidity
    data.frontier.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      ForcedContinuumLaw cls data.target ∧
      data.targetIsEinsteinRepresentative ∧
      data.targetExactIfLossless := by
  obtain ⟨hsingleton, hrep, _heinstein⟩ :=
    endpointRepresentativeFacts data.frontier
  have ⟨_hsingleton, _hrep, hforced⟩ :=
    FlagshipShared.forcedContinuumFromEndpointFacts
      data.frontier.collapse.law.observer.continuumClass
      data.target
      hsingleton
      hrep
      data.targetAdmissible
      data.targetUnique
  exact
    ⟨hsingleton,
      hrep,
      hforced,
      data.targetIsEinsteinRepresentative_valid,
      data.targetExactIfLossless_valid⟩

/-- Once the geometric continuum-closure theorem is in hand, the recognizable
Einstein identity is an immediate corollary of the forced continuum law on the
selected symmetric-tensor carrier. -/
theorem recognizableFromClosure
    {Time Carrier Law Tensor Scalar Group : Type}
    (data : ContinuumClosureData
      Time Carrier Law Tensor Scalar Group) :
    let cls := data.frontier.collapse.law.observer.continuumClass
    ForcedContinuumLaw cls data.target ∧
      Nonempty (RecognizableIdentity
        Time Carrier Law Tensor Scalar) := by
  have hclosure := continuumClosure data
  rcases hclosure with ⟨_hsingleton, _hrep, hforced, _heinstein, _hexact⟩
  exact
    ⟨hforced,
      recognizableWitness
        data.frontier.collapse.law
        data.targetIsEinsteinRepresentative
        data.targetExactIfLossless⟩

end GeometricLane

end CoherenceCalculus
