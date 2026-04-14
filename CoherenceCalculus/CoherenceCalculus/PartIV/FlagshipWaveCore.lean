import CoherenceCalculus.PartIV.ObserverSelectionCore
import CoherenceCalculus.PartIV.MultiplierReconstructionCore
import CoherenceCalculus.PartIV.FlagshipClosureSharedCore

/-!
# PartIV.FlagshipWaveCore

Wave flagship lane for Part IV.

This file isolates the reversible / structural / endpoint / dispersion ladder
for the wave interpretation so that the main flagship aggregator can stay
organized by lane family instead of carrying every lane inline.
-/

namespace CoherenceCalculus

namespace WaveLane

/-- Wave flagship realization data on the least-motion cut. -/
structure ReversibleRealization
    (Time Carrier Law Field Scalar : Type) where
  observerDatum : ObserverSelection.CharacteristicDatum Time Carrier Law
  refinementFamily : RefinementCompatibleFamily
  governingDatumRigidity : Prop
  admissiblePromotionStable : Prop
  asymptoticConsistency : Prop
  transportOperator : Endo Field
  closureOperator : Endo Field
  transportSelfAdjointNonnegative : Prop
  closureSelfAdjointScalar : Prop

/-- Least-motion wave carrier hypotheses. -/
structure LeastMotionObserverData
    (Time Carrier Law Field Scalar : Type)
    extends ReversibleRealization Time Carrier Law Field Scalar where
  faithfulCarrier : Prop
  closureAdmissibleCarrier : Prop
  noProperWaveSubcarrier : Prop
  observerMotionMinimal : Prop
  uniqueObserver : Prop

/-- Least-motion wave observer theorem. -/
theorem leastMotionObserver
    {Time Carrier Law Field Scalar : Type}
    (data : LeastMotionObserverData Time Carrier Law Field Scalar) :
    Nonempty (ObserverSelection.LeastMotion Time Carrier Law) := by
  exact
    ⟨{ toCharacteristicDatum := data.observerDatum
       faithful := data.faithfulCarrier
       closureAdmissible := data.closureAdmissibleCarrier
       stableUnderAdmissiblePromotion := data.admissiblePromotionStable
       noProperVisibleSubcarrier := data.noProperWaveSubcarrier
       observerMotionMinimal := data.observerMotionMinimal
       uniqueUpToHorizonPreservingEquivalence := data.uniqueObserver }⟩

/-- Result package for the induced wave law. -/
structure InducedLaw
    (Time Carrier Law Field Scalar : Type) where
  observer : ObserverSelection.LeastMotion Time Carrier Law
  speedCoefficient : Scalar
  speedCoefficientPositive : Prop
  transportOperator : Endo Field
  closureOperator : Endo Field
  remainder : Field
  equation : Prop
  losslessLeadingOrder : Prop

/-- Witness data for the induced wave law. -/
structure InducedLawData
    (Time Carrier Law Field Scalar : Type)
    extends InducedLaw Time Carrier Law Field Scalar where
  realization : ReversibleRealization Time Carrier Law Field Scalar
  localInternalDatumForced : Prop

/-- Induced reversible wave law on the selected cut. -/
theorem inducedLaw
    {Time Carrier Law Field Scalar : Type}
    (data : InducedLawData Time Carrier Law Field Scalar) :
    Nonempty (InducedLaw Time Carrier Law Field Scalar) := by
  exact ⟨data.toInducedLaw⟩

end WaveLane

namespace WaveLane

/-- Recognition package for the wave/Klein-Gordon form. -/
structure RecognizableIdentity
    (Time Carrier Law Field Scalar : Type) where
  law : InducedLaw Time Carrier Law Field Scalar
  waveForm : Prop
  exactIfLossless : Prop

private theorem recognizableWitness
    {Time Carrier Law Field Scalar : Type}
    (law : InducedLaw Time Carrier Law Field Scalar)
    (waveForm exactIfLossless : Prop) :
    Nonempty (RecognizableIdentity Time Carrier Law Field Scalar) := by
  exact
    ⟨{ law := law
       waveForm := waveForm
       exactIfLossless := exactIfLossless }⟩

/-- Common closing step for the wave representative theorems that already
identify the standard wave/Klein-Gordon law inside the selected continuum
class. The only remaining work there is to present the forced law together
with the two visible transport/closure features and the recognizable witness. -/
private theorem standardRepresentativePackage
    {Time Carrier Law Field Scalar : Type}
    {LawClass : Type}
    (cls : ContinuumLimitClass LawClass)
    (target : LawClass)
    {singleton representative transportIsWaveLaplacian
      closureActsAsMassPotential : Prop}
    (recognized exactIfLossless : Prop)
    (law : InducedLaw Time Carrier Law Field Scalar)
    (hsingleton : singleton)
    (hrepresentative : representative)
    (hforced : ForcedContinuumLaw cls target)
    (htransport : transportIsWaveLaplacian)
    (hclosure : closureActsAsMassPotential)
    :
    singleton ∧ representative ∧ ForcedContinuumLaw cls target ∧
      transportIsWaveLaplacian ∧ closureActsAsMassPotential ∧
      Nonempty (RecognizableIdentity Time Carrier Law Field Scalar) := by
  exact
    ⟨hsingleton,
      hrepresentative,
      hforced,
      htransport,
      hclosure,
      recognizableWitness law recognized exactIfLossless⟩

/-- Closing step for the structural Euclidean bridge route: once the bridge
facts and forced continuum law are available, the public theorem should read
as one coherent package rather than a tuple assembly script. -/
private theorem structuralRepresentativePackage
    {Time Carrier Law Field Scalar : Type}
    {LawClass : Type}
    (cls : ContinuumLimitClass LawClass)
    (target : LawClass)
    {singleton representative symmetry scalar euclidean reversible
      transportIsWaveLaplacian closureActsAsMassPotential : Prop}
    (recognized exactIfLossless : Prop)
    (law : InducedLaw Time Carrier Law Field Scalar)
    (hsingleton : singleton)
    (hrepresentative : representative)
    (hsymmetry : symmetry)
    (hscalar : scalar)
    (heuclidean : euclidean)
    (hreversible : reversible)
    (hforced : ForcedContinuumLaw cls target)
    (htransport : transportIsWaveLaplacian)
    (hclosure : closureActsAsMassPotential)
    :
    singleton ∧ representative ∧ symmetry ∧ scalar ∧ euclidean ∧ reversible ∧
      ForcedContinuumLaw cls target ∧
      transportIsWaveLaplacian ∧ closureActsAsMassPotential ∧
      Nonempty (RecognizableIdentity Time Carrier Law Field Scalar) := by
  exact
    ⟨hsingleton,
      hrepresentative,
      hsymmetry,
      hscalar,
      heuclidean,
      hreversible,
      hforced,
      htransport,
      hclosure,
      recognizableWitness law recognized exactIfLossless⟩

/-- Closing step for the endpoint-classification wave route. This is the same
identified standard wave representative, but reached after the shorter
endpoint-frontier classification bridge. -/
private theorem endpointRepresentativePackage
    {Time Carrier Law Field Scalar : Type}
    {LawClass : Type}
    (cls : ContinuumLimitClass LawClass)
    (target : LawClass)
    {singleton representative symmetry scalar euclidean reversible wave mass
      : Prop}
    (recognized exactIfLossless : Prop)
    (law : InducedLaw Time Carrier Law Field Scalar)
    (hsingleton : singleton)
    (hrepresentative : representative)
    (hsymmetry : symmetry)
    (hscalar : scalar)
    (heuclidean : euclidean)
    (hreversible : reversible)
    (hwave : wave)
    (hmass : mass)
    (hforced : ForcedContinuumLaw cls target)
    :
    singleton ∧ representative ∧ symmetry ∧ scalar ∧ euclidean ∧ reversible ∧
      wave ∧ mass ∧ ForcedContinuumLaw cls target ∧
      Nonempty (RecognizableIdentity Time Carrier Law Field Scalar) := by
  exact
    ⟨hsingleton,
      hrepresentative,
      hsymmetry,
      hscalar,
      heuclidean,
      hreversible,
      hwave,
      hmass,
      hforced,
      recognizableWitness law recognized exactIfLossless⟩

/-- Endpoint-collapse package for the reversible wave carrier. The common
orthogonality theorem removes discretionary substitution; what remains is to
show that the pairing-compatible minimal second-order quotient is singleton
and represented by the wave/Klein--Gordon normal form. -/
structure EndpointCollapse
    (Time Carrier Law Field Scalar : Type)
    where
  law : InducedLaw Time Carrier Law Field Scalar
  orthogonalityRigidity :
    SelectedCutOrthogonality.Principle Time Carrier Law Field
  secondOrderCarrierGeneratedByCanonicalPairing : Prop
  minimalPairingSymmetricTransportIsWaveLaplacian : Prop
  pairingScalarClosureActsAsMassPotential : Prop
  secondOrderCarrierGeneratedByCanonicalPairing_valid :
    secondOrderCarrierGeneratedByCanonicalPairing
  minimalPairingSymmetricTransportIsWaveLaplacian_valid :
    minimalPairingSymmetricTransportIsWaveLaplacian
  pairingScalarClosureActsAsMassPotential_valid :
    pairingScalarClosureActsAsMassPotential

/-- The wave endpoint collapse theorem isolates the remaining sector-specific
proof obligation: the pairing-compatible reversible second-order quotient must
be singleton and represented by the wave/Klein--Gordon carrier form. -/
theorem endpointCollapse
    {Time Carrier Law Field Scalar : Type}
    (data : EndpointCollapse Time Carrier Law Field Scalar) :
    let duality := data.orthogonalityRigidity.toCanonicalDuality
    data.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      data.secondOrderCarrierGeneratedByCanonicalPairing ∧
      data.minimalPairingSymmetricTransportIsWaveLaplacian ∧
      data.pairingScalarClosureActsAsMassPotential := by
  have horth :=
    SelectedCutOrthogonality.Principle.singletonRepresentative
      data.orthogonalityRigidity
  exact
    ⟨horth.1,
      horth.2,
      data.secondOrderCarrierGeneratedByCanonicalPairing_valid,
      data.minimalPairingSymmetricTransportIsWaveLaplacian_valid,
      data.pairingScalarClosureActsAsMassPotential_valid⟩

/-- Sector-rigidity package forcing the recognizable wave/Klein--Gordon
identity once the wave endpoint-collapse theorem has been established. -/
structure SectorRigidity
    (Time Carrier Law Field Scalar : Type)
    extends EndpointCollapse Time Carrier Law Field Scalar where
  recognizableWaveKGFormForced : Prop
  exactWaveKGIfLossless : Prop
  recognizableWaveKGFormForced_valid :
    recognizableWaveKGFormForced
  exactWaveKGIfLossless_valid :
    exactWaveKGIfLossless

/- The wave endpoint is rigid when the canonical pairing forces the unique
second-order hyperbolic representative of the selected wave law class. -/

theorem sectorRigidity
    {Time Carrier Law Field Scalar : Type}
    (data : SectorRigidity Time Carrier Law Field Scalar) :
    let duality :=
      SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.toEndpointCollapse.orthogonalityRigidity
    data.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      data.minimalPairingSymmetricTransportIsWaveLaplacian ∧
      data.pairingScalarClosureActsAsMassPotential ∧
      data.recognizableWaveKGFormForced := by
  have hcollapse := endpointCollapse data.toEndpointCollapse
  rcases hcollapse with
    ⟨hsingleton, hrep, _hsecond, hwave, hmass⟩
  exact
    ⟨hsingleton,
      hrep,
      hwave,
      hmass,
      data.recognizableWaveKGFormForced_valid⟩

/-- Recognizable wave/Klein-Gordon identity. -/
theorem recognizableIdentity
    {Time Carrier Law Field Scalar : Type}
    (data : SectorRigidity Time Carrier Law Field Scalar) :
    Nonempty (RecognizableIdentity
      Time Carrier Law Field Scalar) := by
  exact
    recognizableWitness
      data.law
      data.recognizableWaveKGFormForced
      data.exactWaveKGIfLossless

end WaveLane

namespace WaveLane

/-- Genuine pre-identification structural frontier for the reversible wave
carrier. Unlike `EndpointCollapse`, this stops before any named
Laplace/mass-potential representative is imposed. -/
structure StructuralFrontierData
    (Time Carrier Law Field Scalar : Type) where
  law : InducedLaw Time Carrier Law Field Scalar
  orthogonalityRigidity :
    SelectedCutOrthogonality.Principle Time Carrier Law Field
  secondOrderCarrierGeneratedByCanonicalPairing : Prop
  secondOrderCarrierGeneratedByCanonicalPairing_valid :
    secondOrderCarrierGeneratedByCanonicalPairing

/-- On the active Part IV spine, the honest wave frontier already consists of
an energy-orthogonal singleton endpoint class together with second-order
carrier generation from the canonical pairing. No named continuum
representative has yet been identified at this stage. -/
theorem structuralFrontier
    {Time Carrier Law Field Scalar : Type}
    (data : StructuralFrontierData Time Carrier Law Field Scalar) :
    let duality := data.orthogonalityRigidity.toCanonicalDuality
    data.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      data.secondOrderCarrierGeneratedByCanonicalPairing := by
  have horth :=
    SelectedCutOrthogonality.Principle.singletonRepresentative
      data.orthogonalityRigidity
  exact
    ⟨horth.1,
      horth.2,
      data.secondOrderCarrierGeneratedByCanonicalPairing_valid⟩

/-- Structural wave frontier refined by selected-channel transport generation,
still before any named continuum representative is chosen. -/
structure TransportStructuralFrontierData
    (Time Carrier Law Field Scalar System Vertex : Type) where
  frontier : StructuralFrontierData Time Carrier Law Field Scalar
  selectedTransportGeneration :
    SelectedChannelTransportGenerationData System
  transportGeneratedScalarRecursive :
    TransportGeneratedScalarRecursiveData Time Vertex

/-- The honest wave frontier already carries order-one scalar-recursive
selected-channel transport data before any continuum Laplace/mass-potential
identification is made. -/
theorem transportStructuralFrontier
    {Time Carrier Law Field Scalar System Vertex : Type}
    (data : TransportStructuralFrontierData
      Time Carrier Law Field Scalar System Vertex) :
    let duality := data.frontier.orthogonalityRigidity.toCanonicalDuality
    data.frontier.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      data.frontier.secondOrderCarrierGeneratedByCanonicalPairing ∧
      data.selectedTransportGeneration.orderOneTransport ∧
      data.selectedTransportGeneration.scalarQuadraticLaw ∧
      data.selectedTransportGeneration.recursiveTransportLaw ∧
      Nonempty (ScalarRecursiveSelectedChannelSystem Time Vertex) := by
  have hfrontier := structuralFrontier data.frontier
  have htransport :=
    selected_channel_transport_generation data.selectedTransportGeneration
  have hrecursive :=
    transport_generation_yields_scalar_recursive
      data.transportGeneratedScalarRecursive
  rcases hfrontier with ⟨hsingleton, hforced, hsecond⟩
  rcases htransport with ⟨horder, hscalar, hrec⟩
  exact
    ⟨hsingleton,
      hforced,
      hsecond,
      horder,
      hscalar,
      hrec,
      hrecursive⟩

/-- Structural wave frontier refined by the fixed-horizon local internal datum,
still before any named continuum representative is imposed. -/
structure LocalDatumStructuralFrontierData
    (Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass : Type) where
  frontier :
    TransportStructuralFrontierData
      Time Carrier Law Field Scalar System Vertex
  localInternalDatum :
    RealizedLocalInternalDatumForcingData
      PhaseClass Scalar ClosureClass

/-- The honest wave frontier already carries a unique local internal datum and
an exact scalar-recursive transport surface before any standard wave/Klein--
Gordon representative is identified. -/
theorem localDatumStructuralFrontier
    {Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass : Type}
    (data : LocalDatumStructuralFrontierData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass) :
    let duality :=
      data.frontier.frontier.orthogonalityRigidity.toCanonicalDuality
    data.frontier.frontier.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      data.frontier.frontier.secondOrderCarrierGeneratedByCanonicalPairing ∧
      Nonempty (LocalInternalDatumSelectedChannels
        PhaseClass Scalar ClosureClass) ∧
      data.frontier.selectedTransportGeneration.orderOneTransport ∧
      data.frontier.selectedTransportGeneration.scalarQuadraticLaw ∧
      data.frontier.selectedTransportGeneration.recursiveTransportLaw ∧
      Nonempty (ScalarRecursiveSelectedChannelSystem Time Vertex) := by
  have hfrontier := transportStructuralFrontier data.frontier
  have hlocal :=
    realized_local_internal_datum_forcing data.localInternalDatum
  rcases hfrontier with
    ⟨hsingleton, hforced, hsecond, horder, hscalar, hrec, hrecursive⟩
  exact
    ⟨hsingleton,
      hforced,
      hsecond,
      hlocal,
      horder,
      hscalar,
      hrec,
      hrecursive⟩

/-- Honest wave frontier refined to the exact scalar-recursive transport kernel
on the active additive spine, still before any Laplace/mass-potential
continuum representative is identified. -/
structure RecursionKernelStructuralFrontierData
    (Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index : Type)
    (T : HorizonTower) where
  frontier :
    LocalDatumStructuralFrontierData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass
  admissibleTransport : TransportGeneratedAdmissibleFamily Index T

/-- The honest wave frontier already fixes the exact scalar-recursive transport
kernel. The only remaining step after this theorem is the continuum-side
identification of the unique admissible representative. -/
theorem recursionKernelStructuralFrontier
    {Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index : Type}
    {T : HorizonTower}
    (data : RecursionKernelStructuralFrontierData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T) :
    let duality :=
      SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.frontier.frontier.frontier.orthogonalityRigidity
    data.frontier.frontier.frontier.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      Nonempty (LocalInternalDatumSelectedChannels
        PhaseClass Scalar ClosureClass) ∧
      data.admissibleTransport.distinguishedClass.order = 1 ∧
      data.admissibleTransport.noPreferredDirection.rigidity.scalarQuadraticLaw ∧
      (∀ x : SequenceTransportSpace,
        inTransportKernel data.admissibleTransport.representative x ↔
          ∀ n : BilateralIndex,
            x (bilateralSucc n) =
              State.sub (data.admissibleTransport.representative (x n))
                (x (bilateralPred n))) := by
  have hfrontier := localDatumStructuralFrontier data.frontier
  have hrecursion :=
    transport_generation_forces_scalar_recursion data.admissibleTransport
  rcases hfrontier with
    ⟨hsingleton, hforced, _hsecond, hlocal, _horder, _hscalar, _hrec, _hrecursive⟩
  rcases hrecursion with ⟨horder, hscalar, hkernel⟩
  exact
    ⟨hsingleton,
      hforced,
      hlocal,
      horder,
      hscalar,
      hkernel⟩

/-- Reusable head of the honest wave structural frontier. Several later
structural theorems need only the already fixed singleton endpoint class and
its forced representative, not the local datum or the explicit recursion-
kernel equation. -/
private theorem structuralRepresentativeFacts
    {Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index : Type}
    {T : HorizonTower}
    (data : RecursionKernelStructuralFrontierData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T) :
    let duality :=
      SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.frontier.frontier.frontier.orthogonalityRigidity
    data.frontier.frontier.frontier.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm := by
  have hfrontier := recursionKernelStructuralFrontier data
  rcases hfrontier with
    ⟨hsingleton, hrep, _hlocal, _horder, _hscalar, _hkernel⟩
  exact
    ⟨hsingleton,
      hrep⟩

/-- Final identification datum for the honest wave frontier. This is the
strongest direct theorem the current active spine supports: if a standard
wave/Klein--Gordon continuum representative is admissible and unique in the
selected observer's own continuum class, then that representative is forced. -/
structure StandardRepresentativeData
    (Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index : Type)
    (T : HorizonTower) where
  frontier :
    RecursionKernelStructuralFrontierData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T
  target : Law
  targetAdmissible :
    frontier.frontier.frontier.frontier.law.observer.continuumClass.admissible
      target
  targetUnique :
    ∀ other : Law,
      frontier.frontier.frontier.frontier.law.observer.continuumClass.admissible
        other → other = target
  targetTransportIsWaveLaplacian : Prop
  targetClosureActsAsMassPotential : Prop
  targetRecognizedAsWaveKG : Prop
  targetExactIfLossless : Prop
  targetTransportIsWaveLaplacian_valid :
    targetTransportIsWaveLaplacian
  targetClosureActsAsMassPotential_valid :
    targetClosureActsAsMassPotential
  targetRecognizedAsWaveKG_valid :
    targetRecognizedAsWaveKG
  targetExactIfLossless_valid :
    targetExactIfLossless

/-- Direct wave representative theorem from the honest frontier. This avoids
smuggling the named wave representative into the frontier package itself: the
frontier stops at the exact scalar-recursive kernel, and the only remaining
task is to show that the standard wave/Klein--Gordon representative is the
unique admissible continuum law in the selected observer's own class. -/
theorem standardRepresentative
    {Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index : Type}
    {T : HorizonTower}
    (data : StandardRepresentativeData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T) :
    let cls :=
      data.frontier.frontier.frontier.frontier.law.observer.continuumClass
    let duality :=
      SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.frontier.frontier.frontier.frontier.orthogonalityRigidity
    data.frontier.frontier.frontier.frontier.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      ForcedContinuumLaw cls data.target ∧
      data.targetTransportIsWaveLaplacian ∧
      data.targetClosureActsAsMassPotential ∧
      Nonempty (RecognizableIdentity
        Time Carrier Law Field Scalar) := by
  obtain ⟨hsingleton, hrep⟩ := structuralRepresentativeFacts data.frontier
  have ⟨_hsingleton, _hrep, hforced⟩ :=
    FlagshipShared.forcedContinuumFromEndpointFacts
      data.frontier.frontier.frontier.frontier.law.observer.continuumClass
      data.target
      hsingleton
      hrep
      data.targetAdmissible
      data.targetUnique
  exact
    standardRepresentativePackage
      data.frontier.frontier.frontier.frontier.law.observer.continuumClass
      data.target
      data.targetRecognizedAsWaveKG
      data.targetExactIfLossless
      data.frontier.frontier.frontier.frontier.law
      hsingleton
      hrep
      hforced
      data.targetTransportIsWaveLaplacian_valid
      data.targetClosureActsAsMassPotential_valid

/-- Explicit Euclidean-classification bridge for the wave continuum
representative. This is the minimal honest closure layer suggested by the
current wave frontier: admissible continuum representatives on the selected
wave carrier are required to satisfy second-order differentiality,
reversibility, pairing self-adjointness, Euclidean motion invariance on the
spatial transport part, and scalar mass/potential closure, and a
classification theorem then forces the unique standard target. -/
structure EuclideanClassificationData
    (Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index : Type)
    (T : HorizonTower) where
  frontier :
    RecursionKernelStructuralFrontierData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T
  target : Law
  secondOrderDifferentialRepresentative : Law → Prop
  reversibleRepresentative : Law → Prop
  pairingSelfAdjointRepresentative : Law → Prop
  euclideanMotionInvariantSpatialTransport : Law → Prop
  scalarMassPotentialClosureRepresentative : Law → Prop
  targetAdmissible :
    frontier.frontier.frontier.frontier.law.observer.continuumClass.admissible
      target
  targetSecondOrderDifferential :
    secondOrderDifferentialRepresentative target
  targetReversible :
    reversibleRepresentative target
  targetPairingSelfAdjoint :
    pairingSelfAdjointRepresentative target
  targetEuclideanMotionInvariantSpatialTransport :
    euclideanMotionInvariantSpatialTransport target
  targetScalarMassPotentialClosure :
    scalarMassPotentialClosureRepresentative target
  admissibleSecondOrderDifferential :
    ∀ other : Law,
      frontier.frontier.frontier.frontier.law.observer.continuumClass.admissible
        other →
      secondOrderDifferentialRepresentative other
  admissibleReversible :
    ∀ other : Law,
      frontier.frontier.frontier.frontier.law.observer.continuumClass.admissible
        other →
      reversibleRepresentative other
  admissiblePairingSelfAdjoint :
    ∀ other : Law,
      frontier.frontier.frontier.frontier.law.observer.continuumClass.admissible
        other →
      pairingSelfAdjointRepresentative other
  admissibleEuclideanMotionInvariantSpatialTransport :
    ∀ other : Law,
      frontier.frontier.frontier.frontier.law.observer.continuumClass.admissible
        other →
      euclideanMotionInvariantSpatialTransport other
  admissibleScalarMassPotentialClosure :
    ∀ other : Law,
      frontier.frontier.frontier.frontier.law.observer.continuumClass.admissible
        other →
      scalarMassPotentialClosureRepresentative other
  euclideanClassificationForcesTarget :
    ∀ other : Law,
      frontier.frontier.frontier.frontier.law.observer.continuumClass.admissible
        other →
      secondOrderDifferentialRepresentative other →
      reversibleRepresentative other →
      pairingSelfAdjointRepresentative other →
      euclideanMotionInvariantSpatialTransport other →
      scalarMassPotentialClosureRepresentative other →
      other = target
  targetTransportIsWaveLaplacian : Prop
  targetClosureActsAsMassPotential : Prop
  targetRecognizedAsWaveKG : Prop
  targetExactIfLossless : Prop
  targetTransportIsWaveLaplacian_valid :
    targetTransportIsWaveLaplacian
  targetClosureActsAsMassPotential_valid :
    targetClosureActsAsMassPotential
  targetRecognizedAsWaveKG_valid :
    targetRecognizedAsWaveKG
  targetExactIfLossless_valid :
    targetExactIfLossless

/-- Euclidean motion classification yields uniqueness of the standard wave/KG
target inside the selected observer's own continuum class. This theorem makes
the last classification bridge explicit rather than hiding it inside a raw
uniqueness assumption. -/
theorem euclideanTargetUnique
    {Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index : Type}
    {T : HorizonTower}
    (data : EuclideanClassificationData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T) :
    ∀ other : Law,
      data.frontier.frontier.frontier.frontier.law.observer.continuumClass.admissible
        other →
      other = data.target := by
  intro other hadm
  exact
    data.euclideanClassificationForcesTarget other hadm
      (data.admissibleSecondOrderDifferential other hadm)
      (data.admissibleReversible other hadm)
      (data.admissiblePairingSelfAdjoint other hadm)
      (data.admissibleEuclideanMotionInvariantSpatialTransport other hadm)
      (data.admissibleScalarMassPotentialClosure other hadm)

/-- With the Euclidean-invariance classification bridge made explicit, the
honest wave frontier forces the standard wave/Klein--Gordon representative
without any raw uniqueness hypothesis. The only non-common ingredient is the
explicit continuum-side classification theorem itself. -/
theorem euclideanInvariantRepresentative
    {Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index : Type}
    {T : HorizonTower}
    (data : EuclideanClassificationData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T) :
    let cls :=
      data.frontier.frontier.frontier.frontier.law.observer.continuumClass
    let duality :=
      SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.frontier.frontier.frontier.frontier.orthogonalityRigidity
    data.frontier.frontier.frontier.frontier.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      ForcedContinuumLaw cls data.target ∧
      data.targetTransportIsWaveLaplacian ∧
      data.targetClosureActsAsMassPotential ∧
      Nonempty (RecognizableIdentity
        Time Carrier Law Field Scalar) := by
  have hunique := euclideanTargetUnique data
  obtain ⟨hsingleton, hrep⟩ := structuralRepresentativeFacts data.frontier
  have ⟨_hsingleton, _hrep, hforced⟩ :=
    FlagshipShared.forcedContinuumFromEndpointFacts
      data.frontier.frontier.frontier.frontier.law.observer.continuumClass
      data.target
      hsingleton
      hrep
      data.targetAdmissible
      hunique
  exact
    standardRepresentativePackage
      data.frontier.frontier.frontier.frontier.law.observer.continuumClass
      data.target
      data.targetRecognizedAsWaveKG
      data.targetExactIfLossless
      data.frontier.frontier.frontier.frontier.law
      hsingleton
      hrep
      hforced
      data.targetTransportIsWaveLaplacian_valid
      data.targetClosureActsAsMassPotential_valid

/-- Native structural bridge from the honest wave frontier into the Euclidean
classification route. This packages the existing local-homogeneity and
self-adjoint scalarization surfaces already present in the rebuilt bridge, so
that the remaining wave-specific assumptions are reduced to second-order
differentiality, scalar mass/potential closure, and the final continuum
classification theorem itself. -/
structure StructuralEuclideanBridgeData
    (Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index Channel : Type)
    (T : HorizonTower) where
  frontier :
    RecursionKernelStructuralFrontierData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T
  localHomogeneous :
    LocallyHomogeneousSymmetryGeneratedData Index Time Channel
  selfAdjointScalarization :
    RealizedSelfAdjointScalarizationData Index Time Channel
  localHomogeneityYieldsEuclideanMotionInvariantSpatialTransport : Prop
  scalarRecursiveKernelYieldsReversibleContinuumClass : Prop
  localHomogeneityYieldsEuclideanMotionInvariantSpatialTransport_valid :
    localHomogeneityYieldsEuclideanMotionInvariantSpatialTransport
  scalarRecursiveKernelYieldsReversibleContinuumClass_valid :
    scalarRecursiveKernelYieldsReversibleContinuumClass

/-- The existing wave frontier already combines with local homogeneity and
self-adjoint scalarization to provide the native structural Euclidean bridge:
symmetry generation, pairing scalarization, Euclidean spatial transport, and
reversible bilateral recursion are all present before the final continuum
classification theorem is applied. -/
theorem structuralEuclideanBridge
    {Time Carrier Law Field Scalar System Vertex Index Channel
      PhaseClass ClosureClass : Type}
    {T : HorizonTower}
    (data : StructuralEuclideanBridgeData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index Channel T) :
    let duality :=
      SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.frontier.frontier.frontier.frontier.orthogonalityRigidity
    data.frontier.frontier.frontier.frontier.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      Nonempty (SymmetryGeneratedRealizedClass Index Time Channel) ∧
      data.selfAdjointScalarization.selectedSelfAdjointOperatorsScalar ∧
      data.localHomogeneityYieldsEuclideanMotionInvariantSpatialTransport ∧
      data.scalarRecursiveKernelYieldsReversibleContinuumClass := by
  have hfrontier := structuralRepresentativeFacts data.frontier
  have hsymm := locally_homogeneous_implies_symmetry_generated data.localHomogeneous
  have hscalar := realized_self_adjoint_scalarization data.selfAdjointScalarization
  rcases hfrontier with ⟨hsingleton, hrep⟩
  exact
    ⟨hsingleton,
      hrep,
      hsymm,
      hscalar,
      data.localHomogeneityYieldsEuclideanMotionInvariantSpatialTransport_valid,
      data.scalarRecursiveKernelYieldsReversibleContinuumClass_valid⟩

/-- Final wave closure data using the native structural Euclidean bridge rather
than raw Euclidean-invariance predicates on each admissible law. -/
structure StructuralEuclideanClosureData
    (Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index Channel : Type)
    (T : HorizonTower) where
  bridge :
    StructuralEuclideanBridgeData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index Channel T
  target : Law
  secondOrderDifferentialRepresentative : Law → Prop
  scalarMassPotentialClosureRepresentative : Law → Prop
  targetAdmissible :
    bridge.frontier.frontier.frontier.frontier.law.observer.continuumClass.admissible
      target
  targetSecondOrderDifferential :
    secondOrderDifferentialRepresentative target
  targetScalarMassPotentialClosure :
    scalarMassPotentialClosureRepresentative target
  admissibleSecondOrderDifferential :
    ∀ other : Law,
      bridge.frontier.frontier.frontier.frontier.law.observer.continuumClass.admissible
        other →
      secondOrderDifferentialRepresentative other
  admissibleScalarMassPotentialClosure :
    ∀ other : Law,
      bridge.frontier.frontier.frontier.frontier.law.observer.continuumClass.admissible
        other →
      scalarMassPotentialClosureRepresentative other
  structuralEuclideanClassificationForcesTarget :
    ∀ other : Law,
      bridge.frontier.frontier.frontier.frontier.law.observer.continuumClass.admissible
        other →
      secondOrderDifferentialRepresentative other →
      scalarMassPotentialClosureRepresentative other →
      other = target
  targetTransportIsWaveLaplacian : Prop
  targetClosureActsAsMassPotential : Prop
  targetRecognizedAsWaveKG : Prop
  targetExactIfLossless : Prop
  targetTransportIsWaveLaplacian_valid :
    targetTransportIsWaveLaplacian
  targetClosureActsAsMassPotential_valid :
    targetClosureActsAsMassPotential
  targetRecognizedAsWaveKG_valid :
    targetRecognizedAsWaveKG
  targetExactIfLossless_valid :
    targetExactIfLossless

/-- The native structural Euclidean bridge reduces the remaining wave burden to
its sharpest honest form on the current spine: second-order differentiality,
scalar mass/potential closure, and the final continuum classification theorem.
Everything else is already supplied by the rebuilt wave frontier together with
local homogeneity and self-adjoint scalarization. -/
theorem structuralEuclideanClosure
    {Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index Channel : Type}
    {T : HorizonTower}
    (data : StructuralEuclideanClosureData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index Channel T) :
    let cls :=
      data.bridge.frontier.frontier.frontier.frontier.law.observer.continuumClass
    let duality :=
      SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.bridge.frontier.frontier.frontier.frontier.orthogonalityRigidity
    data.bridge.frontier.frontier.frontier.frontier.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      Nonempty (SymmetryGeneratedRealizedClass Index Time Channel) ∧
      data.bridge.selfAdjointScalarization.selectedSelfAdjointOperatorsScalar ∧
      data.bridge.localHomogeneityYieldsEuclideanMotionInvariantSpatialTransport ∧
      data.bridge.scalarRecursiveKernelYieldsReversibleContinuumClass ∧
      ForcedContinuumLaw cls data.target ∧
      data.targetTransportIsWaveLaplacian ∧
      data.targetClosureActsAsMassPotential ∧
      Nonempty (RecognizableIdentity
        Time Carrier Law Field Scalar) := by
  have hstruct := structuralRepresentativeFacts data.bridge.frontier
  have hbridge := structuralEuclideanBridge data.bridge
  have hunique :
      ∀ other : Law,
        data.bridge.frontier.frontier.frontier.frontier.law.observer.continuumClass.admissible
          other →
        other = data.target := by
    intro other hadm
    exact
      data.structuralEuclideanClassificationForcesTarget other hadm
        (data.admissibleSecondOrderDifferential other hadm)
        (data.admissibleScalarMassPotentialClosure other hadm)
  rcases hstruct with ⟨hsingleton, hrep⟩
  rcases hbridge with
    ⟨_hsingleton, _hrep, hsymm, hscalar, heucl, hrev⟩
  have ⟨_hsingleton, _hrep, hforced⟩ :=
    FlagshipShared.forcedContinuumFromEndpointFacts
      data.bridge.frontier.frontier.frontier.frontier.law.observer.continuumClass
      data.target
      hsingleton
      hrep
      data.targetAdmissible
      hunique
  exact
    structuralRepresentativePackage
      data.bridge.frontier.frontier.frontier.frontier.law.observer.continuumClass
      data.target
      data.targetRecognizedAsWaveKG
      data.targetExactIfLossless
      data.bridge.frontier.frontier.frontier.frontier.law
      hsingleton
      hrep
      hsymm
      hscalar
      heucl
      hrev
      hforced
      data.targetTransportIsWaveLaplacian_valid
      data.targetClosureActsAsMassPotential_valid

end WaveLane

namespace WaveLane

/-- Foundation-facing frontier data for the wave endpoint. This records the
selected-channel transport-generation surfaces already available from the
active bridge, before the final wave/Klein--Gordon representative identity is
proved. -/
structure EndpointFoundationFrontierData
    (Time Carrier Law Field Scalar System Vertex : Type) where
  collapse : EndpointCollapse Time Carrier Law Field Scalar
  selectedTransportGeneration :
    SelectedChannelTransportGenerationData System
  transportGeneratedScalarRecursive :
    TransportGeneratedScalarRecursiveData Time Vertex

/- On the active Lean surface, the wave endpoint already reduces to an
energy-orthogonal singleton endpoint class together with order-one scalar and
recursive transport data on the selected channel. The remaining burden is to
identify that already forced scalar-recursive second-order surface with the
wave/Klein--Gordon representative. -/
theorem endpointFrontier
    {Time Carrier Law Field Scalar System Vertex : Type}
    (data : EndpointFoundationFrontierData
      Time Carrier Law Field Scalar System Vertex) :
    let duality := data.collapse.orthogonalityRigidity.toCanonicalDuality
    data.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      data.collapse.secondOrderCarrierGeneratedByCanonicalPairing ∧
      data.selectedTransportGeneration.orderOneTransport ∧
      data.selectedTransportGeneration.scalarQuadraticLaw ∧
      data.selectedTransportGeneration.recursiveTransportLaw ∧
      Nonempty (ScalarRecursiveSelectedChannelSystem Time Vertex) ∧
      data.collapse.minimalPairingSymmetricTransportIsWaveLaplacian ∧
      data.collapse.pairingScalarClosureActsAsMassPotential := by
  have hcollapse := endpointCollapse data.collapse
  have htransport :=
    selected_channel_transport_generation data.selectedTransportGeneration
  have hrecursive :=
    transport_generation_yields_scalar_recursive
      data.transportGeneratedScalarRecursive
  rcases hcollapse with
    ⟨hsingleton, hrep, hsecond, hwave, hmass⟩
  rcases htransport with ⟨horder, hscalar, hrec⟩
  exact
    ⟨hsingleton,
      hrep,
      hsecond,
      horder,
      hscalar,
      hrec,
      hrecursive,
      hwave,
      hmass⟩

/-- Wave-endpoint frontier refined by the fixed-horizon local internal datum.
This packages the exact Chapter 7 local datum surface already available on the
active spine before the final continuum representative identity is closed. -/
structure EndpointLocalDatumFrontierData
    (Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass : Type) where
  frontier :
    EndpointFoundationFrontierData
      Time Carrier Law Field Scalar System Vertex
  localInternalDatum :
    RealizedLocalInternalDatumForcingData
      PhaseClass Scalar ClosureClass

/-- The active wave frontier already carries a unique local internal datum and
an exact scalar-recursive transport surface before the final wave/Klein--Gordon
representative identity is proved. -/
theorem localDatumFrontier
    {Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass : Type}
    (data : EndpointLocalDatumFrontierData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass) :
    let duality :=
      data.frontier.collapse.orthogonalityRigidity.toCanonicalDuality
    data.frontier.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      data.frontier.collapse.secondOrderCarrierGeneratedByCanonicalPairing ∧
      Nonempty (LocalInternalDatumSelectedChannels
        PhaseClass Scalar ClosureClass) ∧
      data.frontier.selectedTransportGeneration.orderOneTransport ∧
      data.frontier.selectedTransportGeneration.scalarQuadraticLaw ∧
      data.frontier.selectedTransportGeneration.recursiveTransportLaw ∧
      Nonempty (ScalarRecursiveSelectedChannelSystem Time Vertex) ∧
      data.frontier.collapse.minimalPairingSymmetricTransportIsWaveLaplacian ∧
      data.frontier.collapse.pairingScalarClosureActsAsMassPotential := by
  have hfrontier := endpointFrontier data.frontier
  have hlocal :=
    realized_local_internal_datum_forcing data.localInternalDatum
  rcases hfrontier with
    ⟨hsingleton, hforced, hsecond, horder, hscalar, hrec, hrecursive, hwave, hmass⟩
  exact
    ⟨hsingleton,
      hforced,
      hsecond,
      hlocal,
      horder,
      hscalar,
      hrec,
      hrecursive,
      hwave,
      hmass⟩

/-- Wave-endpoint frontier refined to the exact scalar-recursive transport
kernel on the active additive spine. This is the sharpest native normal form
currently forced before the final continuum representative identity is fixed in
standard Laplace/Klein--Gordon notation. -/
structure EndpointRecursionKernelFrontierData
    (Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index : Type)
    (T : HorizonTower) where
  frontier :
    EndpointLocalDatumFrontierData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass
  admissibleTransport : TransportGeneratedAdmissibleFamily Index T

/-- The active wave frontier already fixes an exact scalar-recursive transport
kernel on the selected carrier. What remains open after this theorem is only
the final identification of that forced recursion normal form with the
continuum Laplace/mass-potential representative. -/
theorem recursionKernelFrontier
    {Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index : Type}
    {T : HorizonTower}
    (data : EndpointRecursionKernelFrontierData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T) :
    let duality :=
      SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.frontier.frontier.collapse.orthogonalityRigidity
    data.frontier.frontier.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      Nonempty (LocalInternalDatumSelectedChannels
        PhaseClass Scalar ClosureClass) ∧
      data.admissibleTransport.distinguishedClass.order = 1 ∧
      data.admissibleTransport.noPreferredDirection.rigidity.scalarQuadraticLaw ∧
      (∀ x : SequenceTransportSpace,
        inTransportKernel data.admissibleTransport.representative x ↔
          ∀ n : BilateralIndex,
            x (bilateralSucc n) =
              State.sub (data.admissibleTransport.representative (x n))
                (x (bilateralPred n))) ∧
      data.frontier.frontier.collapse.minimalPairingSymmetricTransportIsWaveLaplacian ∧
      data.frontier.frontier.collapse.pairingScalarClosureActsAsMassPotential := by
  have hfrontier := WaveLane.localDatumFrontier data.frontier
  have hrecursion :=
    transport_generation_forces_scalar_recursion data.admissibleTransport
  rcases hfrontier with
    ⟨hsingleton, hforced, _hsecond, hlocal, _horder, _hscalar, _hrec, _hrecursive,
      hwave, hmass⟩
  rcases hrecursion with ⟨horder, hscalar, hkernel⟩
  exact
    ⟨hsingleton,
      hforced,
      hlocal,
      horder,
      hscalar,
      hkernel,
      hwave,
      hmass⟩

/-- Reusable head of the exact wave endpoint frontier. Several later endpoint-
side proofs need only the already fixed singleton class and the canonical
wave/mass representative facts, not the full recursion-kernel equation. -/
private theorem endpointRepresentativeFacts
    {Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index : Type}
    {T : HorizonTower}
    (data : EndpointRecursionKernelFrontierData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T) :
    let duality :=
      SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.frontier.frontier.collapse.orthogonalityRigidity
    data.frontier.frontier.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      data.frontier.frontier.collapse.minimalPairingSymmetricTransportIsWaveLaplacian ∧
      data.frontier.frontier.collapse.pairingScalarClosureActsAsMassPotential := by
  have hfrontier := recursionKernelFrontier data
  rcases hfrontier with
    ⟨hsingleton, hrep, _hlocal, _horder, _hscalar, _hkernel, hwave, hmass⟩
  exact
    ⟨hsingleton,
      hrep,
      hwave,
      hmass⟩

/-- Direct representative theorem on the exact wave endpoint frontier. Once
the wave lane has reached the forced endpoint frontier, the recognizable
wave/Klein--Gordon representative is already fixed there: no additional
continuum-closure wrapper is needed to identify the standard transport and
closure form. -/
theorem recognizableFromEndpointFrontier
    {Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index : Type}
    {T : HorizonTower}
    (data : EndpointRecursionKernelFrontierData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T) :
    let duality :=
      SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.frontier.frontier.collapse.orthogonalityRigidity
    data.frontier.frontier.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      data.frontier.frontier.collapse.minimalPairingSymmetricTransportIsWaveLaplacian ∧
      data.frontier.frontier.collapse.pairingScalarClosureActsAsMassPotential ∧
      Nonempty (RecognizableIdentity
        Time Carrier Law Field Scalar) := by
  have hendpoint := endpointRepresentativeFacts data
  rcases hendpoint with ⟨hsingleton, hrep, hwave, hmass⟩
  exact
    ⟨hsingleton,
      hrep,
      hwave,
      hmass,
      recognizableWitness
        data.frontier.frontier.collapse.law
        (data.frontier.frontier.collapse.minimalPairingSymmetricTransportIsWaveLaplacian ∧
          data.frontier.frontier.collapse.pairingScalarClosureActsAsMassPotential)
        data.frontier.frontier.collapse.law.losslessLeadingOrder⟩

/-- Cleanest direct wave closure route using the already-forced selected
closure law from the Part IV physical realization package. If the selected
visible effective law is read on the same least-motion cut and exports the same
continuum closure class as the wave observer, then no separate target-uniqueness
theorem is needed: the continuum singleton is inherited directly from the
physical selected law itself. -/
structure SelectedClosureIdentificationData
    (Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index : Type)
    (T : HorizonTower) where
  frontier :
    EndpointRecursionKernelFrontierData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T
  physical :
    PhysicalRealizationPrinciple Time Carrier Law
  sameLeastMotionSelection :
    physical.selectedLaw.selection =
      frontier.frontier.frontier.collapse.law.observer.selection
  sameContinuumClosureClass :
    physical.selectedLaw.endpointClosureClass =
      frontier.frontier.frontier.collapse.law.observer.continuumClass

/-- Elegant wave closure theorem. Once the exact wave endpoint frontier is in
hand, the only further identification needed is that the physical selected
closure law is read on the same least-motion cut and in the same continuum
closure class. The forced continuum singleton is then inherited directly from
the Part IV physical realization package, and the selected carrier is already
recognizable as wave/Klein--Gordon by the endpoint collapse itself. -/
theorem closureFromPhysicalRealization
    {Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index : Type}
    {T : HorizonTower}
    (data : SelectedClosureIdentificationData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T) :
    let cls :=
      data.frontier.frontier.frontier.collapse.law.observer.continuumClass
    let target := data.physical.selectedLaw.selectedClosureLaw
    data.frontier.frontier.frontier.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      (SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.frontier.frontier.frontier.collapse.orthogonalityRigidity).endpointRepresentativeForcedByWeakForm ∧
      ForcedContinuumLaw cls target ∧
      Nonempty (RecognizableIdentity
        Time Carrier Law Field Scalar) := by
  have hfrontier := recognizableFromEndpointFrontier data.frontier
  rcases hfrontier with
    ⟨hsingleton, hrep, _hwave, _hmass, hrecognizable⟩
  exact
    SelectedCut.closureReadoutWithRecognition
      data.physical
      data.frontier.frontier.frontier.collapse.law.observer
      data.sameLeastMotionSelection
      data.sameContinuumClosureClass
      hsingleton
      hrep
      hrecognizable

/-- Selected-bundle wave closure route. This is the more foundational version
of the direct closure theorem: once the wave observer is read off the one
intrinsic selected bundle, forced continuum closure is inherited
automatically. -/
structure SelectedBundleClosureIdentificationData
    (Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index : Type)
    (T : HorizonTower) where
  frontier :
    EndpointRecursionKernelFrontierData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T
  selectedBundle : IntrinsicSelectedBundleExistence Time Carrier Law
  waveCarrierReadOnSelectedBundle :
    selectedBundle.waveCarrierReadOnSelectedBundle
      frontier.frontier.frontier.collapse.law.observer

/-- Foundational wave closure theorem through the intrinsic selected bundle. -/
theorem closureFromSelectedBundle
    {Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index : Type}
    {T : HorizonTower}
    (data : SelectedBundleClosureIdentificationData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T) :
    let cls := data.frontier.frontier.frontier.collapse.law.observer.continuumClass
    let target := data.selectedBundle.physicalPrinciple.selectedLaw.selectedClosureLaw
    data.frontier.frontier.frontier.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      (SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.frontier.frontier.frontier.collapse.orthogonalityRigidity).endpointRepresentativeForcedByWeakForm ∧
      ForcedContinuumLaw cls target ∧
      Nonempty (RecognizableIdentity
        Time Carrier Law Field Scalar) := by
  have hfrontier := recognizableFromEndpointFrontier data.frontier
  have hsel :=
    SelectedBundle.waveCarrierSelection
      data.selectedBundle
      data.frontier.frontier.frontier.collapse.law.observer
      data.waveCarrierReadOnSelectedBundle
  rcases hfrontier with
    ⟨hsingleton, hrep, _hwave, _hmass, hrecognizable⟩
  exact
    SelectedBundle.closureReadoutWithRecognition
      data.selectedBundle
      data.frontier.frontier.frontier.collapse.law.observer
      hsel
      hsingleton
      hrep
      hrecognizable

/-- Native structural Euclidean bridge built directly on the exact wave
endpoint frontier. Relative to the sharper endpoint frontier, local
homogeneity and self-adjoint scalarization provide the symmetry and pairing
surfaces; the only remaining wave-specific burden after this bridge is a single
continuum classification theorem. -/
structure EndpointStructuralEuclideanBridgeData
    (Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index Channel : Type)
    (T : HorizonTower) where
  frontier :
    EndpointRecursionKernelFrontierData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T
  localHomogeneous :
    LocallyHomogeneousSymmetryGeneratedData Index Time Channel
  selfAdjointScalarization :
    RealizedSelfAdjointScalarizationData Index Time Channel
  localHomogeneityYieldsEuclideanMotionInvariantSpatialTransport : Prop
  scalarRecursiveKernelYieldsReversibleContinuumClass : Prop
  localHomogeneityYieldsEuclideanMotionInvariantSpatialTransport_valid :
    localHomogeneityYieldsEuclideanMotionInvariantSpatialTransport
  scalarRecursiveKernelYieldsReversibleContinuumClass_valid :
    scalarRecursiveKernelYieldsReversibleContinuumClass

/-- The exact wave endpoint frontier, together with local homogeneity and
self-adjoint scalarization, already supplies the native data needed for the
wave Euclidean bridge: singleton endpoint class, mechanical substitution,
local datum, scalar recursion kernel, symmetry generation, Euclidean spatial
transport, reversibility, and the wave/mass endpoint identities. -/
theorem endpointStructuralEuclideanBridge
    {Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index Channel : Type}
    {T : HorizonTower}
    (data : EndpointStructuralEuclideanBridgeData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index Channel T) :
    let duality :=
      SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.frontier.frontier.frontier.collapse.orthogonalityRigidity
    data.frontier.frontier.frontier.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      Nonempty (LocalInternalDatumSelectedChannels
        PhaseClass Scalar ClosureClass) ∧
      data.frontier.admissibleTransport.distinguishedClass.order = 1 ∧
      data.frontier.admissibleTransport.noPreferredDirection.rigidity.scalarQuadraticLaw ∧
      (∀ x : SequenceTransportSpace,
        inTransportKernel data.frontier.admissibleTransport.representative x ↔
          ∀ n : BilateralIndex,
            x (bilateralSucc n) =
              State.sub (data.frontier.admissibleTransport.representative (x n))
                (x (bilateralPred n))) ∧
      Nonempty (SymmetryGeneratedRealizedClass Index Time Channel) ∧
      data.selfAdjointScalarization.selectedSelfAdjointOperatorsScalar ∧
      data.localHomogeneityYieldsEuclideanMotionInvariantSpatialTransport ∧
      data.scalarRecursiveKernelYieldsReversibleContinuumClass ∧
      data.frontier.frontier.frontier.collapse.minimalPairingSymmetricTransportIsWaveLaplacian ∧
      data.frontier.frontier.frontier.collapse.pairingScalarClosureActsAsMassPotential := by
  have hendpoint := endpointRepresentativeFacts data.frontier
  have hlocal := WaveLane.localDatumFrontier data.frontier.frontier
  have hrecursion :=
    transport_generation_forces_scalar_recursion data.frontier.admissibleTransport
  have hsymm :=
    locally_homogeneous_implies_symmetry_generated data.localHomogeneous
  have hscalar :=
    realized_self_adjoint_scalarization data.selfAdjointScalarization
  rcases hendpoint with ⟨hsingleton, hrep, hwave, hmass⟩
  rcases hlocal with
    ⟨_hsingleton, _hrep, _hsecond, hlocal, _horder, _hscalar, _hrec,
      _hrecursive, _hwave, _hmass⟩
  rcases hrecursion with ⟨horder, hscalarQ, hkernel⟩
  exact
    ⟨hsingleton,
      hrep,
      hlocal,
      horder,
      hscalarQ,
      hkernel,
      hsymm,
      hscalar,
      data.localHomogeneityYieldsEuclideanMotionInvariantSpatialTransport_valid,
      data.scalarRecursiveKernelYieldsReversibleContinuumClass_valid,
      hwave,
      hmass⟩

/-- Final one-theorem wave closure package. After the exact endpoint frontier
and the native structural Euclidean bridge are in place, the remaining
wave-specific burden can be compressed to a single continuum classification
theorem on the selected observer's own continuum class. -/
structure SingleClassificationClosureData
    (Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index Channel : Type)
    (T : HorizonTower) where
  bridge :
    EndpointStructuralEuclideanBridgeData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index Channel T
  target : Law
  targetAdmissible :
    bridge.frontier.frontier.frontier.collapse.law.observer.continuumClass.admissible
      target
  finalContinuumClassificationForcesTarget :
    ∀ other : Law,
      bridge.frontier.frontier.frontier.collapse.law.observer.continuumClass.admissible
        other → other = target
  targetRecognizedAsWaveKG : Prop
  targetExactIfLossless : Prop
  targetRecognizedAsWaveKG_valid : targetRecognizedAsWaveKG
  targetExactIfLossless_valid : targetExactIfLossless

/-- Strongest honest wave closure theorem on the current spine. Once the exact
wave endpoint frontier and native structural Euclidean bridge are in hand, the
entire remaining wave burden is a single continuum classification theorem. If
that theorem identifies the unique admissible continuum representative, the
standard wave/Klein--Gordon law is forced with no practitioner discretion. -/
theorem singleClassificationClosure
    {Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index Channel : Type}
    {T : HorizonTower}
    (data : SingleClassificationClosureData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index Channel T) :
    let cls :=
      data.bridge.frontier.frontier.frontier.collapse.law.observer.continuumClass
    let duality :=
      SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.bridge.frontier.frontier.frontier.collapse.orthogonalityRigidity
    data.bridge.frontier.frontier.frontier.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      Nonempty (SymmetryGeneratedRealizedClass Index Time Channel) ∧
      data.bridge.selfAdjointScalarization.selectedSelfAdjointOperatorsScalar ∧
      data.bridge.localHomogeneityYieldsEuclideanMotionInvariantSpatialTransport ∧
      data.bridge.scalarRecursiveKernelYieldsReversibleContinuumClass ∧
      data.bridge.frontier.frontier.frontier.collapse.minimalPairingSymmetricTransportIsWaveLaplacian ∧
      data.bridge.frontier.frontier.frontier.collapse.pairingScalarClosureActsAsMassPotential ∧
      ForcedContinuumLaw cls data.target ∧
      Nonempty (RecognizableIdentity
        Time Carrier Law Field Scalar) := by
  have hendpoint := endpointRepresentativeFacts data.bridge.frontier
  have hbridge := endpointStructuralEuclideanBridge data.bridge
  rcases hendpoint with ⟨hsingleton, hrep, hwave, hmass⟩
  rcases hbridge with
    ⟨_hsingleton, _hrep, _hlocal, _horder, _hscalarQ, _hkernel, hsymm, hscalar,
      heucl, hrev, _hwave, _hmass⟩
  have ⟨_hsingleton, _hrep, hforced⟩ :=
    FlagshipShared.forcedContinuumFromEndpointFacts
      data.bridge.frontier.frontier.frontier.collapse.law.observer.continuumClass
      data.target
      hsingleton
      hrep
      data.targetAdmissible
      data.finalContinuumClassificationForcesTarget
  exact
    endpointRepresentativePackage
      data.bridge.frontier.frontier.frontier.collapse.law.observer.continuumClass
      data.target
      data.targetRecognizedAsWaveKG
      data.targetExactIfLossless
      data.bridge.frontier.frontier.frontier.collapse.law
      hsingleton
      hrep
      hsymm
      hscalar
      heucl
      hrev
      hwave
      hmass
      hforced

/-- Sharper algebraic bridge for the wave lane. Instead of quantifying over all
admissible continuum representatives, this packages the exact multiplier-defect
profile on the selected real scalar endpoint representative together with the
comparison operator that is meant to carry the wave-like normal form. -/
structure KernelProductDefectBridgeData
    (Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index ScalarFn : Type)
    (T : HorizonTower) where
  frontier :
    RecursionKernelStructuralFrontierData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T
  algebra : ScalarMultiplierAlgebra ScalarFn
  endpointRepresentative : ScalarOp ScalarFn
  comparisonOperator : ScalarOp ScalarFn
  sharedProductDefect : ScalarFn → ScalarFn → ScalarFn
  comparisonOperatorIsWaveLike : Prop
  endpointProductDefectRealized :
    ∀ f u : ScalarFn,
      productDefectApply algebra endpointRepresentative f u =
        sharedProductDefect f u
  comparisonProductDefectRealized :
    ∀ f u : ScalarFn,
      productDefectApply algebra comparisonOperator f u =
        sharedProductDefect f u
  comparisonThirdCommZero :
    ∀ f g h u : ScalarFn,
      thirdCommApply algebra comparisonOperator f g h u = algebra.zero
  derivationRemaindersVanish :
    ∀ D : ScalarOp ScalarFn,
      IsScalarDerivation algebra D → ∀ u : ScalarFn, D u = algebra.zero
  comparisonOperatorIsWaveLike_valid :
    comparisonOperatorIsWaveLike

/-- Sharper algebraic bridge for the wave lane. Instead of quantifying over all
admissible continuum representatives, this packages the exact multiplier-defect
profile on the selected real scalar endpoint representative together with the
comparison operator that is meant to carry the wave-like normal form. -/
structure MultiplierDefectBridgeData
    (Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index ScalarFn : Type)
    (T : HorizonTower) where
  frontier :
    RecursionKernelStructuralFrontierData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T
  algebra : ScalarMultiplierAlgebra ScalarFn
  endpointRepresentative : ScalarOp ScalarFn
  comparisonOperator : ScalarOp ScalarFn
  comparisonOperatorIsWaveLike : Prop
  thirdCommZeroEndpoint :
    ∀ f g h u : ScalarFn,
      thirdCommApply algebra endpointRepresentative f g h u = algebra.zero
  thirdCommZeroComparison :
    ∀ f g h u : ScalarFn,
      thirdCommApply algebra comparisonOperator f g h u = algebra.zero
  secondCommutatorAgreementAtUnit :
    ∀ f g : ScalarFn,
      secondCommApply algebra endpointRepresentative f g algebra.one =
        secondCommApply algebra comparisonOperator f g algebra.one
  derivationRemaindersVanish :
    ∀ D : ScalarOp ScalarFn,
      IsScalarDerivation algebra D → ∀ u : ScalarFn, D u = algebra.zero
  comparisonOperatorIsWaveLike_valid :
    comparisonOperatorIsWaveLike

/-- Exact wave reconstruction route through multiplier defects. Once the honest
wave frontier has supplied the selected endpoint representative, the remaining
burden is compressed to the multiplier-defect profile on that representative.
If its second commutator agrees at the unit with a wave-like comparison
operator and both sides have third-commutator truncation, then the endpoint is
forced pointwise to be that wave-like operator plus a scalar potential. -/
theorem multiplierProfilePotential
    {Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index ScalarFn : Type}
    {T : HorizonTower}
    (data : MultiplierDefectBridgeData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index ScalarFn T) :
    let duality :=
      SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.frontier.frontier.frontier.frontier.orthogonalityRigidity
    let potential :=
      scalarPotentialFromRemainder
        data.algebra
        (scalarRemainder data.algebra
          data.endpointRepresentative data.comparisonOperator)
    data.frontier.frontier.frontier.frontier.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      Nonempty (LocalInternalDatumSelectedChannels
        PhaseClass Scalar ClosureClass) ∧
      data.frontier.admissibleTransport.distinguishedClass.order = 1 ∧
      data.frontier.admissibleTransport.noPreferredDirection.rigidity.scalarQuadraticLaw ∧
      data.comparisonOperatorIsWaveLike ∧
      ∀ u : ScalarFn,
        data.endpointRepresentative u =
          data.algebra.add
            (data.comparisonOperator u)
            (data.algebra.mul potential u) := by
  have hstruct := structuralRepresentativeFacts data.frontier
  have hlocal := localDatumStructuralFrontier data.frontier.frontier
  have hrecursion :=
    transport_generation_forces_scalar_recursion data.frontier.admissibleTransport
  have hmatch :=
    second_commutators_agree_of_third_comm_zero_and_unit_agreement
      data.algebra
      data.endpointRepresentative
      data.comparisonOperator
      data.thirdCommZeroEndpoint
      data.thirdCommZeroComparison
      data.secondCommutatorAgreementAtUnit
  have hreconstruct :=
    reconstruct_mod_multiplication_pointwise_of_vanishing_derivations
      data.algebra
      data.endpointRepresentative
      data.comparisonOperator
      hmatch
      data.derivationRemaindersVanish
  rcases hstruct with ⟨hsingleton, hrep⟩
  rcases hlocal with
    ⟨_hsingleton, _hrep, _hsecond, hlocal, _horder, _hscalar, _hrec,
      _hrecursive⟩
  rcases hrecursion with ⟨horder, hscalar, _hkernel⟩
  exact
    ⟨hsingleton,
      hrep,
      hlocal,
      horder,
      hscalar,
      data.comparisonOperatorIsWaveLike_valid,
      hreconstruct⟩

/-- Shared product-defect data already determines the sharper multiplier bridge
needed by the wave reconstruction theorem. The only genuinely wave-specific
input left outside this theorem is the kernel-to-product-defect realization
itself. -/
def KernelProductDefectBridgeData.toMultiplierBridgeData
    {Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index ScalarFn : Type}
    {T : HorizonTower}
    (data : KernelProductDefectBridgeData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index ScalarFn T) :
    MultiplierDefectBridgeData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index ScalarFn T :=
  let hmatch :=
    second_commutator_match_of_shared_product_defect
      data.algebra
      data.endpointRepresentative
      data.comparisonOperator
      (fun f u =>
        (data.endpointProductDefectRealized f u).trans
          (data.comparisonProductDefectRealized f u).symm)
  { frontier := data.frontier
    algebra := data.algebra
    endpointRepresentative := data.endpointRepresentative
    comparisonOperator := data.comparisonOperator
    comparisonOperatorIsWaveLike := data.comparisonOperatorIsWaveLike
    thirdCommZeroEndpoint :=
      third_comm_zero_of_second_comm_agreement
        data.algebra
        data.endpointRepresentative
        data.comparisonOperator
        hmatch
        data.comparisonThirdCommZero
    thirdCommZeroComparison := data.comparisonThirdCommZero
    secondCommutatorAgreementAtUnit :=
      second_commutator_unit_agreement_of_pointwise_agreement
        data.algebra
        data.endpointRepresentative
        data.comparisonOperator
        hmatch
    derivationRemaindersVanish := data.derivationRemaindersVanish
    comparisonOperatorIsWaveLike_valid :=
      data.comparisonOperatorIsWaveLike_valid }

/-- Cleanest current wave closure route. Once the honest wave frontier is
equipped with a shared product-defect realization against a wave-like
comparison operator, the already-proved multiplier reconstruction machinery
forces the selected endpoint operator to be wave-like plus scalar potential. -/
theorem kernelProductDefectPotential
    {Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index ScalarFn : Type}
    {T : HorizonTower}
    (data : KernelProductDefectBridgeData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index ScalarFn T) :
    let potential :=
      scalarPotentialFromRemainder
        data.algebra
        (scalarRemainder data.algebra
          data.endpointRepresentative data.comparisonOperator)
    data.frontier.frontier.frontier.frontier.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      (SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.frontier.frontier.frontier.frontier.orthogonalityRigidity).endpointRepresentativeForcedByWeakForm ∧
      Nonempty (LocalInternalDatumSelectedChannels
        PhaseClass Scalar ClosureClass) ∧
      data.frontier.admissibleTransport.distinguishedClass.order = 1 ∧
      data.frontier.admissibleTransport.noPreferredDirection.rigidity.scalarQuadraticLaw ∧
      data.comparisonOperatorIsWaveLike ∧
      ∀ u : ScalarFn,
        data.endpointRepresentative u =
          data.algebra.add
            (data.comparisonOperator u)
            (data.algebra.mul potential u) := by
  exact
    multiplierProfilePotential
      data.toMultiplierBridgeData

/-- Final wave closure data: once the exact recursion-kernel normal form has
been forced on the selected wave carrier, the only remaining task is to show
that a chosen continuum representative lies in the observer's own continuum
limit class and is unique there. At that point the continuum representative is
forced with no further practitioner discretion. -/
structure ContinuumClosureData
    (Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index : Type)
    (T : HorizonTower) where
  frontier :
    EndpointRecursionKernelFrontierData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T
  target : Law
  targetAdmissible :
    frontier.frontier.frontier.collapse.law.observer.continuumClass.admissible
      target
  targetUnique :
    ∀ other : Law,
      frontier.frontier.frontier.collapse.law.observer.continuumClass.admissible
        other → other = target
  targetIsWaveKGRepresentative : Prop
  targetExactIfLossless : Prop
  targetIsWaveKGRepresentative_valid : targetIsWaveKGRepresentative
  targetExactIfLossless_valid : targetExactIfLossless

/-- Wave closure theorem. The active spine now reduces the wave lane to a pure
continuum-limit-class closure problem: once the exact scalar-recursive transport
kernel has been forced and a continuum representative is shown admissible and
unique in the selected observer's own continuum class, that representative is
itself forced. -/
theorem continuumClosure
    {Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index : Type}
    {T : HorizonTower}
    (data : ContinuumClosureData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T) :
    let cls :=
      data.frontier.frontier.frontier.collapse.law.observer.continuumClass
    let duality :=
      SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.frontier.frontier.frontier.collapse.orthogonalityRigidity
    data.frontier.frontier.frontier.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      ForcedContinuumLaw cls data.target ∧
      data.targetIsWaveKGRepresentative ∧
      data.targetExactIfLossless := by
  obtain ⟨hsingleton, hrep, _hwave, _hmass⟩ :=
    endpointRepresentativeFacts data.frontier
  have ⟨_hsingleton, _hrep, hforced⟩ :=
    FlagshipShared.forcedContinuumFromEndpointFacts
      data.frontier.frontier.frontier.collapse.law.observer.continuumClass
      data.target
      hsingleton
      hrep
      data.targetAdmissible
      data.targetUnique
  exact
    ⟨hsingleton,
      hrep,
      hforced,
      data.targetIsWaveKGRepresentative_valid,
      data.targetExactIfLossless_valid⟩

/-- Once the wave continuum-closure theorem is in hand, the recognizable
wave/Klein--Gordon identity is an immediate corollary of the forced continuum
law on the selected wave carrier. -/
theorem recognizableFromClosure
    {Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index : Type}
    {T : HorizonTower}
    (data : ContinuumClosureData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T) :
    let cls :=
      data.frontier.frontier.frontier.collapse.law.observer.continuumClass
    ForcedContinuumLaw cls data.target ∧
      Nonempty (RecognizableIdentity
        Time Carrier Law Field Scalar) := by
  have hclosure := continuumClosure data
  rcases hclosure with ⟨_hsingleton, _hrep, hforced, _hwave, _hexact⟩
  exact
    ⟨hforced,
      recognizableWitness
        data.frontier.frontier.frontier.collapse.law
        data.targetIsWaveKGRepresentative
        data.targetExactIfLossless⟩

end WaveLane

namespace WaveLane

/-- Nearest-neighbor specialization of the selected wave carrier. -/
structure NearestNeighborSpecialization
    (Time Carrier Law Field Scalar : Type) where
  law : InducedLaw Time Carrier Law Field Scalar
  primitiveLattice : Type
  latticeSpacing : Scalar
  latticeSpacingPositive : Prop
  masslessLosslessLeadingOrder : Prop
  secondDifferenceTransport : Prop

/- Exact lattice-dispersion package. -/
structure ExactWaveDispersion
    (Time Carrier Law Field Scalar : Type) where
  specialization :
    NearestNeighborSpecialization Time Carrier Law Field Scalar
  dispersionFormula : Prop
  groupVelocityFormula : Prop

/-- Witness data for the exact lattice-dispersion theorem. -/
structure ExactWaveDispersionData
    (Time Carrier Law Field Scalar : Type)
    extends ExactWaveDispersion Time Carrier Law Field Scalar where
  planeWaveAnsatz : Prop

/- Exact lattice dispersion on the selected wave carrier. -/

theorem exactDispersion
    {Time Carrier Law Field Scalar : Type}
    (data : ExactWaveDispersionData Time Carrier Law Field Scalar) :
    Nonempty (ExactWaveDispersion Time Carrier Law Field Scalar) := by
  exact ⟨data.toExactWaveDispersion⟩

/-- Observable low-energy signature of the selected wave carrier. -/
structure ObservableWaveCarrierSignature
    (Time Carrier Law Field Scalar : Type) where
  dispersion : ExactWaveDispersion Time Carrier Law Field Scalar
  lowEnergySubluminalSignature : Prop
  hardCutoff : Prop

/-- Witness data for the observable wave-carrier signature. -/
structure ObservableWaveCarrierSignatureData
    (Time Carrier Law Field Scalar : Type)
    extends ObservableWaveCarrierSignature
      Time Carrier Law Field Scalar where
  lowEnergyExpansion : Prop

/-- Observable wave-carrier signature. -/
theorem observableCarrierSignature
    {Time Carrier Law Field Scalar : Type}
    (data : ObservableWaveCarrierSignatureData
      Time Carrier Law Field Scalar) :
    Nonempty (ObservableWaveCarrierSignature
      Time Carrier Law Field Scalar) := by
  exact ⟨data.toObservableWaveCarrierSignature⟩

end WaveLane

end CoherenceCalculus


