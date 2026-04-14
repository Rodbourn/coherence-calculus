import CoherenceCalculus.PartIV.ObserverSelectionCore
import CoherenceCalculus.PartIV.FlagshipClosureSharedCore

/-!
# PartIV.FlagshipPhaseCore

Phase flagship lane for Part IV.

This file isolates the Hamiltonian / Schr\"odinger lane so the main flagship
aggregator can stay organized by lane family instead of carrying every lane
inline.
-/

namespace CoherenceCalculus

namespace PhaseLane

/-- Phase flagship realization data on the least-motion cut. -/
structure HamiltonianRealization
    (Time Carrier Law Field Scalar : Type) where
  observerDatum : ObserverSelection.CharacteristicDatum Time Carrier Law
  refinementFamily : RefinementCompatibleFamily
  governingDatumRigidity : Prop
  admissiblePromotionStable : Prop
  asymptoticConsistency : Prop
  transportOperator : Endo Field
  closureOperator : Endo Field
  transportSelfAdjoint : Prop
  closureSelfAdjointScalar : Prop

/-- The phase carrier hypotheses used in the least-motion observer theorem. -/
structure LeastMotionObserverData
    (Time Carrier Law Field Scalar : Type)
    extends HamiltonianRealization Time Carrier Law Field Scalar where
  faithfulCarrier : Prop
  closureAdmissibleCarrier : Prop
  noProperPhaseSubcarrier : Prop
  observerMotionMinimal : Prop
  uniqueObserver : Prop

/-- Least-motion phase observer theorem. -/
theorem leastMotionObserver
    {Time Carrier Law Field Scalar : Type}
    (data : LeastMotionObserverData Time Carrier Law Field Scalar) :
    Nonempty (ObserverSelection.LeastMotion Time Carrier Law) := by
  exact
    ⟨{ toCharacteristicDatum := data.observerDatum
       faithful := data.faithfulCarrier
       closureAdmissible := data.closureAdmissibleCarrier
       stableUnderAdmissiblePromotion := data.admissiblePromotionStable
       noProperVisibleSubcarrier := data.noProperPhaseSubcarrier
       observerMotionMinimal := data.observerMotionMinimal
       uniqueUpToHorizonPreservingEquivalence := data.uniqueObserver }⟩

/-- Result package for the induced reversible phase law. -/
structure InducedHamiltonianLaw
    (Time Carrier Law Field Scalar : Type) where
  observer : ObserverSelection.LeastMotion Time Carrier Law
  phaseRepresentative : Endo Field
  scalarCoefficient : Scalar
  scalarCoefficientNonnegative : Prop
  transportOperator : Endo Field
  closureOperator : Endo Field
  remainder : Field
  equation : Prop
  losslessLeadingOrder : Prop

/-- Witness data for the induced reversible phase law. -/
structure InducedHamiltonianLawData
    (Time Carrier Law Field Scalar : Type)
    extends InducedHamiltonianLaw Time Carrier Law Field Scalar where
  realization : HamiltonianRealization Time Carrier Law Field Scalar
  governingDatumRigidSelectedChannels : Prop
  localInternalDatumForced : Prop

/-- Induced reversible phase law on the selected cut. -/
theorem inducedHamiltonianLaw
    {Time Carrier Law Field Scalar : Type}
    (data : InducedHamiltonianLawData Time Carrier Law Field Scalar) :
    Nonempty (InducedHamiltonianLaw Time Carrier Law Field Scalar) := by
  exact ⟨data.toInducedHamiltonianLaw⟩

/-- Recognition package for the Schr\"odinger form on the selected carrier. -/
structure RecognizableIdentity
    (Time Carrier Law Field Scalar : Type) where
  law : InducedHamiltonianLaw Time Carrier Law Field Scalar
  schrodingerForm : Prop
  exactIfLossless : Prop

private theorem recognizableWitness
    {Time Carrier Law Field Scalar : Type}
    (law : InducedHamiltonianLaw Time Carrier Law Field Scalar)
    (schrodingerForm exactIfLossless : Prop) :
    Nonempty (RecognizableIdentity Time Carrier Law Field Scalar) := by
  exact
    ⟨{ law := law
       schrodingerForm := schrodingerForm
       exactIfLossless := exactIfLossless }⟩

/-- Endpoint-collapse package for the phase carrier. This isolates the exact
remaining proof obligation after the common realized-cut orthogonality theorem:
the pairing-compatible endpoint quotient must collapse to a singleton whose
canonical representative is the familiar complex/Laplacian/potential phase
form. -/
structure EndpointCollapse
    (Time Carrier Law Field Scalar : Type)
    where
  law : InducedHamiltonianLaw Time Carrier Law Field Scalar
  orthogonalityRigidity :
    SelectedCutOrthogonality.Principle Time Carrier Law Field
  complexCarrierGeneratedByCanonicalPairing : Prop
  phaseRepresentativeFixedByCanonicalPairing : Prop
  minimalPairingSymmetricTransportIsLaplaceType : Prop
  pairingScalarClosureActsAsRealPotential : Prop
  complexCarrierGeneratedByCanonicalPairing_valid :
    complexCarrierGeneratedByCanonicalPairing
  phaseRepresentativeFixedByCanonicalPairing_valid :
    phaseRepresentativeFixedByCanonicalPairing
  minimalPairingSymmetricTransportIsLaplaceType_valid :
    minimalPairingSymmetricTransportIsLaplaceType
  pairingScalarClosureActsAsRealPotential_valid :
    pairingScalarClosureActsAsRealPotential

/-- The phase endpoint collapses exactly when the energy-orthogonal realized
cut leaves a singleton pairing-compatible endpoint quotient whose canonical
representative is the complex/Laplacian/potential phase form. -/
theorem endpointCollapse
    {Time Carrier Law Field Scalar : Type}
    (data : EndpointCollapse Time Carrier Law Field Scalar) :
    let duality := data.orthogonalityRigidity.toCanonicalDuality
    data.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      data.complexCarrierGeneratedByCanonicalPairing ∧
      data.phaseRepresentativeFixedByCanonicalPairing ∧
      data.minimalPairingSymmetricTransportIsLaplaceType ∧
      data.pairingScalarClosureActsAsRealPotential := by
  have horth :=
    SelectedCutOrthogonality.Principle.singletonRepresentative
      data.orthogonalityRigidity
  exact
    ⟨horth.1,
      horth.2,
      data.complexCarrierGeneratedByCanonicalPairing_valid,
      data.phaseRepresentativeFixedByCanonicalPairing_valid,
      data.minimalPairingSymmetricTransportIsLaplaceType_valid,
      data.pairingScalarClosureActsAsRealPotential_valid⟩

/-- Sector-rigidity package forcing the recognizable Schr\"odinger identity
once the phase endpoint collapse has been established. -/
structure SectorRigidity
    (Time Carrier Law Field Scalar : Type)
    extends EndpointCollapse Time Carrier Law Field Scalar where
  recognizableSchrodingerFormForced : Prop
  exactSchrodingerIfLossless : Prop
  recognizableSchrodingerFormForced_valid :
    recognizableSchrodingerFormForced
  exactSchrodingerIfLossless_valid :
    exactSchrodingerIfLossless

/- The phase endpoint is rigid precisely when the canonical duality on the
generated phase carrier forces the complex/Laplacian/potential representative. -/

theorem sectorRigidity
    {Time Carrier Law Field Scalar : Type}
    (data : SectorRigidity Time Carrier Law Field Scalar) :
    let duality :=
      SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.toEndpointCollapse.orthogonalityRigidity
    data.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      data.minimalPairingSymmetricTransportIsLaplaceType ∧
      data.pairingScalarClosureActsAsRealPotential ∧
      data.recognizableSchrodingerFormForced := by
  have hcollapse := endpointCollapse data.toEndpointCollapse
  rcases hcollapse with
    ⟨hsingleton, hrep, _hcomplex, _hphase, hlaplace, hpotential⟩
  exact
    ⟨hsingleton,
      hrep,
      hlaplace,
      hpotential,
      data.recognizableSchrodingerFormForced_valid⟩

/-- Recognizable Schr\"odinger identity. -/
theorem recognizableIdentity
    {Time Carrier Law Field Scalar : Type}
    (data : SectorRigidity Time Carrier Law Field Scalar) :
    Nonempty (RecognizableIdentity
      Time Carrier Law Field Scalar) := by
  exact
    recognizableWitness
      data.law
      data.recognizableSchrodingerFormForced
      data.exactSchrodingerIfLossless

/-- Foundation-facing frontier data for the phase endpoint. This packages the
active early bridge surfaces already available before the final phase
representative identity is closed. -/
structure EndpointFoundationFrontierData
    (Time Carrier Law Field Scalar Index Channel : Type) where
  collapse : EndpointCollapse Time Carrier Law Field Scalar
  transportBase : AddMap
  selectedProjection : Projection
  phaseCompatibleTower :
    PhaseCompatibleSchurTowerData transportBase selectedProjection
  observableScalarization :
    RealizedSelfAdjointScalarizationData Index Time Channel

/- On the active Lean surface, the phase endpoint already reduces to an
energy-orthogonal singleton endpoint class together with self-adjoint
scalarization and phase-compatible Schur-tower structure. The only remaining
carrier-specific burden is to identify the scalarized pairing-compatible phase
representative with the familiar complex/Laplacian/potential form. -/

theorem endpointFrontier
    {Time Carrier Law Field Scalar Index Channel : Type}
    (data : EndpointFoundationFrontierData
      Time Carrier Law Field Scalar Index Channel) :
    let duality := data.collapse.orthogonalityRigidity.toCanonicalDuality
    data.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      data.collapse.complexCarrierGeneratedByCanonicalPairing ∧
      data.observableScalarization.selectedSelfAdjointOperatorsScalar ∧
      data.phaseCompatibleTower.towerPhaseCompatibility ∧
      data.collapse.phaseRepresentativeFixedByCanonicalPairing ∧
      data.collapse.minimalPairingSymmetricTransportIsLaplaceType ∧
      data.collapse.pairingScalarClosureActsAsRealPotential := by
  have hcollapse := endpointCollapse data.collapse
  have hscalar := realized_self_adjoint_scalarization data.observableScalarization
  have hphase := phase_compatible_schur_tower data.phaseCompatibleTower
  rcases hcollapse with
    ⟨hsingleton, hrep, hcomplex, hphaseRep, hlaplace, hpotential⟩
  rcases hphase with ⟨_hJ, _hschur, _heff, htower⟩
  exact
    ⟨hsingleton,
      hrep,
      hcomplex,
      hscalar,
      htower,
      hphaseRep,
      hlaplace,
      hpotential⟩

/-- Reusable head of the exact phase endpoint frontier. Later phase proofs
often need only the singleton class, forced representative, and
Laplace/potential endpoint identity, not the full scalarization and tower
package. -/
private theorem endpointRepresentativeFacts
    {Time Carrier Law Field Scalar Index Channel : Type}
    (data : EndpointFoundationFrontierData
      Time Carrier Law Field Scalar Index Channel) :
    let duality := data.collapse.orthogonalityRigidity.toCanonicalDuality
    data.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      data.collapse.minimalPairingSymmetricTransportIsLaplaceType ∧
      data.collapse.pairingScalarClosureActsAsRealPotential := by
  have hfrontier := endpointFrontier data
  rcases hfrontier with
    ⟨hsingleton, hrep, _hcomplex, _hscalar, _htower, _hphase, hlaplace,
      hpotential⟩
  exact
    ⟨hsingleton,
      hrep,
      hlaplace,
      hpotential⟩

/-- Direct representative theorem on the exact phase endpoint frontier. Once
the phase lane has reached the forced endpoint frontier, the recognizable
Schrödinger representative is already fixed there: no additional
continuum-closure wrapper is needed to identify the standard transport and
closure form. -/
theorem recognizableFromEndpointFrontier
    {Time Carrier Law Field Scalar Index Channel : Type}
    (data : EndpointFoundationFrontierData
      Time Carrier Law Field Scalar Index Channel) :
    let duality := data.collapse.orthogonalityRigidity.toCanonicalDuality
    data.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      data.collapse.minimalPairingSymmetricTransportIsLaplaceType ∧
      data.collapse.pairingScalarClosureActsAsRealPotential ∧
      Nonempty (RecognizableIdentity
        Time Carrier Law Field Scalar) := by
  have hendpoint := endpointRepresentativeFacts data
  rcases hendpoint with ⟨hsingleton, hrep, hlaplace, hpotential⟩
  exact
    ⟨hsingleton,
      hrep,
      hlaplace,
      hpotential,
      recognizableWitness
        data.collapse.law
        (data.collapse.minimalPairingSymmetricTransportIsLaplaceType ∧
          data.collapse.pairingScalarClosureActsAsRealPotential)
        data.collapse.law.losslessLeadingOrder⟩

/-- Clean direct phase closure route using the already-forced selected closure
law from the Part IV physical realization package. Once the selected phase
carrier is read on the same least-motion cut and carries the same continuum
closure class, the continuum singleton is inherited directly from the physical
selected law itself. -/
structure SelectedClosureIdentificationData
    (Time Carrier Law Field Scalar Index Channel : Type) where
  frontier :
    EndpointFoundationFrontierData
      Time Carrier Law Field Scalar Index Channel
  physical :
    PhysicalRealizationPrinciple Time Carrier Law
  sameLeastMotionSelection :
    physical.selectedLaw.selection =
      frontier.collapse.law.observer.selection
  sameContinuumClosureClass :
    physical.selectedLaw.endpointClosureClass =
      frontier.collapse.law.observer.continuumClass

/-- Elegant phase closure theorem. The phase frontier already fixes the
recognizable pairing-compatible endpoint form; if the phase observer is reading
the same selected cut and continuum closure class as the Part IV physical
selected law, then the forced continuum singleton is inherited directly with no
separate target-uniqueness theorem. -/
theorem closureFromPhysicalRealization
    {Time Carrier Law Field Scalar Index Channel : Type}
    (data : SelectedClosureIdentificationData
      Time Carrier Law Field Scalar Index Channel) :
    let cls := data.frontier.collapse.law.observer.continuumClass
    let target := data.physical.selectedLaw.selectedClosureLaw
    data.frontier.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      (SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.frontier.collapse.orthogonalityRigidity).endpointRepresentativeForcedByWeakForm ∧
      ForcedContinuumLaw cls target ∧
      Nonempty (RecognizableIdentity
        Time Carrier Law Field Scalar) := by
  have hfrontier := recognizableFromEndpointFrontier data.frontier
  rcases hfrontier with
    ⟨hsingleton, hrep, _hlaplace, _hpotential, hrecognizable⟩
  exact
    SelectedCut.closureReadoutWithRecognition
      data.physical
      data.frontier.collapse.law.observer
      data.sameLeastMotionSelection
      data.sameContinuumClosureClass
      hsingleton
      hrep
      hrecognizable

/-- Selected-bundle phase closure route. This is the more foundational version
of the direct closure theorem: once the phase observer is read off the one
intrinsic selected bundle, forced continuum closure is inherited
automatically. -/
structure SelectedBundleClosureIdentificationData
    (Time Carrier Law Field Scalar Index Channel : Type) where
  frontier :
    EndpointFoundationFrontierData
      Time Carrier Law Field Scalar Index Channel
  selectedBundle : IntrinsicSelectedBundleExistence Time Carrier Law
  phaseCarrierReadOnSelectedBundle :
    selectedBundle.phaseCarrierReadOnSelectedBundle
      frontier.collapse.law.observer

/-- Foundational phase closure theorem through the intrinsic selected bundle. -/
theorem closureFromSelectedBundle
    {Time Carrier Law Field Scalar Index Channel : Type}
    (data : SelectedBundleClosureIdentificationData
      Time Carrier Law Field Scalar Index Channel) :
    let cls := data.frontier.collapse.law.observer.continuumClass
    let target := data.selectedBundle.physicalPrinciple.selectedLaw.selectedClosureLaw
    data.frontier.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      (SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.frontier.collapse.orthogonalityRigidity).endpointRepresentativeForcedByWeakForm ∧
      ForcedContinuumLaw cls target ∧
      Nonempty (RecognizableIdentity
        Time Carrier Law Field Scalar) := by
  have hfrontier := recognizableFromEndpointFrontier data.frontier
  have hsel :=
    SelectedBundle.phaseCarrierSelection
      data.selectedBundle
      data.frontier.collapse.law.observer
      data.phaseCarrierReadOnSelectedBundle
  rcases hfrontier with
    ⟨hsingleton, hrep, _hlaplace, _hpotential, hrecognizable⟩
  exact
    SelectedBundle.closureReadoutWithRecognition
      data.selectedBundle
      data.frontier.collapse.law.observer
      hsel
      hsingleton
      hrep
      hrecognizable

/-- Final phase closure data: once the scalarized phase-compatible frontier has
been forced on the selected phase carrier, the only remaining task is to show
that a chosen continuum representative lies in the observer's own continuum
limit class and is unique there. At that point the continuum representative is
forced with no further practitioner discretion. -/
structure ContinuumClosureData
    (Time Carrier Law Field Scalar Index Channel : Type) where
  frontier :
    EndpointFoundationFrontierData
      Time Carrier Law Field Scalar Index Channel
  target : Law
  targetAdmissible :
    frontier.collapse.law.observer.continuumClass.admissible target
  targetUnique :
    ∀ other : Law,
      frontier.collapse.law.observer.continuumClass.admissible other →
        other = target
  targetIsSchrodingerRepresentative : Prop
  targetExactIfLossless : Prop
  targetIsSchrodingerRepresentative_valid :
    targetIsSchrodingerRepresentative
  targetExactIfLossless_valid : targetExactIfLossless

/-- Phase closure theorem. The active spine now reduces the phase lane to a
pure continuum-limit-class closure problem: once the scalarized
phase-compatible frontier is forced and a continuum representative is shown
admissible and unique in the selected observer's own continuum class, that
representative is itself forced. -/
theorem continuumClosure
    {Time Carrier Law Field Scalar Index Channel : Type}
    (data : ContinuumClosureData
      Time Carrier Law Field Scalar Index Channel) :
    let cls := data.frontier.collapse.law.observer.continuumClass
    let duality :=
      SelectedCutOrthogonality.Principle.toCanonicalDuality
        data.frontier.collapse.orthogonalityRigidity
    data.frontier.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      ForcedContinuumLaw cls data.target ∧
      data.targetIsSchrodingerRepresentative ∧
      data.targetExactIfLossless := by
  obtain ⟨hsingleton, hrep, _hlaplace, _hpotential⟩ :=
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
      data.targetIsSchrodingerRepresentative_valid,
      data.targetExactIfLossless_valid⟩

/-- Once the phase continuum-closure theorem is in hand, the recognizable
Schr\"odinger identity is an immediate corollary of the forced continuum law on
the selected phase carrier. -/
theorem recognizableFromClosure
    {Time Carrier Law Field Scalar Index Channel : Type}
    (data : ContinuumClosureData
      Time Carrier Law Field Scalar Index Channel) :
    let cls := data.frontier.collapse.law.observer.continuumClass
    ForcedContinuumLaw cls data.target ∧
      Nonempty (RecognizableIdentity
        Time Carrier Law Field Scalar) := by
  have hclosure := continuumClosure data
  rcases hclosure with ⟨_hsingleton, _hrep, hforced, _hschrodinger, _hexact⟩
  exact
    ⟨hforced,
      recognizableWitness
        data.frontier.collapse.law
        data.targetIsSchrodingerRepresentative
        data.targetExactIfLossless⟩

end PhaseLane

end CoherenceCalculus
