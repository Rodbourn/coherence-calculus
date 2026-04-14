import CoherenceCalculus.Foundation.ProjectionCalculusCore

/-!
# Foundation.ComplexCompatibilityInterfaceCore

Structural interfaces for the compatible complex-structure section of Chapter 5.

These declarations package the manuscript's phase, multiplicity, observable,
and transport-network data as explicit local fields. They deliberately avoid
rebuilding Hilbert-space analysis or representation theory inside the active
foundation chain.
-/

namespace CoherenceCalculus

/-- A phase carrier / compatible complex structure for split data `(A, P)`. -/
structure PhaseCarrier (A : AddMap) (P : Projection) where
  phase : AddMap
  unitary : Prop
  squaresToNegIdentity : ∀ x : State, phase (phase x) = State.negate x
  commutesWithOperator : ∀ x : State, phase (A x) = A (phase x)
  commutesWithProjection : ∀ x : State, phase (P x) = P (phase x)

/-- Multiplicity-free complex-type symmetry data on observed channels. -/
structure ComplexTypeSymmetryPackage (Group Channel : Type) where
  relevantChannel : Channel → Prop
  channelCarrier : Channel → Type
  channelAction :
    (g : Group) → (rho : Channel) → channelCarrier rho → channelCarrier rho
  operatorEquivariantOnObservedSector : Prop
  observedSectorMultiplicityFree : Prop
  distinguishedPhase :
    (rho : Channel) → channelCarrier rho → channelCarrier rho
  distinguishedPhaseSkewAdjointUnitary :
    ∀ rho : Channel, relevantChannel rho → Prop
  distinguishedPhaseSquaresNegIdentity :
    ∀ rho : Channel, relevantChannel rho → Prop
  equivariantEndomorphismNormalForm :
    ∀ rho : Channel, relevantChannel rho → Prop

/-- Phase carriers are equivalent when they agree modulo channel signs. -/
structure PhaseCarrierEquivalence (Channel : Type) where
  relevantChannel : Channel → Prop
  channelCarrier : Channel → Type
  referencePhase :
    (rho : Channel) → channelCarrier rho → channelCarrier rho
  comparisonPhase :
    (rho : Channel) → channelCarrier rho → channelCarrier rho
  signChoice : Channel → Bool
  equivalentModuloChannelSigns :
    ∀ rho : Channel, relevantChannel rho → Prop

/-- Complex-type symmetry data with explicit multiplicity spaces. -/
structure ComplexTypeMultiplicityPackage (Group Channel : Type) where
  relevantChannel : Channel → Prop
  channelCarrier : Channel → Type
  multiplicitySpace : Channel → Type
  channelAction :
    (g : Group) → (rho : Channel) → channelCarrier rho → channelCarrier rho
  operatorEquivariantOnObservedSector : Prop
  distinguishedPhase :
    (rho : Channel) → channelCarrier rho → channelCarrier rho
  distinguishedPhaseSkewAdjointUnitary :
    ∀ rho : Channel, relevantChannel rho → Prop
  distinguishedPhaseSquaresNegIdentity :
    ∀ rho : Channel, relevantChannel rho → Prop
  multiplicityNormalForm :
    ∀ rho : Channel, relevantChannel rho → Prop

/-- Phase carriers are gauge-equivalent when they differ by multiplicity-space
unitary conjugacy on each isotypic channel. -/
structure MultiplicityGaugeEquivalence (Channel : Type) where
  relevantChannel : Channel → Prop
  channelCarrier : Channel → Type
  multiplicitySpace : Channel → Type
  referencePhase :
    (rho : Channel) → channelCarrier rho → multiplicitySpace rho → Prop
  comparisonPhase :
    (rho : Channel) → channelCarrier rho → multiplicitySpace rho → Prop
  multiplicityGauge :
    (rho : Channel) → multiplicitySpace rho → multiplicitySpace rho
  gaugeConjugacy :
    ∀ rho : Channel, relevantChannel rho → Prop

/-- Scalarity of the multiplicity commutant for a selected operator family. -/
structure ScalarMultiplicityCommutant (Channel : Type) where
  relevantChannel : Channel → Prop
  multiplicitySpace : Channel → Type
  operatorFamily : (rho : Channel) → Type
  actsOnMultiplicity :
    (rho : Channel) →
      operatorFamily rho → multiplicitySpace rho → multiplicitySpace rho
  commutantIsScalar : ∀ rho : Channel, relevantChannel rho → Prop

/-- Observable irreducibility of an operator family on a multiplicity space. -/
structure ObservableIrreducibility (Space Operator : Type) where
  familyIndex : Type
  family : familyIndex → Operator
  invariantSubspace : (Space → Prop) → Prop
  onlyTrivialInvariantSubspaces : Prop

/-- Real-type observable channels are observable-irreducible with scalar
commutant. -/
structure RealTypeObservableChannel (Space Operator : Type)
    extends ObservableIrreducibility Space Operator where
  commutantIsScalar : Prop

/-- Observable completeness means the generated unital algebra is the full
endomorphism algebra of the multiplicity space. -/
structure ObservableCompleteness (Space Operator : Type) where
  familyIndex : Type
  family : familyIndex → Operator
  generatedUnitalAlgebra : Type
  actsOnSpace : generatedUnitalAlgebra → Space → Space
  generatedAlgebraIsFull : Prop

/-- The generated observable algebra is closed under taking adjoints. -/
structure AdjointClosedGeneratedObservableAlgebra (Space Operator : Type)
    extends ObservableCompleteness Space Operator where
  adjoint : generatedUnitalAlgebra → generatedUnitalAlgebra
  adjointClosed : Prop

/-- A rank-one observable seed is a rank-one projector already present in the
generated observable algebra. -/
structure RankOneObservableSeed (Space Operator : Type) where
  generatedUnitalAlgebra : Type
  rankOneProjection : Operator
  seedLine : Space → Prop
  containedInGeneratedAlgebra : Prop
  projectsOntoSeedLine : Prop

/-- A simple-spectrum observable packages an eigenbasis with pairwise distinct
eigenvalues. -/
structure SimpleSpectrumObservable (Space Scalar Operator : Type) where
  observable : Operator
  basisIndex : Type
  basisVector : basisIndex → Space
  eigenvalue : basisIndex → Scalar
  diagonalizesObservable : Prop
  pairwiseDistinctSpectrum : Prop

/-- Orbit-line data for the rank-one observable orbit construction. -/
structure ObservableOrbitLineFamily (Group Space Line : Type) where
  lineContains : Line → Space → Prop
  action : Group → Space → Space
  seedLine : Line
  orbitLine : Group → Line
  nonorthogonal : Line → Line → Prop
  orbitSpansSpace : Prop
  nonorthogonalityConnected : Prop

/-- A matrix-unit scaffold records the full finite matrix-unit family in a
chosen orthonormal frame. -/
structure MatrixUnitObservableScaffold (Basis Operator : Type) where
  matrixUnit : Basis → Basis → Operator
  containsAllMatrixUnits : Prop

/-- Phase-rigid observable families have scalar commutant. -/
structure PhaseRigidObservableFamily (Space Operator : Type)
    extends ObservableIrreducibility Space Operator where
  commutantIsScalar : Prop

/-- Phase-generating observable families are those for which one of the
manuscript's rigidity packages is explicitly present. -/
structure PhaseGeneratingObservableFamily (Space Operator : Type) where
  familyIndex : Type
  family : familyIndex → Operator
  selectedLawActsThroughFamily : Prop
  commutingPhaseCarrier : Prop
  phaseRigidCase : Prop
  finiteObservableRigidityCase : Prop
  adjointClosedRealTypeCase : Prop
  witness :
    phaseRigidCase ∨ finiteObservableRigidityCase ∨ adjointClosedRealTypeCase

/-- A finite directed graph used for channel transport networks. -/
structure ChannelTransportGraph where
  Vertex : Type
  Edge : Type
  src : Edge → Vertex
  dst : Edge → Vertex
  finiteVertices : Prop
  finiteEdges : Prop

/-- A channel transport network on a finite directed graph. -/
structure ChannelTransportNetwork (Graph : ChannelTransportGraph) where
  fiber : Graph.Vertex → Type
  fiberHilbert : ∀ _ : Graph.Vertex, Prop
  transport : (e : Graph.Edge) → fiber (Graph.dst e) → fiber (Graph.src e)
  transportUnitary : ∀ _ : Graph.Edge, Prop

/-- The transport-energy functional attached to a channel network and a chosen
configuration. -/
structure ChannelTransportEnergy (Graph : ChannelTransportGraph) where
  network : ChannelTransportNetwork Graph
  configuration : (x : Graph.Vertex) → network.fiber x
  energyFunctional : Prop

end CoherenceCalculus
