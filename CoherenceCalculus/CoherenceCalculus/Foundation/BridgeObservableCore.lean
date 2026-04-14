import CoherenceCalculus.Foundation.VariationalSelectionCore

/-!
# Foundation.BridgeObservableCore

Structural realized-class interfaces for the early Chapter 7 observable and
phase bridge.

These definitions package the exact manuscript-facing hypotheses while keeping
all representation-theoretic and multiplicity-space content explicit as local
fields.
-/

namespace CoherenceCalculus

/-- Intrinsic equivariance on the canonical carrier. -/
structure IntrinsicallyEquivariantRealizedClass (Index Time : Type)
    extends AdmissibleRealizedClass Index Time where
  canonicalCarrierIdentification : ∀ _ : Index, Prop
  intrinsicRelabelingAction : Prop
  lowerBoundAndCandidateFamilyEquivariant : ∀ _ : Index, Prop
  normalizationInvariant : ∀ _ : Index, Prop

/-- Subgroup-broken equivariance on the canonical carrier. -/
structure SubgroupBrokenRealizedClass (Index Time : Type)
    extends AdmissibleRealizedClass Index Time where
  canonicalCarrierIdentification : ∀ _ : Index, Prop
  subgroupRestrictedEquivariance : ∀ _ : Index, Prop

/-- Complex-type realized classes with scalar multiplicity commutant. -/
structure ComplexTypeRealizedClass (Index Time Channel : Type)
    extends AdmissibleRealizedClass Index Time where
  relevantChannel : Index → Channel → Prop
  observedSectorHasFiniteUnitarySymmetry :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  transportedSelectionDataEquivariant :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  complexTypeMultiplicityPackage :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  scalarMultiplicityCommutant :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop

/-- Observable irreducibility on the selected channels. -/
structure ObservableIrreducibleRealizedClass (Index Time Channel : Type)
    extends AdmissibleRealizedClass Index Time where
  relevantChannel : Index → Channel → Prop
  multiplicityFamilyAction :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  observableIrreducible :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  selectedSelfAdjointCommutant :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop

/-- Phase-generated realized classes on the selected channels. -/
structure PhaseGeneratedRealizedClass (Index Time Channel : Type)
    extends AdmissibleRealizedClass Index Time where
  relevantChannel : Index → Channel → Prop
  complexTypeMultiplicityPackage :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  phaseGeneratingMultiplicityFamily :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  reducedSelectionSingleton : Prop

/-- Phase-rigid realized classes on the selected channels. -/
structure PhaseRigidRealizedClass (Index Time Channel : Type)
    extends AdmissibleRealizedClass Index Time where
  relevantChannel : Index → Channel → Prop
  complexTypeMultiplicityPackage :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  phaseRigidMultiplicityFamily :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  reducedSelectionSingleton : Prop

/-- Observable rigidity on the selected channels is the conjunction of
phase-rigidity and observable irreducibility. -/
structure ObservableRigidRealizedClass (Index Time : Type)
    extends AdmissibleRealizedClass Index Time where
  phaseRigidSelectedChannels : Prop
  observableIrreducibleSelectedChannels : Prop

/-- Observable-orbit generated realized classes on the selected channels. -/
structure ObservableOrbitGeneratedRealizedClass (Index Time Channel : Type)
    extends AdmissibleRealizedClass Index Time where
  relevantChannel : Index → Channel → Prop
  complexTypeMultiplicityPackage :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  orthogonalSphereTransitiveAction :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  rankOneProjectionOrbitContained :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  reducedSelectionSingleton : Prop

end CoherenceCalculus
