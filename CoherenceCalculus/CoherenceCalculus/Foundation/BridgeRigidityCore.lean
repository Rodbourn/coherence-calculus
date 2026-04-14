import CoherenceCalculus.Foundation.SelectedChannelRigidityCore

/-!
# Foundation.BridgeRigidityCore

Manuscript-facing realized-class rigidity packages and local datum interfaces
for the Chapter 7 bridge.

These definitions remain structural. They record the exact package data named
in the manuscript while keeping all analytic, spectral, and representation
content explicit as local fields.
-/

namespace CoherenceCalculus

/-- A realized class is transport-rigid on the selected channels when it
carries disciplined transport-order data and every relevant selected channel is
equipped with a quadratically rigid selected channel package together with the
explicit order-one forcing data named in the manuscript. -/
structure TransportRigidRealizedClass (Index Time Channel : Type)
    extends TransportOrderDisciplinedRealizedClass Index Time where
  relevantChannel : Index → Channel → Prop
  orderOneForcingHypotheses :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  boundedTransportBaseRepresentation :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  quadraticallyRigidSystem :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c →
      QuadraticallyRigidSelectedChannelSystem Time Channel

/-- A realized class is observable-rigidity generated on the selected channels
when each relevant channel comes with at least one of the witness packages
listed in the manuscript. -/
structure ObservableRigidityGeneratedRealizedClass (Index Time Channel : Type)
    extends AdmissibleRealizedClass Index Time where
  relevantChannel : Index → Channel → Prop
  phaseGeneratedWithObservableIrreducible :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  observableCompletePackage :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  finiteObservableRigidityPackage :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  adjointClosedRealTypePackage :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  observableOrbitGeneratedPackage :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  witness :
    ∀ i : Index, ∀ c : Channel, ∀ hc : relevantChannel i c,
      phaseGeneratedWithObservableIrreducible i c hc ∨
        observableCompletePackage i c hc ∨
        finiteObservableRigidityPackage i c hc ∨
        adjointClosedRealTypePackage i c hc ∨
        observableOrbitGeneratedPackage i c hc

/-- A realized class is transport-rigidity generated on the selected channels
when each relevant channel comes with at least one transport-rigidity witness
package from the manuscript list. -/
structure TransportRigidityGeneratedRealizedClass (Index Time Channel : Type)
    extends AdmissibleRealizedClass Index Time where
  relevantChannel : Index → Channel → Prop
  transportGeneratedPackage :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  noPreferredDirectionOrderOnePackage :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  quadraticallyRigidOrderOnePackage :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  witness :
    ∀ i : Index, ∀ c : Channel, ∀ hc : relevantChannel i c,
      transportGeneratedPackage i c hc ∨
        noPreferredDirectionOrderOnePackage i c hc ∨
        quadraticallyRigidOrderOnePackage i c hc

/-- A realized class is rigidity-generated on the selected channels when it is
both observable-rigidity generated and transport-rigidity generated. -/
structure RigidityGeneratedRealizedClass (Index Time Channel : Type) where
  observable :
    ObservableRigidityGeneratedRealizedClass Index Time Channel
  transport :
    TransportRigidityGeneratedRealizedClass Index Time Channel

/-- Governing-datum rigidity is the conjunction of observable rigidity and
transport rigidity on the selected channels. -/
structure GoverningDatumRigidRealizedClass (Index Time : Type)
    extends AdmissibleRealizedClass Index Time where
  observableRigidSelectedChannels : Prop
  transportRigidSelectedChannels : Prop

/-- Closure rigidity on the selected symmetry channels. All representation and
equivariance content remains explicit as local fields. -/
structure ClosureRigidRealizedClass (Index Time Channel : Type)
    extends AdmissibleRealizedClass Index Time where
  relevantChannel : Index → Channel → Prop
  observedSectorHasFiniteUnitarySymmetry :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  selectedClosureEquivariant :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  selectedClosureSymmetryScalar :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop

/-- Symmetry-generated realized classes package the exact bridge hypotheses
listed in the manuscript. -/
structure SymmetryGeneratedRealizedClass (Index Time Channel : Type)
    extends AdmissibleRealizedClass Index Time where
  observableRigidityGeneratedSelectedChannels : Prop
  transportOrderDisciplinedSelectedChannels : Prop
  relevantChannel : Index → Channel → Prop
  transportGeneratedSelectedChannelSystem :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c →
      TransportGeneratedSelectedChannelSystem Time Channel
  observedSectorHasFiniteUnitarySymmetry :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  selectedClosureEquivariant :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  multiplicityFreeSymmetryRepresentation :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop

/-- Locally homogeneous realized classes package the orbit-frame, order-one,
and multiplicity-free closure data from the manuscript. -/
structure LocallyHomogeneousRealizedClass (Index Time Channel : Type)
    extends AdmissibleRealizedClass Index Time where
  observableOrbitGeneratedSelectedChannels : Prop
  transportOrderDisciplinedSelectedChannels : Prop
  relevantChannel : Index → Channel → Prop
  irreducibleOrthogonalOrbitFrame :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  selectedQuadraticTransportDirectionAdapted : 
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  orderOneForcedTransportBase :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  observedSectorHasFiniteUnitarySymmetry :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  selectedClosureEquivariant :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop
  multiplicityFreeSymmetryRepresentation :
    ∀ i : Index, ∀ c : Channel, relevantChannel i c → Prop

/-- The local internal datum on a selected channel is the triple of forced
phase, scalar quadratic, and scalar closure data. -/
structure LocalInternalDatumSelectedChannels
    (PhaseClass Scalar ClosureClass : Type) where
  phaseCarrierClass : PhaseClass
  quadraticScalar : Scalar
  closureClass : ClosureClass
  phaseCarrierMeaning : Prop
  quadraticScalarMeaning : Prop
  closureClassMeaning : Prop

/-- The gauge-compatible local internal datum extends the local internal datum
by the local gauge-covariance class, with an optional unimodular reduction
flag. -/
structure GaugeCompatibleLocalInternalDatum
    (PhaseClass Scalar ClosureClass GaugeClass : Type)
    extends LocalInternalDatumSelectedChannels
      PhaseClass Scalar ClosureClass where
  gaugeCovarianceClass : GaugeClass
  gaugeCovarianceMeaning : Prop
  reducedUnimodularGaugeClass : Prop

end CoherenceCalculus
