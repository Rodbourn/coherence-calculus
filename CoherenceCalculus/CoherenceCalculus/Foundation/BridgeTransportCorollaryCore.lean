import CoherenceCalculus.Foundation.BridgeRigidityCore

/-!
# Foundation.BridgeTransportCorollaryCore

Thin Chapter 7 bridge corollaries for the transport/rigidity tranche.

These theorems deliberately stay structural. Each packages the exact local
selected-channel conclusions named in the manuscript without importing
additional analytic or representation-theoretic machinery.
-/

namespace CoherenceCalculus

/-- Explicit local gauge-covariance package on a selected channel transport
system. -/
structure SelectedChannelGaugeCovarianceData (Time Vertex : Type) where
  system : SelectedChannelTransportSystem Time Vertex
  localGaugeInvariant : Prop
  unimodularReduction : Prop
  localGaugeInvariant_valid : localGaugeInvariant
  unimodularReduction_valid : unimodularReduction

/-- Local gauge covariance and unimodular reduction on a selected channel
transport system. -/
theorem selected_channel_gauge_covariance
    {Time Vertex : Type}
    (data : SelectedChannelGaugeCovarianceData Time Vertex) :
    data.localGaugeInvariant ∧ data.unimodularReduction := by
  exact ⟨data.localGaugeInvariant_valid, data.unimodularReduction_valid⟩

/-- Explicit recursion-forcing package on a selected channel. -/
structure SelectedChannelRecursiveForcingData (Time Vertex : Type) where
  system : SelectedChannelTransportSystem Time Vertex
  orderOneTransport : Prop
  recursiveTransportLaw : Prop
  phaseCompatible : Prop
  orderOneTransport_valid : orderOneTransport
  recursiveTransportLaw_valid : recursiveTransportLaw
  phaseCompatible_valid : phaseCompatible

/-- Order-one selected channels carry the packaged recursion forcing data. -/
theorem selected_channel_recursive_forcing
    {Time Vertex : Type}
    (data : SelectedChannelRecursiveForcingData Time Vertex) :
    data.orderOneTransport ∧
      data.recursiveTransportLaw ∧
      data.phaseCompatible := by
  exact ⟨data.orderOneTransport_valid, data.recursiveTransportLaw_valid,
    data.phaseCompatible_valid⟩

/-- Explicit scalarization package on a selected channel. -/
structure SelectedChannelScalarizationData (System : Type) where
  system : System
  scalarQuadraticLaw : Prop
  uniqueScalar : Prop
  scalarQuadraticLaw_valid : scalarQuadraticLaw
  uniqueScalar_valid : uniqueScalar

/-- The selected channel exports the packaged scalar quadratic transport law. -/
theorem selected_channel_scalarization
    {System : Type}
    (data : SelectedChannelScalarizationData System) :
    data.scalarQuadraticLaw ∧ data.uniqueScalar := by
  exact ⟨data.scalarQuadraticLaw_valid, data.uniqueScalar_valid⟩

/-- Explicit orbit-frame package on a selected channel. -/
structure SelectedChannelOrbitDirectionFrameData (System : Type) where
  system : System
  tightIsotropicDirectionFrame : Prop
  tightIsotropicDirectionFrame_valid : tightIsotropicDirectionFrame

/-- Orbit-generated selected directions form the packaged tight isotropic
direction frame. -/
theorem selected_channel_orbit_direction_frame
    {System : Type}
    (data : SelectedChannelOrbitDirectionFrameData System) :
    data.tightIsotropicDirectionFrame := by
  exact data.tightIsotropicDirectionFrame_valid

/-- Explicit scalar-recursive package on a selected channel. -/
structure SelectedChannelScalarRecursiveData (System : Type) where
  system : System
  scalarQuadraticLaw : Prop
  recursiveTransportLaw : Prop
  scalarQuadraticLaw_valid : scalarQuadraticLaw
  recursiveTransportLaw_valid : recursiveTransportLaw

/-- The selected channel exports the packaged scalar-recursive law. -/
theorem selected_channel_scalar_recursive
    {System : Type}
    (data : SelectedChannelScalarRecursiveData System) :
    data.scalarQuadraticLaw ∧ data.recursiveTransportLaw := by
  exact ⟨data.scalarQuadraticLaw_valid, data.recursiveTransportLaw_valid⟩

/-- Explicit transport-generation package on a selected channel. -/
structure SelectedChannelTransportGenerationData (System : Type) where
  system : System
  orderOneTransport : Prop
  scalarQuadraticLaw : Prop
  recursiveTransportLaw : Prop
  orderOneTransport_valid : orderOneTransport
  scalarQuadraticLaw_valid : scalarQuadraticLaw
  recursiveTransportLaw_valid : recursiveTransportLaw

/-- Transport-generated selected channels export the packaged order-one,
scalar, and recursive transport laws. -/
theorem selected_channel_transport_generation
    {System : Type}
    (data : SelectedChannelTransportGenerationData System) :
    data.orderOneTransport ∧
      data.scalarQuadraticLaw ∧
      data.recursiveTransportLaw := by
  exact ⟨data.orderOneTransport_valid, data.scalarQuadraticLaw_valid,
    data.recursiveTransportLaw_valid⟩

end CoherenceCalculus
