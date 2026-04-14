import CoherenceCalculus.Foundation.BridgeTransportCore

/-!
# Foundation.SelectedChannelRigidityCore

Manuscript-facing selected-channel rigidity packages for the Chapter 7 bridge.

These definitions stay deliberately structural. They package the exact channel
data named in the manuscript without importing Hilbert-space, Lie-group, or
representation-theoretic infrastructure into the active root.
-/

namespace CoherenceCalculus

/-- The selected channel fiber at a distinguished channel of a selected channel
transport system. -/
abbrev SelectedChannelFiber
    {Time Vertex : Type}
    (system : SelectedChannelTransportSystem Time Vertex)
    (channel : Vertex) : Type :=
  system.fiber channel

/-- Manuscript-facing package for isotropic selected channel data. -/
structure IsotropicSelectedChannelSystem (Time Vertex Symm : Type) where
  system : SelectedChannelTransportSystem Time Vertex
  channel : Vertex
  transportBase : SelectedChannelFiber system channel → SelectedChannelFiber system channel
  action : Symm → SelectedChannelFiber system channel → SelectedChannelFiber system channel
  action_is_orthogonal : Prop
  irreducible_real_module : Prop
  transport_commutes :
    ∀ g : Symm, ∀ x : SelectedChannelFiber system channel,
      action g (transportBase x) = transportBase (action g x)

/-- Manuscript-facing package for sphere-transitive selected channel data. -/
structure SphereTransitiveSelectedChannelSystem (Time Vertex Symm : Type) where
  system : SelectedChannelTransportSystem Time Vertex
  channel : Vertex
  transportBase : SelectedChannelFiber system channel → SelectedChannelFiber system channel
  action : Symm → SelectedChannelFiber system channel → SelectedChannelFiber system channel
  action_is_orthogonal : Prop
  sphere_transitive : Prop
  transport_commutes :
    ∀ g : Symm, ∀ x : SelectedChannelFiber system channel,
      action g (transportBase x) = transportBase (action g x)

/-- Manuscript-facing package for full-orthogonal selected channel data. -/
structure FullOrthogonalSelectedChannelSystem (Time Vertex : Type) where
  system : SelectedChannelTransportSystem Time Vertex
  channel : Vertex
  transportBase : SelectedChannelFiber system channel → SelectedChannelFiber system channel
  full_orthogonal_action : Prop
  transport_commutes_with_all_orthogonal : Prop

/-- Manuscript-facing package for metric-isotropic selected channel data. -/
structure MetricIsotropicSelectedChannelSystem (Time Vertex : Type) where
  system : SelectedChannelTransportSystem Time Vertex
  channel : Vertex
  transportBase : SelectedChannelFiber system channel → SelectedChannelFiber system channel
  metric_isotropic : Prop

/-- Manuscript-facing package for direction-frame isotropic selected channel
data. -/
structure DirectionFrameSelectedChannelSystem
    (Time Vertex Frame Symm : Type) where
  system : SelectedChannelTransportSystem Time Vertex
  channel : Vertex
  transportBase : SelectedChannelFiber system channel → SelectedChannelFiber system channel
  quadraticTransport :
    SelectedChannelFiber system channel → SelectedChannelFiber system channel
  frame : Frame
  action : Symm → SelectedChannelFiber system channel → SelectedChannelFiber system channel
  tight_isotropic_frame : Prop
  direction_adapted_quadratic_transport : Prop
  quadratic_transport_equivariant : Prop

/-- Manuscript-facing package for selected channels without preferred direction
at quadratic order. -/
structure NoPreferredDirectionSelectedChannelSystem (Time Vertex : Type) where
  system : SelectedChannelTransportSystem Time Vertex
  channel : Vertex
  transportBase : SelectedChannelFiber system channel → SelectedChannelFiber system channel
  quadratic_transport_rigidity_package : Prop

/-- Manuscript-facing package for quadratically rigid selected channel data:
one of the listed rigidity packages holds on the distinguished selected
channel. -/
structure QuadraticallyRigidSelectedChannelSystem (Time Vertex : Type) where
  system : SelectedChannelTransportSystem Time Vertex
  channel : Vertex
  transportBase : SelectedChannelFiber system channel → SelectedChannelFiber system channel
  isotropic_selected_channel_data : Prop
  sphere_transitive_selected_channel_data : Prop
  full_orthogonal_selected_channel_data : Prop
  metric_isotropic_selected_channel_data : Prop
  direction_frame_selected_channel_data : Prop
  rigid_case :
    isotropic_selected_channel_data ∨
      sphere_transitive_selected_channel_data ∨
      full_orthogonal_selected_channel_data ∨
      metric_isotropic_selected_channel_data ∨
      direction_frame_selected_channel_data

/-- Manuscript-facing package for transport-generated selected channel data. -/
structure TransportGeneratedSelectedChannelSystem (Time Vertex : Type) where
  system : SelectedChannelTransportSystem Time Vertex
  channel : Vertex
  transportBase : SelectedChannelFiber system channel → SelectedChannelFiber system channel
  order_one_forcing_hypotheses : Prop
  unique_minimal_order_class : Prop
  no_preferred_direction_at_quadratic_order : Prop

/-- Manuscript-facing package for scalar-recursive selected channel data. -/
structure ScalarRecursiveSelectedChannelSystem (Time Vertex : Type) where
  system : SelectedChannelTransportSystem Time Vertex
  channel : Vertex
  transportBase : SelectedChannelFiber system channel → SelectedChannelFiber system channel
  scalar_quadratic_transport_law : Prop
  recursive_transport_law : Prop

end CoherenceCalculus
