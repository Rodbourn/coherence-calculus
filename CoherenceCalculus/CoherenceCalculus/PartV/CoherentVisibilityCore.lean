import CoherenceCalculus.PartV.CoherentPrimitiveCore

namespace CoherenceCalculus

/-- A coherence-visible candidate packages the nontrivial endpoint source class
that is read directly on the primary carrier together with one finite active
cut where the retained endpoint-return channel is already active. -/
structure CoherenceVisibleCandidate
    {Channel State Threshold Profile Scalar Horizon : Type}
    (interface : CoherentDirectReturnInterface Channel Scalar)
    (surface : CoherentSchurCandidateSurface
      Channel State Threshold Profile Scalar Horizon) where
  endpointSourceClass : Type
  endpointSourceNontrivial : Prop
  readOnPrimaryCarrier : Prop
  finiteActiveCut : Horizon
  finiteActiveCut_ready : Prop
  retainedEndpointChannelActive : Prop

/-- The visible coherent scalar observable basis records the direct coherent
observable, the scalar endpoint-source observable, and the anchored tangent
observable carried by a coherence-visible candidate. -/
structure VisibleCoherentScalarObservableBasis
    {Channel State Threshold Profile Scalar Horizon : Type}
    (interface : CoherentDirectReturnInterface Channel Scalar)
    (surface : CoherentSchurCandidateSurface
      Channel State Threshold Profile Scalar Horizon) where
  visibleCandidate : CoherenceVisibleCandidate interface surface
  directObservable : Scalar
  endpointObservable : Scalar
  tangentObservable : Scalar

/-- The theorem-facing export of coherence visibility for the later
packet-faithful local layer: one finite active coherent cut with active
retained endpoint-return channel. -/
structure FiniteCoherentEndpointActivity
    {Channel State Threshold Profile Scalar Horizon : Type}
    (surface : CoherentSchurCandidateSurface
      Channel State Threshold Profile Scalar Horizon) where
  activeCut : Horizon
  activeCutFinite : Prop
  retainedEndpointChannelActive : Prop

/-- Coherence visibility already supplies a finite coherent stage where the
retained endpoint-return channel is active. -/
def finiteEndpointActivity
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {surface : CoherentSchurCandidateSurface
      Channel State Threshold Profile Scalar Horizon}
    (basis : VisibleCoherentScalarObservableBasis interface surface) :
    FiniteCoherentEndpointActivity surface := by
  exact
    { activeCut := basis.visibleCandidate.finiteActiveCut
      activeCutFinite := basis.visibleCandidate.finiteActiveCut_ready
      retainedEndpointChannelActive :=
        basis.visibleCandidate.retainedEndpointChannelActive }

/-- The finite coherent endpoint activity read from coherence visibility keeps
exactly the active cut and retained-channel clause carried by the visible
candidate. -/
theorem finiteEndpointActivityCutSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {surface : CoherentSchurCandidateSurface
      Channel State Threshold Profile Scalar Horizon}
    (basis : VisibleCoherentScalarObservableBasis interface surface) :
    (finiteEndpointActivity basis).activeCut =
        basis.visibleCandidate.finiteActiveCut ∧
      (finiteEndpointActivity basis).activeCutFinite =
        basis.visibleCandidate.finiteActiveCut_ready := by
  exact ⟨rfl, rfl⟩

/-- The finite coherent endpoint activity read from coherence visibility keeps
exactly the retained endpoint-channel clause carried by the visible candidate. -/
theorem finiteEndpointActivityChannelSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {surface : CoherentSchurCandidateSurface
      Channel State Threshold Profile Scalar Horizon}
    (basis : VisibleCoherentScalarObservableBasis interface surface) :
    (finiteEndpointActivity basis).retainedEndpointChannelActive =
      basis.visibleCandidate.retainedEndpointChannelActive := by
  rfl

/-- Coherence visibility already carries the finite endpoint activity object
itself, not just its readout. -/
theorem finiteEndpointActivityNonemptySurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {surface : CoherentSchurCandidateSurface
      Channel State Threshold Profile Scalar Horizon}
    (basis : VisibleCoherentScalarObservableBasis interface surface) :
    Nonempty (FiniteCoherentEndpointActivity surface) := by
  exact ⟨finiteEndpointActivity basis⟩

/-- The finite coherent endpoint activity read from coherence visibility keeps
exactly the active cut and retained-channel clause carried by the visible
candidate. -/
theorem finiteEndpointActivitySurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {surface : CoherentSchurCandidateSurface
      Channel State Threshold Profile Scalar Horizon}
    (basis : VisibleCoherentScalarObservableBasis interface surface) :
    (finiteEndpointActivity basis).activeCut =
        basis.visibleCandidate.finiteActiveCut ∧
      (finiteEndpointActivity basis).activeCutFinite =
        basis.visibleCandidate.finiteActiveCut_ready ∧
      (finiteEndpointActivity basis).retainedEndpointChannelActive =
        basis.visibleCandidate.retainedEndpointChannelActive := by
  refine
    ⟨(finiteEndpointActivityCutSurface basis).1,
      (finiteEndpointActivityCutSurface basis).2,
      finiteEndpointActivityChannelSurface basis⟩

/-- Coherence visibility already carries both the exact finite-activity readout
and the corresponding finite endpoint activity object. -/
theorem finiteEndpointActivityWitnessSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {surface : CoherentSchurCandidateSurface
      Channel State Threshold Profile Scalar Horizon}
    (basis : VisibleCoherentScalarObservableBasis interface surface) :
    ((finiteEndpointActivity basis).activeCut =
        basis.visibleCandidate.finiteActiveCut ∧
      (finiteEndpointActivity basis).activeCutFinite =
        basis.visibleCandidate.finiteActiveCut_ready ∧
      (finiteEndpointActivity basis).retainedEndpointChannelActive =
        basis.visibleCandidate.retainedEndpointChannelActive) ∧
      Nonempty (FiniteCoherentEndpointActivity surface) := by
  exact
    ⟨finiteEndpointActivitySurface basis,
      finiteEndpointActivityNonemptySurface basis⟩

/-- Coherence visibility already supplies a finite coherent stage where the
retained endpoint-return channel is active. -/
theorem coherence_visibility_forces_finite_endpoint_activity
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {surface : CoherentSchurCandidateSurface
      Channel State Threshold Profile Scalar Horizon}
    (basis : VisibleCoherentScalarObservableBasis interface surface) :
    Nonempty (FiniteCoherentEndpointActivity surface) := by
  exact finiteEndpointActivityNonemptySurface basis

end CoherenceCalculus
