import CoherenceCalculus.PartV.ConstantCandidateCore

namespace CoherenceCalculus

/-- The first coherent direct/return interface, together with the exact
lossless first closed scalar law on that packet. -/
structure CoherentDirectReturnInterface (Channel Scalar : Type) where
  primitive : TwoChannelPrimitiveDatum Channel Scalar
  forcing : Channel
  derivative : Channel
  add : Channel → Channel → Channel
  action : Scalar → Channel → Channel
  exact_law :
    derivative = add forcing (action primitive.closureScalar primitive.direct)

/-- The theorem-facing export of the first coherent packet: the packet itself
and the exact first closed affine law carried on it. -/
def forcedPrimitive
    {Channel Scalar : Type}
    (data : CoherentDirectReturnInterface Channel Scalar) :
    TwoChannelPrimitiveDatum Channel Scalar := by
  exact data.primitive

/-- The coherent direct/return interface already fixes its primitive packet and
the exact first closed affine law carried on that packet. -/
theorem forcedPrimitiveSurface
    {Channel Scalar : Type}
    (data : CoherentDirectReturnInterface Channel Scalar) :
    forcedPrimitive data = data.primitive ∧
      data.derivative =
        data.add data.forcing
          (data.action (forcedPrimitive data).closureScalar
            (forcedPrimitive data).direct) := by
  exact ⟨rfl, data.exact_law⟩

/-- The theorem-facing export of the first coherent packet: the packet itself
and the exact first closed affine law carried on it. -/
theorem forced_first_coherent_direct_return_interface
    {Channel Scalar : Type}
    (data : CoherentDirectReturnInterface Channel Scalar) :
    ∃ primitive : TwoChannelPrimitiveDatum Channel Scalar,
      primitive = data.primitive ∧
        data.derivative =
          data.add data.forcing
            (data.action primitive.closureScalar primitive.direct) := by
  refine ⟨forcedPrimitive data, (forcedPrimitiveSurface data).1, ?_⟩
  exact (forcedPrimitiveSurface data).2

/-- Any first-rung scalar intrinsic to the coherent primitive packet is rigid
when it is forced to agree with the unique closure scalar. -/
structure CoherentIntrinsicScalarFamily (Channel Scalar : Type) where
  interface : CoherentDirectReturnInterface Channel Scalar
  Carrier : Type
  value : Carrier → Scalar
  rigid : ∀ x : Carrier, value x = interface.primitive.closureScalar

/-- The earliest intrinsic scalar on the pure coherent branch is exactly the
first coherent closure scalar. -/
theorem earliest_intrinsic_scalar_coupling_pure_coherent
    {Channel Scalar : Type}
    (family : CoherentIntrinsicScalarFamily Channel Scalar)
    (x : family.Carrier) :
    family.value x = family.interface.primitive.closureScalar := by
  exact family.rigid x

/-- Build the coherent Part V search surface directly from the first coherent
direct/return primitive interface. -/
def coherentSchurCandidateSurfaceOfInterface
    {Channel State Threshold Profile Scalar Horizon : Type}
    (interface : CoherentDirectReturnInterface Channel Scalar)
    (thresholdView : State → Threshold)
    (profileView : State → Profile)
    (localInvariant : State → Scalar)
    (horizonCut : Horizon)
    (profile_autonomous : AutonomousCarrier profileView localInvariant) :
    CoherentSchurCandidateSurface
      Channel State Threshold Profile Scalar Horizon := by
  refine
    { primitive := interface.primitive
      thresholdView := thresholdView
      profileView := profileView
      localInvariant := localInvariant
      horizonCut := horizonCut
      profile_autonomous := profile_autonomous }

/-- The coherent search surface built from the interface keeps exactly that
primitive packet, those views, that local invariant, and that horizon cut. -/
theorem coherentSchurCandidatePrimitiveSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    (interface : CoherentDirectReturnInterface Channel Scalar)
    (thresholdView : State → Threshold)
    (profileView : State → Profile)
    (localInvariant : State → Scalar)
    (horizonCut : Horizon)
    (profile_autonomous : AutonomousCarrier profileView localInvariant) :
    (coherentSchurCandidateSurfaceOfInterface
      interface thresholdView profileView localInvariant horizonCut
      profile_autonomous).primitive = interface.primitive := by
  rfl

/-- The coherent search surface keeps exactly the threshold and profile views
that were supplied at the interface. -/
theorem coherentSchurCandidateViewSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    (interface : CoherentDirectReturnInterface Channel Scalar)
    (thresholdView : State → Threshold)
    (profileView : State → Profile)
    (localInvariant : State → Scalar)
    (horizonCut : Horizon)
    (profile_autonomous : AutonomousCarrier profileView localInvariant) :
    (coherentSchurCandidateSurfaceOfInterface
      interface thresholdView profileView localInvariant horizonCut
      profile_autonomous).thresholdView = thresholdView ∧
      (coherentSchurCandidateSurfaceOfInterface
        interface thresholdView profileView localInvariant horizonCut
        profile_autonomous).profileView = profileView := by
  exact ⟨rfl, rfl⟩

/-- The coherent search surface keeps exactly the local invariant and horizon
cut that were supplied at the interface. -/
theorem coherentSchurCandidateLocalSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    (interface : CoherentDirectReturnInterface Channel Scalar)
    (thresholdView : State → Threshold)
    (profileView : State → Profile)
    (localInvariant : State → Scalar)
    (horizonCut : Horizon)
    (profile_autonomous : AutonomousCarrier profileView localInvariant) :
    (coherentSchurCandidateSurfaceOfInterface
      interface thresholdView profileView localInvariant horizonCut
      profile_autonomous).localInvariant = localInvariant ∧
      (coherentSchurCandidateSurfaceOfInterface
        interface thresholdView profileView localInvariant horizonCut
        profile_autonomous).horizonCut = horizonCut := by
  exact ⟨rfl, rfl⟩

/-- The coherent search surface built from the interface keeps exactly that
primitive packet, those views, that local invariant, and that horizon cut. -/
theorem coherentSchurCandidateSurfaceOfInterface_readout
    {Channel State Threshold Profile Scalar Horizon : Type}
    (interface : CoherentDirectReturnInterface Channel Scalar)
    (thresholdView : State → Threshold)
    (profileView : State → Profile)
    (localInvariant : State → Scalar)
    (horizonCut : Horizon)
    (profile_autonomous : AutonomousCarrier profileView localInvariant) :
    (coherentSchurCandidateSurfaceOfInterface
      interface thresholdView profileView localInvariant horizonCut
      profile_autonomous).primitive = interface.primitive ∧
      (coherentSchurCandidateSurfaceOfInterface
        interface thresholdView profileView localInvariant horizonCut
        profile_autonomous).thresholdView = thresholdView ∧
      (coherentSchurCandidateSurfaceOfInterface
        interface thresholdView profileView localInvariant horizonCut
        profile_autonomous).profileView = profileView ∧
      (coherentSchurCandidateSurfaceOfInterface
        interface thresholdView profileView localInvariant horizonCut
        profile_autonomous).localInvariant = localInvariant ∧
      (coherentSchurCandidateSurfaceOfInterface
        interface thresholdView profileView localInvariant horizonCut
        profile_autonomous).horizonCut = horizonCut := by
  refine
    ⟨coherentSchurCandidatePrimitiveSurface
      interface thresholdView profileView localInvariant horizonCut
      profile_autonomous, ?_, ?_, ?_, ?_⟩
  exact
    (coherentSchurCandidateViewSurface
      interface thresholdView profileView localInvariant horizonCut
      profile_autonomous).1
  exact
    (coherentSchurCandidateViewSurface
      interface thresholdView profileView localInvariant horizonCut
      profile_autonomous).2
  exact
    (coherentSchurCandidateLocalSurface
      interface thresholdView profileView localInvariant horizonCut
      profile_autonomous).1
  exact
    (coherentSchurCandidateLocalSurface
      interface thresholdView profileView localInvariant horizonCut
      profile_autonomous).2

/-- The coherent primitive constant search datum is obtained by reusing the
primitive scalar already forced on the first coherent packet. -/
def coherentPrimitiveConstantSearchDatumOfInterface
    {Channel State Threshold Profile Scalar Horizon : Type}
    (interface : CoherentDirectReturnInterface Channel Scalar)
    (thresholdView : State → Threshold)
    (profileView : State → Profile)
    (localInvariant : State → Scalar)
    (horizonCut : Horizon)
    (profile_autonomous : AutonomousCarrier profileView localInvariant) :
    CoherentPrimitiveConstantSearchDatum
      Channel State Threshold Profile Scalar Horizon := by
  refine
    { surface :=
        coherentSchurCandidateSurfaceOfInterface
          interface thresholdView profileView localInvariant horizonCut
          profile_autonomous
      primitiveScalar := interface.primitive.closureScalar
      primitiveScalar_exact := rfl }

/-- The primitive constant-search datum built from the interface keeps exactly
the constructed coherent surface and the forced primitive closure scalar. -/
theorem coherentPrimitiveConstantSearchSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    (interface : CoherentDirectReturnInterface Channel Scalar)
    (thresholdView : State → Threshold)
    (profileView : State → Profile)
    (localInvariant : State → Scalar)
    (horizonCut : Horizon)
    (profile_autonomous : AutonomousCarrier profileView localInvariant) :
    (coherentPrimitiveConstantSearchDatumOfInterface
      interface thresholdView profileView localInvariant horizonCut
      profile_autonomous).surface =
        coherentSchurCandidateSurfaceOfInterface
          interface thresholdView profileView localInvariant horizonCut
          profile_autonomous := by
  rfl

/-- The primitive constant-search datum keeps exactly the coherent closure
scalar already forced on the first coherent packet. -/
theorem coherentPrimitiveScalarSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    (interface : CoherentDirectReturnInterface Channel Scalar)
    (thresholdView : State → Threshold)
    (profileView : State → Profile)
    (localInvariant : State → Scalar)
    (horizonCut : Horizon)
    (profile_autonomous : AutonomousCarrier profileView localInvariant) :
    (coherentPrimitiveConstantSearchDatumOfInterface
      interface thresholdView profileView localInvariant horizonCut
      profile_autonomous).primitiveScalar =
        interface.primitive.closureScalar := by
  rfl

/-- The primitive constant-search datum built from the interface keeps exactly
the constructed coherent surface and the forced primitive closure scalar. -/
theorem coherentPrimitiveConstantSearchDatumOfInterface_readout
    {Channel State Threshold Profile Scalar Horizon : Type}
    (interface : CoherentDirectReturnInterface Channel Scalar)
    (thresholdView : State → Threshold)
    (profileView : State → Profile)
    (localInvariant : State → Scalar)
    (horizonCut : Horizon)
    (profile_autonomous : AutonomousCarrier profileView localInvariant) :
    (coherentPrimitiveConstantSearchDatumOfInterface
      interface thresholdView profileView localInvariant horizonCut
      profile_autonomous).surface =
        coherentSchurCandidateSurfaceOfInterface
          interface thresholdView profileView localInvariant horizonCut
          profile_autonomous ∧
      (coherentPrimitiveConstantSearchDatumOfInterface
        interface thresholdView profileView localInvariant horizonCut
        profile_autonomous).primitiveScalar =
          interface.primitive.closureScalar := by
  exact
    ⟨coherentPrimitiveConstantSearchSurface
        interface thresholdView profileView localInvariant horizonCut
        profile_autonomous,
      coherentPrimitiveScalarSurface
        interface thresholdView profileView localInvariant horizonCut
        profile_autonomous⟩

end CoherenceCalculus
