import CoherenceCalculus.PartV.LocalSchurWitnessCore

namespace CoherenceCalculus

/-- The canonical packet-faithful family carried by a single horizon-independent
ratio. The later endpoint/running layers can read their exact scalar faces from
this finite family without reopening the local Schur search. -/
structure CanonicalPacketFaithfulTwoChannelCandidateFamily (Scalar : Type) where
  ratio : Scalar
  beta : Scalar
  rho : Scalar
  gamma : Scalar
  directCompletion : Scalar
  returnCompletion : Scalar

/-- The packet-faithful local surface needs only the scalar arithmetic that
reads the exact local ratio, the canonical finite family, and the least
completion coordinate from the same ratio. -/
structure PacketFaithfulLocalArithmetic (Scalar : Type) where
  directReturnSupportRatio : Scalar → Scalar → Scalar
  canonicalFamilyFromRatio :
    Scalar → CanonicalPacketFaithfulTwoChannelCandidateFamily Scalar
  leastCompletionCoordinateFromRatio : Scalar → Scalar

/-- On an active ordered primitive-packet cut, the collapse defect and the
surviving local scalar are read directly from the direct/return support pair. -/
structure OrderedPrimitivePacketActiveCutDatum
    {Channel Horizon Scalar : Type}
    (surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar)
    (arith : PacketFaithfulLocalArithmetic Scalar) where
  directSupport : Scalar
  returnSupport : Scalar
  retainedEndpointActive : Prop
  collapseDefectPositive : Prop
  localRatio : Scalar
  localRatio_exact :
    localRatio =
      arith.directReturnSupportRatio directSupport returnSupport

/-- On a primitive-packet realized cut, the exact local search is already
reduced to one scalar face, equivalently to the direct/return ratio. -/
structure PrimitivePacketRealizedLocalDatum
    {Channel Horizon Scalar : Type}
    (surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar)
    (arith : PacketFaithfulLocalArithmetic Scalar) where
  localRatio : Scalar
  exactLocalScalarFaceReduction : Prop
  localRatio_is_directReturnBalance : Prop

/-- On a packet-faithful chain, the exact local ratio rigidifies to a canonical
horizon-independent ratio together with its finite family and least-completion
coordinate. -/
structure PacketFaithfulChainRigidityDatum
    {Channel Horizon Scalar : Type}
    (surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar)
    (arith : PacketFaithfulLocalArithmetic Scalar) where
  canonicalRatio : Scalar
  canonicalFamily : CanonicalPacketFaithfulTwoChannelCandidateFamily Scalar
  canonicalFamily_exact :
    canonicalFamily = arith.canonicalFamilyFromRatio canonicalRatio
  unconditionalCompiler : Prop
  leastCompletionCoordinate : Scalar
  leastCompletionCoordinate_exact :
    leastCompletionCoordinate =
      arith.leastCompletionCoordinateFromRatio canonicalRatio
  minimumCompletionBoundary : Prop

/-- The packet-faithful local surface is the combined ordered-cut,
primitive-packet-realized, and packet-faithful-chain package on one local
surface. -/
structure PacketFaithfulLocalSurfaceOutput
    {Channel Horizon Scalar : Type}
    (surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar)
    (arith : PacketFaithfulLocalArithmetic Scalar) where
  orderedCut : OrderedPrimitivePacketActiveCutDatum surface arith
  realizedCut : PrimitivePacketRealizedLocalDatum surface arith
  chain : PacketFaithfulChainRigidityDatum surface arith

/-- Once the branch-local Schur witness certifies the ordered primitive-packet,
primitive-packet realized, and packet-faithful packages on the same primitive
surface, the whole packet-faithful local surface is generic and witness-driven.
-/
def packetFaithfulLocalSurface
    {Channel Horizon Scalar : Type}
    {primitive : TwoChannelPrimitiveDatum Channel Scalar}
    (datum : BranchLocalSchurWitnessDatum
      (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar) primitive)
    {arith : PacketFaithfulLocalArithmetic Scalar}
    (orderedCut : OrderedPrimitivePacketActiveCutDatum datum.surface arith)
    (realizedCut : PrimitivePacketRealizedLocalDatum datum.surface arith)
    (chain : PacketFaithfulChainRigidityDatum datum.surface arith) :
    PacketFaithfulLocalSurfaceOutput datum.surface arith := by
  exact
    { orderedCut := orderedCut
      realizedCut := realizedCut
      chain := chain }

/-- The generic packet-faithful local surface keeps exactly the ordered cut,
realized cut, and chain-rigidity data used to build it. -/
theorem packetFaithfulLocalOrderedCutSurface
    {Channel Horizon Scalar : Type}
    {primitive : TwoChannelPrimitiveDatum Channel Scalar}
    (datum : BranchLocalSchurWitnessDatum
      (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar) primitive)
    {arith : PacketFaithfulLocalArithmetic Scalar}
    (orderedCut : OrderedPrimitivePacketActiveCutDatum datum.surface arith)
    (realizedCut : PrimitivePacketRealizedLocalDatum datum.surface arith)
    (chain : PacketFaithfulChainRigidityDatum datum.surface arith) :
    (packetFaithfulLocalSurface datum orderedCut realizedCut chain).orderedCut =
      orderedCut := by
  rfl

theorem packetFaithfulLocalRealizedCutSurface
    {Channel Horizon Scalar : Type}
    {primitive : TwoChannelPrimitiveDatum Channel Scalar}
    (datum : BranchLocalSchurWitnessDatum
      (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar) primitive)
    {arith : PacketFaithfulLocalArithmetic Scalar}
    (orderedCut : OrderedPrimitivePacketActiveCutDatum datum.surface arith)
    (realizedCut : PrimitivePacketRealizedLocalDatum datum.surface arith)
    (chain : PacketFaithfulChainRigidityDatum datum.surface arith) :
    (packetFaithfulLocalSurface datum orderedCut realizedCut chain).realizedCut =
      realizedCut := by
  rfl

theorem packetFaithfulLocalChainSurface
    {Channel Horizon Scalar : Type}
    {primitive : TwoChannelPrimitiveDatum Channel Scalar}
    (datum : BranchLocalSchurWitnessDatum
      (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar) primitive)
    {arith : PacketFaithfulLocalArithmetic Scalar}
    (orderedCut : OrderedPrimitivePacketActiveCutDatum datum.surface arith)
    (realizedCut : PrimitivePacketRealizedLocalDatum datum.surface arith)
    (chain : PacketFaithfulChainRigidityDatum datum.surface arith) :
    (packetFaithfulLocalSurface datum orderedCut realizedCut chain).chain =
      chain := by
  rfl

/-- The generic packet-faithful local surface keeps exactly the ordered cut,
realized cut, and chain-rigidity data used to build it. -/
theorem packetFaithfulLocalSurface_readout
    {Channel Horizon Scalar : Type}
    {primitive : TwoChannelPrimitiveDatum Channel Scalar}
    (datum : BranchLocalSchurWitnessDatum
      (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar) primitive)
    {arith : PacketFaithfulLocalArithmetic Scalar}
    (orderedCut : OrderedPrimitivePacketActiveCutDatum datum.surface arith)
    (realizedCut : PrimitivePacketRealizedLocalDatum datum.surface arith)
    (chain : PacketFaithfulChainRigidityDatum datum.surface arith) :
    (packetFaithfulLocalSurface datum orderedCut realizedCut chain).orderedCut =
        orderedCut ∧
      (packetFaithfulLocalSurface datum orderedCut realizedCut chain).realizedCut =
        realizedCut ∧
      (packetFaithfulLocalSurface datum orderedCut realizedCut chain).chain =
        chain := by
  exact
    ⟨packetFaithfulLocalOrderedCutSurface datum orderedCut realizedCut chain,
      packetFaithfulLocalRealizedCutSurface datum orderedCut realizedCut chain,
      packetFaithfulLocalChainSurface datum orderedCut realizedCut chain⟩

/-- Once the local witness datum certifies the ordered, realized, and
packet-faithful hypotheses, the packet-faithful surface itself is already the
generic local surface on that same cut. -/
def packetFaithfulLocalWitnessSurface
    {Channel Horizon Scalar : Type}
    {primitive : TwoChannelPrimitiveDatum Channel Scalar}
    (datum : BranchLocalSchurWitnessDatum
      (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar) primitive)
    {arith : PacketFaithfulLocalArithmetic Scalar}
    (orderedCut : OrderedPrimitivePacketActiveCutDatum datum.surface arith)
    (realizedCut : PrimitivePacketRealizedLocalDatum datum.surface arith)
    (chain : PacketFaithfulChainRigidityDatum datum.surface arith) :
    datum.orderedPrimitivePacketReady →
      datum.primitivePacketRealizedReady →
    datum.packetFaithfulReady →
        PacketFaithfulLocalSurfaceOutput datum.surface arith := by
  intro _ _ _
  exact packetFaithfulLocalSurface datum orderedCut realizedCut chain

/-- Once the branch-local Schur witness certifies the ordered primitive-packet,
primitive-packet realized, and packet-faithful packages on the same primitive
surface, the whole packet-faithful local surface is generic and witness-driven.
-/
theorem packet_faithful_local_surfaces_now_witness_driven
    {Channel Horizon Scalar : Type}
    {primitive : TwoChannelPrimitiveDatum Channel Scalar}
    (datum : BranchLocalSchurWitnessDatum
      (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar) primitive)
    {arith : PacketFaithfulLocalArithmetic Scalar}
    (orderedCut : OrderedPrimitivePacketActiveCutDatum datum.surface arith)
    (realizedCut : PrimitivePacketRealizedLocalDatum datum.surface arith)
    (chain : PacketFaithfulChainRigidityDatum datum.surface arith) :
    datum.orderedPrimitivePacketReady →
      datum.primitivePacketRealizedReady →
      datum.packetFaithfulReady →
        Nonempty (PacketFaithfulLocalSurfaceOutput datum.surface arith) := by
  intro orderedReady realizedReady faithfulReady
  exact
    ⟨packetFaithfulLocalWitnessSurface
      datum orderedCut realizedCut chain
      orderedReady realizedReady faithfulReady⟩

end CoherenceCalculus
