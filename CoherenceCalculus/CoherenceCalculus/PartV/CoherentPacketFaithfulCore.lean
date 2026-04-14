import CoherenceCalculus.PartV.CoherentVisibilityCore
import CoherenceCalculus.PartV.PacketFaithfulLocalCore
import CoherenceCalculus.PartV.CoherentLocalSchurCore

namespace CoherenceCalculus

/-- On the coherent surface, the finite active-cut witness from coherence
visibility and the generic packet-faithful local surface package are the only
remaining data needed before the dressed running/endpoint layers. -/
structure CoherentPacketFaithfulSurfaceOutput
    {Channel State Threshold Profile Scalar Horizon : Type}
    (surface : CoherentSchurCandidateSurface
      Channel State Threshold Profile Scalar Horizon)
    (arith : PacketFaithfulLocalArithmetic Scalar) where
  finiteEndpointActivity : FiniteCoherentEndpointActivity surface
  genericPacketFaithful :
    PacketFaithfulLocalSurfaceOutput
      (coherentToTwoChannelSchurCandidateSurface surface) arith

/-- Once coherence visibility supplies a finite active cut and the coherent
local Schur witness certifies the ordered/realized/packet-faithful hypotheses,
the packet-faithful coherent surface is exactly the generic two-channel local
surface on that same witness. -/
def coherentPacketFaithfulSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface)
    {arith : PacketFaithfulLocalArithmetic Scalar}
    (activity : FiniteCoherentEndpointActivity datum.surface)
    (genericPacketFaithful :
      PacketFaithfulLocalSurfaceOutput
        (coherentToTwoChannelSchurCandidateSurface datum.surface) arith) :
    CoherentPacketFaithfulSurfaceOutput datum.surface arith := by
  exact
    { finiteEndpointActivity := activity
      genericPacketFaithful := genericPacketFaithful }

/-- The coherent packet-faithful surface keeps exactly the finite coherent
activity and generic two-channel packet-faithful package used to build it. -/
theorem coherentPacketFaithfulActivitySurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface)
    {arith : PacketFaithfulLocalArithmetic Scalar}
    (activity : FiniteCoherentEndpointActivity datum.surface)
    (genericPacketFaithful :
      PacketFaithfulLocalSurfaceOutput
        (coherentToTwoChannelSchurCandidateSurface datum.surface) arith) :
    (coherentPacketFaithfulSurface datum activity genericPacketFaithful).finiteEndpointActivity =
      activity := by
  rfl

theorem coherentPacketFaithfulGenericSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface)
    {arith : PacketFaithfulLocalArithmetic Scalar}
    (activity : FiniteCoherentEndpointActivity datum.surface)
    (genericPacketFaithful :
      PacketFaithfulLocalSurfaceOutput
        (coherentToTwoChannelSchurCandidateSurface datum.surface) arith) :
    (coherentPacketFaithfulSurface datum activity genericPacketFaithful).genericPacketFaithful =
      genericPacketFaithful := by
  rfl

/-- The coherent packet-faithful surface keeps exactly the finite coherent
activity and generic two-channel packet-faithful package used to build it. -/
theorem coherentPacketFaithfulSurface_readout
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface)
    {arith : PacketFaithfulLocalArithmetic Scalar}
    (activity : FiniteCoherentEndpointActivity datum.surface)
    (genericPacketFaithful :
      PacketFaithfulLocalSurfaceOutput
        (coherentToTwoChannelSchurCandidateSurface datum.surface) arith) :
    (coherentPacketFaithfulSurface datum activity genericPacketFaithful).finiteEndpointActivity =
        activity ∧
      (coherentPacketFaithfulSurface datum activity genericPacketFaithful).genericPacketFaithful =
        genericPacketFaithful := by
  exact
    ⟨coherentPacketFaithfulActivitySurface datum activity genericPacketFaithful,
      coherentPacketFaithfulGenericSurface datum activity genericPacketFaithful⟩

/-- Once coherence visibility supplies a finite active cut and the coherent
local witness certifies the ordered/realized/packet-faithful hypotheses, the
coherent packet-faithful surface itself is already determined. -/
def coherentPacketFaithfulWitnessSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface)
    (basis : VisibleCoherentScalarObservableBasis interface datum.surface)
    {arith : PacketFaithfulLocalArithmetic Scalar}
    (orderedCut :
      OrderedPrimitivePacketActiveCutDatum
        (coherentToTwoChannelSchurCandidateSurface datum.surface) arith)
    (realizedCut :
      PrimitivePacketRealizedLocalDatum
        (coherentToTwoChannelSchurCandidateSurface datum.surface) arith)
    (chain :
      PacketFaithfulChainRigidityDatum
        (coherentToTwoChannelSchurCandidateSurface datum.surface) arith) :
    datum.orderedPrimitivePacketReady →
      datum.primitivePacketRealizedReady →
      datum.packetFaithfulReady →
        CoherentPacketFaithfulSurfaceOutput datum.surface arith := by
  intro orderedReady realizedReady faithfulReady
  have activity : FiniteCoherentEndpointActivity datum.surface :=
    finiteEndpointActivity basis
  have generic :
      PacketFaithfulLocalSurfaceOutput
        (coherentToTwoChannelSchurCandidateSurface datum.surface) arith :=
    packetFaithfulLocalWitnessSurface
      datum.toBranchLocalWitnessDatum
      orderedCut realizedCut chain
      orderedReady realizedReady faithfulReady
  exact coherentPacketFaithfulSurface datum activity generic

/-- Once coherence visibility supplies a finite active cut and the coherent
local Schur witness certifies the ordered/realized/packet-faithful hypotheses,
the packet-faithful coherent surface is exactly the generic two-channel local
surface on that same witness. -/
theorem ordered_coherent_first_packet_witnesses_now_generic
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface)
    (basis : VisibleCoherentScalarObservableBasis interface datum.surface)
    {arith : PacketFaithfulLocalArithmetic Scalar}
    (orderedCut :
      OrderedPrimitivePacketActiveCutDatum
        (coherentToTwoChannelSchurCandidateSurface datum.surface) arith)
    (realizedCut :
      PrimitivePacketRealizedLocalDatum
        (coherentToTwoChannelSchurCandidateSurface datum.surface) arith)
    (chain :
      PacketFaithfulChainRigidityDatum
        (coherentToTwoChannelSchurCandidateSurface datum.surface) arith) :
    datum.orderedPrimitivePacketReady →
      datum.primitivePacketRealizedReady →
      datum.packetFaithfulReady →
        Nonempty
          (CoherentPacketFaithfulSurfaceOutput datum.surface arith) := by
  intro orderedReady realizedReady faithfulReady
  exact
    ⟨coherentPacketFaithfulWitnessSurface
      datum basis orderedCut realizedCut chain
      orderedReady realizedReady faithfulReady⟩

end CoherenceCalculus
