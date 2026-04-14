import CoherenceCalculus.PartV.ConstantCandidateCore

/-!
# PartV.LocalSchurWitnessCore

Detached Part V local witness surface for the two-channel Schur reduction.

This file packages the minimal generic witness layer needed by the later local
compiler:

- the local two-channel surface
- rank-two support witnesses
- branch-local witness data
- the generic local compiler output read from that witness data

The intent is reader-facing: the public surface should expose the mathematical
packages, while the witness extraction itself stays lightweight.
-/

namespace CoherenceCalculus

/-- The generic two-channel local Schur surface only freezes the primitive
packet and the active horizon cut needed by the local compiler. -/
structure TwoChannelSchurCandidateSurface (Channel Horizon Scalar : Type) where
  primitive : TwoChannelPrimitiveDatum Channel Scalar
  horizonCut : Horizon

/-- A rank-at-most-two Schur support witness records the two active local
channels that survive the local Schur compression. -/
structure RankTwoTwoChannelSchurSupport
    {Channel Horizon Scalar : Type}
    (surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar) where
  directSupport : Channel
  returnSupport : Channel

/-- A transported multiplicity-free mode gate already carries the local
rank-two support witness needed by the generic compiler. -/
structure TransportedMultiplicityFreeTwoChannelModeGate
    {Channel Horizon Scalar : Type}
    (surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar) where
  rankTwoSupport : RankTwoTwoChannelSchurSupport surface

namespace TransportedMultiplicityFreeTwoChannelModeGate

/-- Mode-gated local cuts therefore force the generic rank-two support
certificate immediately. -/
def rankTwoSupportWitness
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    (gate : TransportedMultiplicityFreeTwoChannelModeGate surface) :
    RankTwoTwoChannelSchurSupport surface := by
  exact gate.rankTwoSupport

/-- Mode-gated local cuts therefore force the generic rank-two support
certificate immediately. -/
theorem rankTwoSupport_nonempty
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    (gate : TransportedMultiplicityFreeTwoChannelModeGate surface) :
    Nonempty (RankTwoTwoChannelSchurSupport surface) := by
  exact ⟨gate.rankTwoSupportWitness⟩

end TransportedMultiplicityFreeTwoChannelModeGate

/-- A symmetry-rigid gate packages the same local rank-two support witness. -/
structure SymmetryRigidTwoChannelSchurGate
    {Channel Horizon Scalar : Type}
    (surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar) where
  rankTwoSupport : RankTwoTwoChannelSchurSupport surface

namespace SymmetryRigidTwoChannelSchurGate

/-- Symmetry-rigid local cuts also force generic rank-two Schur support. -/
def rankTwoSupportWitness
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    (gate : SymmetryRigidTwoChannelSchurGate surface) :
    RankTwoTwoChannelSchurSupport surface := by
  exact gate.rankTwoSupport

/-- Symmetry-rigid local cuts also force generic rank-two Schur support. -/
theorem rankTwoSupport_nonempty
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    (gate : SymmetryRigidTwoChannelSchurGate surface) :
    Nonempty (RankTwoTwoChannelSchurSupport surface) := by
  exact ⟨gate.rankTwoSupportWitness⟩

end SymmetryRigidTwoChannelSchurGate

/-- The local rank-two source on a branch may come either from a symmetry-rigid
gate or from a transported multiplicity-free mode gate. -/
inductive LocalRankTwoSource
    {Channel Horizon Scalar : Type}
    (surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar) where
  | symmetry
      (gate : SymmetryRigidTwoChannelSchurGate surface) :
      LocalRankTwoSource surface
  | mode
      (gate : TransportedMultiplicityFreeTwoChannelModeGate surface) :
      LocalRankTwoSource surface

namespace LocalRankTwoSource

/-- Any certified local rank-two source yields the rank-two support witness
needed by the generic local compiler. -/
def rankTwoSupport
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    (source : LocalRankTwoSource surface) :
    RankTwoTwoChannelSchurSupport surface := by
  cases source with
  | symmetry gate =>
      exact gate.rankTwoSupportWitness
  | mode gate =>
      exact gate.rankTwoSupportWitness

/-- Any certified local rank-two source yields the rank-two support witness
needed by the generic local compiler. -/
theorem rankTwoSupport_nonempty
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    (source : LocalRankTwoSource surface) :
    Nonempty (RankTwoTwoChannelSchurSupport surface) := by
  exact ⟨source.rankTwoSupport⟩

end LocalRankTwoSource

/-- A branch-local Schur witness datum fixes the active two-channel local
surface, its primitive compatibility, the local rank-two source, and any later
generic local witness packages already certified on that same surface. -/
structure BranchLocalSchurWitnessDatum
    {Channel Horizon Scalar : Type}
    (primitive : TwoChannelPrimitiveDatum Channel Scalar) where
  surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar
  source : LocalRankTwoSource surface
  primitive_compatible : surface.primitive = primitive
  projectiveReady : Prop
  strictReady : Prop
  distinguishedCutReady : Prop
  orderedPrimitivePacketReady : Prop
  primitivePacketRealizedReady : Prop
  packetFaithfulReady : Prop

/-- The generic local compiler consumes only the rank-two witness and the later
surface packages already carried by the branch-local datum. -/
structure LocalSchurCompilerOutput
    {Channel Horizon Scalar : Type}
    (surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar) where
  rankTwoSupport : RankTwoTwoChannelSchurSupport surface
  projectiveReady : Prop
  strictReady : Prop
  distinguishedCutReady : Prop
  orderedPrimitivePacketReady : Prop
  primitivePacketRealizedReady : Prop
  packetFaithfulReady : Prop

namespace BranchLocalSchurWitnessDatum

/-- After the branch supplies its local witness datum, the generic local
two-channel compiler can be reused without any further branch-specific local
Schur algebra. -/
def compilerOutput
    {Channel Horizon Scalar : Type}
    {primitive : TwoChannelPrimitiveDatum Channel Scalar}
    (datum : BranchLocalSchurWitnessDatum
      (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar) primitive) :
    LocalSchurCompilerOutput datum.surface := by
  refine
    { rankTwoSupport := datum.source.rankTwoSupport
      projectiveReady := datum.projectiveReady
      strictReady := datum.strictReady
      distinguishedCutReady := datum.distinguishedCutReady
      orderedPrimitivePacketReady := datum.orderedPrimitivePacketReady
      primitivePacketRealizedReady := datum.primitivePacketRealizedReady
      packetFaithfulReady := datum.packetFaithfulReady }

/-- The branch-local witness datum already fixes the rank-two support witness
and every later readiness clause consumed by the generic local compiler. -/
theorem supportSurface
    {Channel Horizon Scalar : Type}
    {primitive : TwoChannelPrimitiveDatum Channel Scalar}
    (datum : BranchLocalSchurWitnessDatum
      (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar) primitive) :
    Nonempty (RankTwoTwoChannelSchurSupport datum.surface) := by
  exact datum.source.rankTwoSupport_nonempty

/-- The same branch-local witness datum first fixes the local cut readiness
surface read before the packet-faithful stage. -/
theorem projectiveStrictSurface
    {Channel Horizon Scalar : Type}
    {primitive : TwoChannelPrimitiveDatum Channel Scalar}
    (datum : BranchLocalSchurWitnessDatum
      (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar) primitive) :
    datum.compilerOutput.projectiveReady = datum.projectiveReady ∧
      datum.compilerOutput.strictReady = datum.strictReady := by
  exact ⟨rfl, rfl⟩

/-- The same branch-local witness datum also fixes the distinguished-cut clause
inside the local cut readiness surface. -/
theorem distinguishedCutSurface
    {Channel Horizon Scalar : Type}
    {primitive : TwoChannelPrimitiveDatum Channel Scalar}
    (datum : BranchLocalSchurWitnessDatum
      (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar) primitive) :
    datum.compilerOutput.distinguishedCutReady = datum.distinguishedCutReady := by
  rfl

/-- The same branch-local witness datum first fixes the local cut readiness
surface read before the packet-faithful stage. -/
theorem localCutReadinessSurface
    {Channel Horizon Scalar : Type}
    {primitive : TwoChannelPrimitiveDatum Channel Scalar}
    (datum : BranchLocalSchurWitnessDatum
      (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar) primitive) :
    datum.compilerOutput.projectiveReady = datum.projectiveReady ∧
      datum.compilerOutput.strictReady = datum.strictReady ∧
      datum.compilerOutput.distinguishedCutReady = datum.distinguishedCutReady := by
  exact
    ⟨(datum.projectiveStrictSurface).1,
      (datum.projectiveStrictSurface).2,
      datum.distinguishedCutSurface⟩

/-- It then fixes the later ordered-packet, realized-packet, and packet-faithful
readiness surface on the same local cut. -/
theorem orderedRealizedPacketSurface
    {Channel Horizon Scalar : Type}
    {primitive : TwoChannelPrimitiveDatum Channel Scalar}
    (datum : BranchLocalSchurWitnessDatum
      (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar) primitive) :
    datum.compilerOutput.orderedPrimitivePacketReady = datum.orderedPrimitivePacketReady ∧
      datum.compilerOutput.primitivePacketRealizedReady =
        datum.primitivePacketRealizedReady := by
  exact ⟨rfl, rfl⟩

/-- It also fixes the packet-faithful clause read at the end of the same local
cut. -/
theorem packetFaithfulSurface
    {Channel Horizon Scalar : Type}
    {primitive : TwoChannelPrimitiveDatum Channel Scalar}
    (datum : BranchLocalSchurWitnessDatum
      (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar) primitive) :
    datum.compilerOutput.packetFaithfulReady = datum.packetFaithfulReady := by
  rfl

/-- It then fixes the later ordered-packet, realized-packet, and packet-faithful
readiness surface on the same local cut. -/
theorem packetReadinessSurface
    {Channel Horizon Scalar : Type}
    {primitive : TwoChannelPrimitiveDatum Channel Scalar}
    (datum : BranchLocalSchurWitnessDatum
      (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar) primitive) :
    datum.compilerOutput.orderedPrimitivePacketReady = datum.orderedPrimitivePacketReady ∧
      datum.compilerOutput.primitivePacketRealizedReady =
        datum.primitivePacketRealizedReady ∧
      datum.compilerOutput.packetFaithfulReady = datum.packetFaithfulReady := by
  exact
    ⟨(datum.orderedRealizedPacketSurface).1,
      (datum.orderedRealizedPacketSurface).2,
      datum.packetFaithfulSurface⟩

/-- The branch-local witness datum also fixes every readiness clause consumed
by the generic local compiler once the rank-two support witness is in place. -/
theorem readinessSurface
    {Channel Horizon Scalar : Type}
    {primitive : TwoChannelPrimitiveDatum Channel Scalar}
    (datum : BranchLocalSchurWitnessDatum
      (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar) primitive) :
    datum.compilerOutput.projectiveReady = datum.projectiveReady ∧
      datum.compilerOutput.strictReady = datum.strictReady ∧
      datum.compilerOutput.distinguishedCutReady = datum.distinguishedCutReady ∧
      datum.compilerOutput.orderedPrimitivePacketReady = datum.orderedPrimitivePacketReady ∧
      datum.compilerOutput.primitivePacketRealizedReady =
        datum.primitivePacketRealizedReady ∧
      datum.compilerOutput.packetFaithfulReady = datum.packetFaithfulReady := by
  have hcut := datum.localCutReadinessSurface
  have hpacket := datum.packetReadinessSurface
  rcases hcut with ⟨hprojective, hstrict, hcutReady⟩
  rcases hpacket with ⟨hordered, hrealized, hfaithful⟩
  exact ⟨hprojective, hstrict, hcutReady, hordered, hrealized, hfaithful⟩

/-- The branch-local witness datum already fixes the rank-two support witness
and every later readiness clause consumed by the generic local compiler. -/
theorem compilerSurface
    {Channel Horizon Scalar : Type}
    {primitive : TwoChannelPrimitiveDatum Channel Scalar}
    (datum : BranchLocalSchurWitnessDatum
      (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar) primitive) :
    Nonempty (RankTwoTwoChannelSchurSupport datum.surface) ∧
      datum.compilerOutput.projectiveReady = datum.projectiveReady ∧
      datum.compilerOutput.strictReady = datum.strictReady ∧
      datum.compilerOutput.distinguishedCutReady = datum.distinguishedCutReady ∧
      datum.compilerOutput.orderedPrimitivePacketReady = datum.orderedPrimitivePacketReady ∧
      datum.compilerOutput.primitivePacketRealizedReady =
        datum.primitivePacketRealizedReady ∧
      datum.compilerOutput.packetFaithfulReady = datum.packetFaithfulReady := by
  have hcut := datum.localCutReadinessSurface
  have hpacket := datum.packetReadinessSurface
  rcases hcut with ⟨hprojective, hstrict, hcutReady⟩
  rcases hpacket with ⟨hordered, hrealized, hfaithful⟩
  exact
    ⟨datum.supportSurface,
      hprojective,
      hstrict,
      hcutReady,
      hordered,
      hrealized,
      hfaithful⟩

/-- The branch-local witness datum already carries both the compiler readout
surface and the local compiler object itself. -/
theorem witnessSurface
    {Channel Horizon Scalar : Type}
    {primitive : TwoChannelPrimitiveDatum Channel Scalar}
    (datum : BranchLocalSchurWitnessDatum
      (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar) primitive) :
    (Nonempty (RankTwoTwoChannelSchurSupport datum.surface) ∧
        datum.compilerOutput.projectiveReady = datum.projectiveReady ∧
        datum.compilerOutput.strictReady = datum.strictReady ∧
        datum.compilerOutput.distinguishedCutReady = datum.distinguishedCutReady ∧
        datum.compilerOutput.orderedPrimitivePacketReady = datum.orderedPrimitivePacketReady ∧
        datum.compilerOutput.primitivePacketRealizedReady =
          datum.primitivePacketRealizedReady ∧
        datum.compilerOutput.packetFaithfulReady = datum.packetFaithfulReady) ∧
      Nonempty (LocalSchurCompilerOutput datum.surface) := by
  exact ⟨datum.compilerSurface, ⟨datum.compilerOutput⟩⟩

/-- After the branch supplies its local witness datum, the generic local
two-channel compiler can be reused without any further branch-specific local
Schur algebra. -/
theorem compilerOutput_nonempty
    {Channel Horizon Scalar : Type}
    {primitive : TwoChannelPrimitiveDatum Channel Scalar}
    (datum : BranchLocalSchurWitnessDatum
      (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar) primitive) :
    Nonempty (LocalSchurCompilerOutput datum.surface) := by
  exact ⟨datum.compilerOutput⟩

/-- Once the local witness datum exists, the branch's local Schur reduction is
entirely witness-driven. -/
theorem witnessDrivenReduction
    {Channel Horizon Scalar : Type}
    {primitive : TwoChannelPrimitiveDatum Channel Scalar}
    (datum : BranchLocalSchurWitnessDatum
      (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar) primitive) :
    Nonempty (LocalSchurCompilerOutput datum.surface) := by
  exact datum.compilerOutput_nonempty

end BranchLocalSchurWitnessDatum

end CoherenceCalculus
