import CoherenceCalculus.PartV.CoherentPrimitiveCore
import CoherenceCalculus.PartV.LocalSchurWitnessCore

/-!
# PartV.CoherentLocalSchurCore

Coherent specialization of the detached Part V local Schur witness surface.

This file reuses the generic two-channel witness layer on coherent local cuts
without adding new local algebra. Its public surface records only:

- the coherent-to-generic forgetful map
- coherent rank-two sources
- coherent local witness data
- reuse of the generic local compiler on the coherent specialization
-/

namespace CoherenceCalculus

/-- Forget the coherent-only threshold/profile decoration and keep only the
two-channel local surface used by the generic local compiler. -/
def coherentToTwoChannelSchurCandidateSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    (surface : CoherentSchurCandidateSurface
      Channel State Threshold Profile Scalar Horizon) :
    TwoChannelSchurCandidateSurface Channel Horizon Scalar := by
  refine
    { primitive := surface.primitive
      horizonCut := surface.horizonCut }

/-- A symmetry-rigid coherent gate is exactly a symmetry-rigid generic
two-channel gate on the coherent specialization. -/
structure SymmetryRigidTwoChannelCoherentSchurGate
    {Channel State Threshold Profile Scalar Horizon : Type}
    (surface : CoherentSchurCandidateSurface
      Channel State Threshold Profile Scalar Horizon) where
  genericGate :
    SymmetryRigidTwoChannelSchurGate
      (coherentToTwoChannelSchurCandidateSurface surface)

namespace SymmetryRigidTwoChannelCoherentSchurGate

/-- Symmetry-rigid coherent cuts force rank-two support by reuse of the generic
two-channel gate theorem. -/
def rankTwoSupport
    {Channel State Threshold Profile Scalar Horizon : Type}
    {surface : CoherentSchurCandidateSurface
      Channel State Threshold Profile Scalar Horizon}
    (gate : SymmetryRigidTwoChannelCoherentSchurGate surface) :
    RankTwoTwoChannelSchurSupport
      (coherentToTwoChannelSchurCandidateSurface surface) := by
  exact gate.genericGate.rankTwoSupportWitness

/-- Symmetry-rigid coherent cuts force rank-two support by reuse of the generic
two-channel gate theorem. -/
theorem rankTwoSupport_nonempty
    {Channel State Threshold Profile Scalar Horizon : Type}
    {surface : CoherentSchurCandidateSurface
      Channel State Threshold Profile Scalar Horizon}
    (gate : SymmetryRigidTwoChannelCoherentSchurGate surface) :
    Nonempty
      (RankTwoTwoChannelSchurSupport
        (coherentToTwoChannelSchurCandidateSurface surface)) := by
  exact ⟨gate.rankTwoSupport⟩

end SymmetryRigidTwoChannelCoherentSchurGate

/-- A mode-aligned coherent cut is exactly a transported multiplicity-free
two-channel mode gate on the coherent specialization. -/
structure ModeAlignedTwoChannelCoherentSchurCut
    {Channel State Threshold Profile Scalar Horizon : Type}
    (surface : CoherentSchurCandidateSurface
      Channel State Threshold Profile Scalar Horizon) where
  genericGate :
    TransportedMultiplicityFreeTwoChannelModeGate
      (coherentToTwoChannelSchurCandidateSurface surface)

namespace ModeAlignedTwoChannelCoherentSchurCut

/-- Mode-aligned coherent cuts likewise force rank-two support by the generic
two-channel mode-gate theorem. -/
def rankTwoSupport
    {Channel State Threshold Profile Scalar Horizon : Type}
    {surface : CoherentSchurCandidateSurface
      Channel State Threshold Profile Scalar Horizon}
    (cut : ModeAlignedTwoChannelCoherentSchurCut surface) :
    RankTwoTwoChannelSchurSupport
      (coherentToTwoChannelSchurCandidateSurface surface) := by
  exact cut.genericGate.rankTwoSupportWitness

/-- Mode-aligned coherent cuts likewise force rank-two support by the generic
two-channel mode-gate theorem. -/
theorem rankTwoSupport_nonempty
    {Channel State Threshold Profile Scalar Horizon : Type}
    {surface : CoherentSchurCandidateSurface
      Channel State Threshold Profile Scalar Horizon}
    (cut : ModeAlignedTwoChannelCoherentSchurCut surface) :
    Nonempty
      (RankTwoTwoChannelSchurSupport
        (coherentToTwoChannelSchurCandidateSurface surface)) := by
  exact ⟨cut.rankTwoSupport⟩

end ModeAlignedTwoChannelCoherentSchurCut

/-- The coherent local rank-two source is furnished either by the symmetry-rigid
coherent gate or by the mode-aligned coherent cut. -/
inductive CoherentLocalRankTwoSource
    {Channel State Threshold Profile Scalar Horizon : Type}
    (surface : CoherentSchurCandidateSurface
      Channel State Threshold Profile Scalar Horizon) where
  | symmetry
      (gate : SymmetryRigidTwoChannelCoherentSchurGate surface) :
      CoherentLocalRankTwoSource surface
  | modeAligned
      (cut : ModeAlignedTwoChannelCoherentSchurCut surface) :
      CoherentLocalRankTwoSource surface

/-- A coherent local Schur witness datum packages the coherent local surface,
its primitive compatibility with the first coherent packet, the local rank-two
source, and the later witness packages already certified there. -/
structure CoherentLocalSchurWitnessDatum
    {Channel State Threshold Profile Scalar Horizon : Type}
    (interface : CoherentDirectReturnInterface Channel Scalar) where
  surface : CoherentSchurCandidateSurface
    Channel State Threshold Profile Scalar Horizon
  source : CoherentLocalRankTwoSource surface
  primitive_exact : surface.primitive = interface.primitive
  projectiveReady : Prop
  strictReady : Prop
  distinguishedCutReady : Prop
  orderedPrimitivePacketReady : Prop
  primitivePacketRealizedReady : Prop
  packetFaithfulReady : Prop

namespace CoherentLocalSchurWitnessDatum

/-- Forgetting the coherent-only presentation turns a coherent local Schur
witness datum into a generic branch-local witness datum on the same primitive
packet. -/
def toBranchLocalWitnessDatum
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface) :
    BranchLocalSchurWitnessDatum
      (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar)
      interface.primitive := by
  refine
    { surface := coherentToTwoChannelSchurCandidateSurface datum.surface
      source := ?_
      primitive_compatible := datum.primitive_exact
      projectiveReady := datum.projectiveReady
      strictReady := datum.strictReady
      distinguishedCutReady := datum.distinguishedCutReady
      orderedPrimitivePacketReady := datum.orderedPrimitivePacketReady
      primitivePacketRealizedReady := datum.primitivePacketRealizedReady
      packetFaithfulReady := datum.packetFaithfulReady }
  cases datum.source with
  | symmetry gate =>
      exact LocalRankTwoSource.symmetry gate.genericGate
  | modeAligned cut =>
      exact LocalRankTwoSource.mode cut.genericGate

/-- Coherent local Schur witnesses therefore reuse the generic local compiler
without adding coherent-only local algebra. -/
def compilerOutput
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface) :
    LocalSchurCompilerOutput
      (coherentToTwoChannelSchurCandidateSurface datum.surface) := by
  exact
    (datum.toBranchLocalWitnessDatum).compilerOutput

/-- On the coherent specialization, the local witness datum already fixes the
generic rank-two support and every later readiness clause on that same cut. -/
theorem supportSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface) :
    Nonempty
      (RankTwoTwoChannelSchurSupport
        (coherentToTwoChannelSchurCandidateSurface datum.surface)) := by
  cases datum.source with
  | symmetry gate =>
      exact gate.rankTwoSupport_nonempty
  | modeAligned cut =>
      exact cut.rankTwoSupport_nonempty

/-- On the coherent specialization, the local witness datum first fixes the
local cut readiness surface read before the packet-faithful stage. -/
theorem projectiveStrictSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface) :
    datum.compilerOutput.projectiveReady = datum.projectiveReady ∧
      datum.compilerOutput.strictReady = datum.strictReady := by
  exact ⟨rfl, rfl⟩

/-- On the coherent specialization, the same witness datum also fixes the
distinguished-cut clause inside the local cut readiness surface. -/
theorem distinguishedCutSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface) :
    datum.compilerOutput.distinguishedCutReady = datum.distinguishedCutReady := by
  rfl

/-- On the coherent specialization, the local witness datum first fixes the
local cut readiness surface read before the packet-faithful stage. -/
theorem localCutReadinessSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface) :
    datum.compilerOutput.projectiveReady = datum.projectiveReady ∧
      datum.compilerOutput.strictReady = datum.strictReady ∧
      datum.compilerOutput.distinguishedCutReady = datum.distinguishedCutReady := by
  exact
    ⟨(datum.projectiveStrictSurface).1,
      (datum.projectiveStrictSurface).2,
      datum.distinguishedCutSurface⟩

/-- It then fixes the later ordered-packet, realized-packet, and packet-faithful
readiness surface on that same coherent cut. -/
theorem orderedRealizedPacketSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface) :
    datum.compilerOutput.orderedPrimitivePacketReady = datum.orderedPrimitivePacketReady ∧
      datum.compilerOutput.primitivePacketRealizedReady =
        datum.primitivePacketRealizedReady := by
  exact ⟨rfl, rfl⟩

/-- On the coherent specialization, it also fixes the packet-faithful clause
read at the end of that same coherent cut. -/
theorem packetFaithfulSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface) :
    datum.compilerOutput.packetFaithfulReady = datum.packetFaithfulReady := by
  rfl

/-- It then fixes the later ordered-packet, realized-packet, and packet-faithful
readiness surface on that same coherent cut. -/
theorem packetReadinessSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface) :
    datum.compilerOutput.orderedPrimitivePacketReady = datum.orderedPrimitivePacketReady ∧
      datum.compilerOutput.primitivePacketRealizedReady =
        datum.primitivePacketRealizedReady ∧
      datum.compilerOutput.packetFaithfulReady = datum.packetFaithfulReady := by
  exact
    ⟨(datum.orderedRealizedPacketSurface).1,
      (datum.orderedRealizedPacketSurface).2,
      datum.packetFaithfulSurface⟩

/-- On the coherent specialization, the local witness datum also fixes every
later readiness clause read by the generic local compiler. -/
theorem readinessSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface) :
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

/-- On the coherent specialization, the local witness datum already fixes the
generic rank-two support and every later readiness clause on that same cut. -/
theorem compilerSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface) :
    Nonempty
      (RankTwoTwoChannelSchurSupport
        (coherentToTwoChannelSchurCandidateSurface datum.surface)) ∧
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

/-- The coherent local witness datum already carries both the coherent compiler
readout surface and the corresponding generic local compiler object. -/
theorem witnessSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface) :
    (Nonempty
        (RankTwoTwoChannelSchurSupport
          (coherentToTwoChannelSchurCandidateSurface datum.surface)) ∧
      datum.compilerOutput.projectiveReady = datum.projectiveReady ∧
      datum.compilerOutput.strictReady = datum.strictReady ∧
      datum.compilerOutput.distinguishedCutReady = datum.distinguishedCutReady ∧
      datum.compilerOutput.orderedPrimitivePacketReady = datum.orderedPrimitivePacketReady ∧
      datum.compilerOutput.primitivePacketRealizedReady =
        datum.primitivePacketRealizedReady ∧
      datum.compilerOutput.packetFaithfulReady = datum.packetFaithfulReady) ∧
      Nonempty
        (LocalSchurCompilerOutput
          (coherentToTwoChannelSchurCandidateSurface datum.surface)) := by
  exact ⟨datum.compilerSurface, ⟨datum.compilerOutput⟩⟩

/-- Coherent local Schur witnesses therefore reuse the generic local compiler
without adding coherent-only local algebra. -/
theorem compilerOutput_nonempty
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface) :
    Nonempty
      (LocalSchurCompilerOutput
        (coherentToTwoChannelSchurCandidateSurface datum.surface)) := by
  exact ⟨datum.compilerOutput⟩

/-- After the coherent local Schur lift, the remaining burden is only the
production of the coherent witness datum on the local surface. -/
theorem remainingWitnessBurden
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface) :
    Nonempty
      (LocalSchurCompilerOutput
        (coherentToTwoChannelSchurCandidateSurface datum.surface)) := by
  exact datum.compilerOutput_nonempty

end CoherentLocalSchurWitnessDatum

end CoherenceCalculus
