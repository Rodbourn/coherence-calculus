import CoherenceCalculus.PartV.LocalSchurWitnessCore

/-!
# PartV.BranchWitnessAdapterCore

Detached Part V witness-adapter surface for the generic three-stage branch
compiler.

This file records the branch-side witness packages that remain after the
generic local Schur layer is fixed:

- endpoint-source forms
- running-transport witness data
- witness adapters into the generic three-stage compiler
- the residual branch-specific witness burden after that lift
-/

namespace CoherenceCalculus

inductive BranchEndpointSourceForm where
  | earliestClosure
  | closureReduction
  | shellBenchmark
  | visibleCountThree
  | exactCapacity
  | constantTransport
  | eventIntegratedAtomicHorizon
  | exactGreenEvent
  | dressedResummation

/-- The generic three-stage compiler keeps only the forced primitive packet and
the distinguished horizon on which the later bridge and endpoint witnesses are
read. -/
structure ThreeStageBranchCompilerDatum (Channel Horizon Scalar : Type) where
  primitive : TwoChannelPrimitiveDatum Channel Scalar
  distinguishedHorizon : Horizon

structure BranchPrimitiveWitnessDatum
    {Channel Horizon Scalar : Type}
    (compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar) where
  primitive_exact : compiler.primitive = compiler.primitive
  primitiveStageOutput : Prop

structure BranchBridgeWitnessDatum
    {Channel Horizon Scalar : Type}
    (compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar) where
  bridgeWitness : Prop
  bareBridgeOutput : Prop

structure BranchEndpointWitnessDatum
    {Channel Horizon Scalar : Type}
    (compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar) where
  endpointSource : Type
  compatibility : Prop
  sourceForm : BranchEndpointSourceForm
  dressedEndpointOutput : Prop

structure BranchEventIntegratedAtomicHorizonEndpointWitnessDatum
    {Channel Horizon Scalar : Type}
    (compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar) where
  endpointWitness : BranchEndpointWitnessDatum compiler
  exactSourceForm :
    endpointWitness.sourceForm =
      BranchEndpointSourceForm.eventIntegratedAtomicHorizon

/-- Running transport witness production records exactly which generic dressed
running layers the same certified endpoint source realizes. -/
structure BranchRunningTransportWitnessDatum
    {Channel Horizon Scalar : Type}
    (compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar)
    (endpointWitness : BranchEndpointWitnessDatum compiler) where
  rawPacketFlowAndFineEndpointReady : Prop
  recursiveOrProjectiveReady : Prop
  matrixOrContractiveTransportReady : Prop
  schurTransportReady : Prop

structure BranchRunningTransportCompilerOutput where
  exactDiscreteRunningLaw : Prop
  packetFaithfulFixedSurface : Prop
  fineEndpointCriterion : Prop
  dressedEndpointTrichotomy : Prop
  singletonEndpointCriterion : Prop
  recursiveRigidityOrProjectiveGeneration : Prop
  matrixOrContractiveTransport : Prop
  schurTransportClosing : Prop

namespace BranchRunningTransportWitnessDatum

def compilerOutput
    {Channel Horizon Scalar : Type}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    {endpointWitness : BranchEndpointWitnessDatum compiler}
    (witness :
      BranchRunningTransportWitnessDatum compiler endpointWitness) :
    BranchRunningTransportCompilerOutput := by
  exact
    { exactDiscreteRunningLaw := witness.rawPacketFlowAndFineEndpointReady
      packetFaithfulFixedSurface := witness.rawPacketFlowAndFineEndpointReady
      fineEndpointCriterion := witness.rawPacketFlowAndFineEndpointReady
      dressedEndpointTrichotomy := witness.rawPacketFlowAndFineEndpointReady
      singletonEndpointCriterion := witness.rawPacketFlowAndFineEndpointReady
      recursiveRigidityOrProjectiveGeneration := witness.recursiveOrProjectiveReady
      matrixOrContractiveTransport := witness.matrixOrContractiveTransportReady
      schurTransportClosing := witness.schurTransportReady }

/-- The running-transport witness already fixes the full generic running
surface read by the three-stage compiler. -/
theorem runningLawSurface
    {Channel Horizon Scalar : Type}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    {endpointWitness : BranchEndpointWitnessDatum compiler}
    (witness :
      BranchRunningTransportWitnessDatum compiler endpointWitness) :
    witness.compilerOutput.exactDiscreteRunningLaw =
        witness.rawPacketFlowAndFineEndpointReady ∧
      witness.compilerOutput.packetFaithfulFixedSurface =
        witness.rawPacketFlowAndFineEndpointReady := by
  exact ⟨rfl, rfl⟩

/-- The same endpoint head already fixes the later endpoint-side criterion
surface read by the generic three-stage compiler. -/
theorem endpointCriterionSurface
    {Channel Horizon Scalar : Type}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    {endpointWitness : BranchEndpointWitnessDatum compiler}
    (witness :
      BranchRunningTransportWitnessDatum compiler endpointWitness) :
    witness.compilerOutput.fineEndpointCriterion =
        witness.rawPacketFlowAndFineEndpointReady ∧
      witness.compilerOutput.dressedEndpointTrichotomy =
        witness.rawPacketFlowAndFineEndpointReady ∧
      witness.compilerOutput.singletonEndpointCriterion =
        witness.rawPacketFlowAndFineEndpointReady := by
  exact ⟨rfl, rfl, rfl⟩

/-- The running-transport witness already fixes the full generic running
surface read by the three-stage compiler. -/
theorem endpointSurface
    {Channel Horizon Scalar : Type}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    {endpointWitness : BranchEndpointWitnessDatum compiler}
    (witness :
      BranchRunningTransportWitnessDatum compiler endpointWitness) :
    witness.compilerOutput.exactDiscreteRunningLaw =
        witness.rawPacketFlowAndFineEndpointReady ∧
      witness.compilerOutput.packetFaithfulFixedSurface =
        witness.rawPacketFlowAndFineEndpointReady ∧
      witness.compilerOutput.fineEndpointCriterion =
        witness.rawPacketFlowAndFineEndpointReady ∧
      witness.compilerOutput.dressedEndpointTrichotomy =
        witness.rawPacketFlowAndFineEndpointReady ∧
      witness.compilerOutput.singletonEndpointCriterion =
        witness.rawPacketFlowAndFineEndpointReady := by
  have hlaw := witness.runningLawSurface
  have hcriterion := witness.endpointCriterionSurface
  rcases hlaw with ⟨hexact, hpacket⟩
  rcases hcriterion with ⟨hfine, hdressed, hsingle⟩
  exact ⟨hexact, hpacket, hfine, hdressed, hsingle⟩

/-- The same running-transport witness also fixes the later transport closure
surface on that endpoint source. -/
theorem transportSurface
    {Channel Horizon Scalar : Type}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    {endpointWitness : BranchEndpointWitnessDatum compiler}
    (witness :
      BranchRunningTransportWitnessDatum compiler endpointWitness) :
    witness.compilerOutput.recursiveRigidityOrProjectiveGeneration =
        witness.recursiveOrProjectiveReady ∧
      witness.compilerOutput.matrixOrContractiveTransport =
        witness.matrixOrContractiveTransportReady ∧
      witness.compilerOutput.schurTransportClosing =
        witness.schurTransportReady := by
  exact ⟨rfl, rfl, rfl⟩

/-- The running-transport witness already fixes the full generic running
surface read by the three-stage compiler. -/
theorem compilerSurface
    {Channel Horizon Scalar : Type}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    {endpointWitness : BranchEndpointWitnessDatum compiler}
    (witness :
      BranchRunningTransportWitnessDatum compiler endpointWitness) :
    witness.compilerOutput.exactDiscreteRunningLaw =
        witness.rawPacketFlowAndFineEndpointReady ∧
      witness.compilerOutput.packetFaithfulFixedSurface =
        witness.rawPacketFlowAndFineEndpointReady ∧
      witness.compilerOutput.fineEndpointCriterion =
        witness.rawPacketFlowAndFineEndpointReady ∧
      witness.compilerOutput.dressedEndpointTrichotomy =
        witness.rawPacketFlowAndFineEndpointReady ∧
      witness.compilerOutput.singletonEndpointCriterion =
        witness.rawPacketFlowAndFineEndpointReady ∧
      witness.compilerOutput.recursiveRigidityOrProjectiveGeneration =
        witness.recursiveOrProjectiveReady ∧
      witness.compilerOutput.matrixOrContractiveTransport =
        witness.matrixOrContractiveTransportReady ∧
      witness.compilerOutput.schurTransportClosing =
        witness.schurTransportReady := by
  have hendpoint := witness.endpointSurface
  have htransport := witness.transportSurface
  rcases hendpoint with
    ⟨hexact, hpacket, hfine, hdressed, hsingle⟩
  rcases htransport with
    ⟨hrecursive, hmatrix, hschur⟩
  exact
    ⟨hexact,
      hpacket,
      hfine,
      hdressed,
      hsingle,
      hrecursive,
      hmatrix,
      hschur⟩

/-- The running-transport witness already carries both the full compiler
readout surface and the corresponding generic running object. -/
theorem witnessSurface
    {Channel Horizon Scalar : Type}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    {endpointWitness : BranchEndpointWitnessDatum compiler}
    (witness :
      BranchRunningTransportWitnessDatum compiler endpointWitness) :
    (witness.compilerOutput.exactDiscreteRunningLaw =
        witness.rawPacketFlowAndFineEndpointReady ∧
      witness.compilerOutput.packetFaithfulFixedSurface =
        witness.rawPacketFlowAndFineEndpointReady ∧
      witness.compilerOutput.fineEndpointCriterion =
        witness.rawPacketFlowAndFineEndpointReady ∧
      witness.compilerOutput.dressedEndpointTrichotomy =
        witness.rawPacketFlowAndFineEndpointReady ∧
      witness.compilerOutput.singletonEndpointCriterion =
        witness.rawPacketFlowAndFineEndpointReady ∧
      witness.compilerOutput.recursiveRigidityOrProjectiveGeneration =
        witness.recursiveOrProjectiveReady ∧
      witness.compilerOutput.matrixOrContractiveTransport =
        witness.matrixOrContractiveTransportReady ∧
      witness.compilerOutput.schurTransportClosing =
        witness.schurTransportReady) ∧
      Nonempty BranchRunningTransportCompilerOutput := by
  exact ⟨witness.compilerSurface, ⟨witness.compilerOutput⟩⟩

/-- A branch running transport witness reuses the generic dressed endpoint
compiler on the same endpoint source. -/
theorem compilerOutput_nonempty
    {Channel Horizon Scalar : Type}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    {endpointWitness : BranchEndpointWitnessDatum compiler}
    (witness :
      BranchRunningTransportWitnessDatum compiler endpointWitness) :
    Nonempty BranchRunningTransportCompilerOutput := by
  exact ⟨witness.compilerOutput⟩

/-- After the running lift, the branch only certifies which generic running
layer its endpoint source realizes. -/
theorem witnessDrivenEndpoint
    {Channel Horizon Scalar : Type}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    {endpointWitness : BranchEndpointWitnessDatum compiler}
    (witness :
      BranchRunningTransportWitnessDatum compiler endpointWitness) :
    Nonempty BranchRunningTransportCompilerOutput := by
  exact witness.compilerOutput_nonempty

end BranchRunningTransportWitnessDatum

structure BranchWitnessAdapterDatum
    {Channel Horizon Scalar : Type}
    (compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar) where
  primitiveWitness : BranchPrimitiveWitnessDatum compiler
  localWitness :
    BranchLocalSchurWitnessDatum
      (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar)
      compiler.primitive
  bridgeWitness : BranchBridgeWitnessDatum compiler
  endpointWitness : BranchEndpointWitnessDatum compiler

structure ThreeStageBranchCompilerMechanicalOutput where
  primitiveStageOutput : Prop
  bareBridgeOutput : Prop
  dressedEndpointOutput : Prop

namespace BranchWitnessAdapterDatum

def mechanicalOutput
    {Channel Horizon Scalar : Type}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum :
      BranchWitnessAdapterDatum
        (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar)
        compiler) :
    ThreeStageBranchCompilerMechanicalOutput := by
  exact
    { primitiveStageOutput := datum.primitiveWitness.primitiveStageOutput
      bareBridgeOutput := datum.bridgeWitness.bareBridgeOutput
      dressedEndpointOutput := datum.endpointWitness.dressedEndpointOutput }

/-- Witness adapters instantiate the generic primitive, bridge, and endpoint
compiler outputs mechanically. -/
theorem mechanicalOutput_nonempty
    {Channel Horizon Scalar : Type}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum :
      BranchWitnessAdapterDatum
        (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar)
        compiler) :
    Nonempty ThreeStageBranchCompilerMechanicalOutput := by
  exact ⟨datum.mechanicalOutput⟩

structure RemainingBranchSpecificWitnessBurden where
  primitiveWitnessProduction : Prop
  localSchurWitnessProduction : Prop
  bridgeWitnessProduction : Prop
  endpointWitnessProduction : Prop

def remainingWitnessBurden
    {Channel Horizon Scalar : Type}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum :
      BranchWitnessAdapterDatum
        (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar)
        compiler) :
    RemainingBranchSpecificWitnessBurden := by
  exact
    { primitiveWitnessProduction := datum.primitiveWitness.primitiveStageOutput
      localSchurWitnessProduction := True
      bridgeWitnessProduction := datum.bridgeWitness.bridgeWitness
      endpointWitnessProduction := datum.endpointWitness.compatibility }

/-- The witness adapter mechanically fixes the primitive, bridge, and endpoint
outputs of the generic three-stage compiler. -/
theorem primitiveMechanicalSurface
    {Channel Horizon Scalar : Type}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum :
      BranchWitnessAdapterDatum
        (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar)
        compiler) :
    datum.mechanicalOutput.primitiveStageOutput =
      datum.primitiveWitness.primitiveStageOutput := by
  rfl

theorem bridgeMechanicalSurface
    {Channel Horizon Scalar : Type}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum :
      BranchWitnessAdapterDatum
        (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar)
        compiler) :
    datum.mechanicalOutput.bareBridgeOutput =
      datum.bridgeWitness.bareBridgeOutput := by
  rfl

theorem endpointMechanicalSurface
    {Channel Horizon Scalar : Type}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum :
      BranchWitnessAdapterDatum
        (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar)
        compiler) :
    datum.mechanicalOutput.dressedEndpointOutput =
      datum.endpointWitness.dressedEndpointOutput := by
  rfl

/-- The witness adapter mechanically fixes the primitive, bridge, and endpoint
outputs of the generic three-stage compiler. -/
theorem mechanicalSurface
    {Channel Horizon Scalar : Type}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum :
      BranchWitnessAdapterDatum
        (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar)
        compiler) :
    datum.mechanicalOutput.primitiveStageOutput =
        datum.primitiveWitness.primitiveStageOutput ∧
      datum.mechanicalOutput.bareBridgeOutput =
        datum.bridgeWitness.bareBridgeOutput ∧
      datum.mechanicalOutput.dressedEndpointOutput =
        datum.endpointWitness.dressedEndpointOutput := by
  exact
    ⟨datum.primitiveMechanicalSurface,
      datum.bridgeMechanicalSurface,
      datum.endpointMechanicalSurface⟩

/-- After the generic lift, the remaining branch-specific burden is exactly the
production of the primitive, local Schur, bridge, and endpoint witnesses. -/
theorem primitiveLocalWitnessSurface
    {Channel Horizon Scalar : Type}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum :
      BranchWitnessAdapterDatum
        (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar)
        compiler) :
    datum.remainingWitnessBurden.primitiveWitnessProduction =
        datum.primitiveWitness.primitiveStageOutput ∧
      datum.remainingWitnessBurden.localSchurWitnessProduction = True := by
  exact ⟨rfl, rfl⟩

theorem bridgeEndpointWitnessSurface
    {Channel Horizon Scalar : Type}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum :
      BranchWitnessAdapterDatum
        (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar)
        compiler) :
    datum.remainingWitnessBurden.bridgeWitnessProduction =
        datum.bridgeWitness.bridgeWitness ∧
      datum.remainingWitnessBurden.endpointWitnessProduction =
        datum.endpointWitness.compatibility := by
  exact ⟨rfl, rfl⟩

/-- After the generic lift, the remaining branch-specific burden is exactly the
production of the primitive, local Schur, bridge, and endpoint witnesses. -/
theorem remainingWitnessSurface
    {Channel Horizon Scalar : Type}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum :
      BranchWitnessAdapterDatum
        (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar)
        compiler) :
    datum.remainingWitnessBurden.primitiveWitnessProduction =
        datum.primitiveWitness.primitiveStageOutput ∧
      datum.remainingWitnessBurden.localSchurWitnessProduction = True ∧
      datum.remainingWitnessBurden.bridgeWitnessProduction =
        datum.bridgeWitness.bridgeWitness ∧
      datum.remainingWitnessBurden.endpointWitnessProduction =
        datum.endpointWitness.compatibility := by
  have hprim := datum.primitiveLocalWitnessSurface
  have hrest := datum.bridgeEndpointWitnessSurface
  rcases hprim with ⟨hprimitive, hlocal⟩
  rcases hrest with ⟨hbridge, hendpoint⟩
  exact ⟨hprimitive, hlocal, hbridge, hendpoint⟩

/-- The generic branch witness adapter separates cleanly into the mechanical
compiler surface and the residual branch-specific witness-production surface. -/
theorem adapterSurface
    {Channel Horizon Scalar : Type}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum :
      BranchWitnessAdapterDatum
        (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar)
        compiler) :
    (datum.mechanicalOutput.primitiveStageOutput =
        datum.primitiveWitness.primitiveStageOutput ∧
      datum.mechanicalOutput.bareBridgeOutput =
        datum.bridgeWitness.bareBridgeOutput ∧
      datum.mechanicalOutput.dressedEndpointOutput =
        datum.endpointWitness.dressedEndpointOutput) ∧
      (datum.remainingWitnessBurden.primitiveWitnessProduction =
          datum.primitiveWitness.primitiveStageOutput ∧
        datum.remainingWitnessBurden.localSchurWitnessProduction = True ∧
        datum.remainingWitnessBurden.bridgeWitnessProduction =
          datum.bridgeWitness.bridgeWitness ∧
        datum.remainingWitnessBurden.endpointWitnessProduction =
          datum.endpointWitness.compatibility) := by
  exact ⟨datum.mechanicalSurface, datum.remainingWitnessSurface⟩

/-- The generic branch witness adapter already carries the full adapter
readout together with the mechanical compiler object and the residual
branch-specific witness-production object. -/
theorem adapterWitnessSurface
    {Channel Horizon Scalar : Type}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum :
      BranchWitnessAdapterDatum
        (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar)
        compiler) :
    ((datum.mechanicalOutput.primitiveStageOutput =
        datum.primitiveWitness.primitiveStageOutput ∧
      datum.mechanicalOutput.bareBridgeOutput =
        datum.bridgeWitness.bareBridgeOutput ∧
      datum.mechanicalOutput.dressedEndpointOutput =
        datum.endpointWitness.dressedEndpointOutput) ∧
      (datum.remainingWitnessBurden.primitiveWitnessProduction =
          datum.primitiveWitness.primitiveStageOutput ∧
        datum.remainingWitnessBurden.localSchurWitnessProduction = True ∧
        datum.remainingWitnessBurden.bridgeWitnessProduction =
          datum.bridgeWitness.bridgeWitness ∧
        datum.remainingWitnessBurden.endpointWitnessProduction =
          datum.endpointWitness.compatibility)) ∧
      Nonempty ThreeStageBranchCompilerMechanicalOutput ∧
      Nonempty RemainingBranchSpecificWitnessBurden := by
  exact
    ⟨datum.adapterSurface,
      ⟨datum.mechanicalOutput⟩,
      ⟨datum.remainingWitnessBurden⟩⟩

/-- After the full generic lift, what remains branch-specific is only witness
production at the primitive, local Schur, bridge, and endpoint layers. -/
theorem remainingWitnessBurden_nonempty
    {Channel Horizon Scalar : Type}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum :
      BranchWitnessAdapterDatum
        (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar)
        compiler) :
    Nonempty RemainingBranchSpecificWitnessBurden := by
  exact ⟨datum.remainingWitnessBurden⟩

end BranchWitnessAdapterDatum

structure BranchExactAlphaFacingAdapterDatum
    {Channel Horizon Scalar : Type}
    (compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar) where
  adapter :
    BranchWitnessAdapterDatum
      (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar)
      compiler
  exactEndpointRoute :
    adapter.endpointWitness.sourceForm =
      BranchEndpointSourceForm.eventIntegratedAtomicHorizon

end CoherenceCalculus
