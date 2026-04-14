import CoherenceCalculus.PartV.CoherentLocalSchurCore
import CoherenceCalculus.PartV.CoherentVisibilityCore
import CoherenceCalculus.PartV.BranchWitnessAdapterCore

/-!
# PartV.CoherentWitnessAdapterCore

Coherent specialization of the detached Part V witness-adapter surface.

This file packages the first coherent specialization of the generic branch
adapter layers:

- coherent dressed running witnesses
- coherent branch witness adapters
- forgetful passage back to the generic three-stage witness adapter
-/

namespace CoherenceCalculus

/-- A coherent dressed running witness package is just the coherent
specialization of the generic endpoint-witness and running-transport layers on
the first coherent packet. -/
structure CoherentDressedRunningWitnessPackage
    {Channel State Threshold Profile Scalar Horizon : Type}
    (interface : CoherentDirectReturnInterface Channel Scalar)
    (compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar) where
  compiler_primitive_exact : compiler.primitive = interface.primitive
  localWitness : CoherentLocalSchurWitnessDatum
    (Channel := Channel) (State := State) (Threshold := Threshold)
    (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface
  visibleBasis :
    VisibleCoherentScalarObservableBasis interface localWitness.surface
  endpointWitness : BranchEndpointWitnessDatum compiler
  packetFaithfulEndpointSource : Prop
  runningWitness : BranchRunningTransportWitnessDatum compiler endpointWitness

namespace CoherentDressedRunningWitnessPackage

def runningCompilerOutput
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (package : CoherentDressedRunningWitnessPackage
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface compiler) :
    BranchRunningTransportCompilerOutput := by
  exact package.runningWitness.compilerOutput

/-- The coherent dressed running package keeps exactly the generic running
readout carried by the underlying running witness. -/
theorem runningLawSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (package : CoherentDressedRunningWitnessPackage
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface compiler) :
    package.runningCompilerOutput.exactDiscreteRunningLaw =
        package.runningWitness.rawPacketFlowAndFineEndpointReady ∧
      package.runningCompilerOutput.packetFaithfulFixedSurface =
        package.runningWitness.rawPacketFlowAndFineEndpointReady := by
  exact package.runningWitness.runningLawSurface

/-- The same coherent package already fixes the endpoint-side criterion layer
on that running output. -/
theorem endpointCriterionSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (package : CoherentDressedRunningWitnessPackage
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface compiler) :
    package.runningCompilerOutput.fineEndpointCriterion =
        package.runningWitness.rawPacketFlowAndFineEndpointReady ∧
      package.runningCompilerOutput.dressedEndpointTrichotomy =
        package.runningWitness.rawPacketFlowAndFineEndpointReady ∧
      package.runningCompilerOutput.singletonEndpointCriterion =
        package.runningWitness.rawPacketFlowAndFineEndpointReady := by
  exact package.runningWitness.endpointCriterionSurface

/-- The same coherent package also keeps the later transport closure layer on
that running output. -/
theorem transportSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (package : CoherentDressedRunningWitnessPackage
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface compiler) :
    package.runningCompilerOutput.recursiveRigidityOrProjectiveGeneration =
        package.runningWitness.recursiveOrProjectiveReady ∧
      package.runningCompilerOutput.matrixOrContractiveTransport =
        package.runningWitness.matrixOrContractiveTransportReady ∧
      package.runningCompilerOutput.schurTransportClosing =
        package.runningWitness.schurTransportReady := by
  exact package.runningWitness.transportSurface

/-- The coherent dressed running package keeps exactly the generic running
readout carried by the underlying running witness. -/
theorem runningCompilerOutputSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (package : CoherentDressedRunningWitnessPackage
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface compiler) :
    package.runningCompilerOutput.exactDiscreteRunningLaw =
        package.runningWitness.rawPacketFlowAndFineEndpointReady ∧
      package.runningCompilerOutput.packetFaithfulFixedSurface =
        package.runningWitness.rawPacketFlowAndFineEndpointReady ∧
      package.runningCompilerOutput.fineEndpointCriterion =
        package.runningWitness.rawPacketFlowAndFineEndpointReady ∧
      package.runningCompilerOutput.dressedEndpointTrichotomy =
        package.runningWitness.rawPacketFlowAndFineEndpointReady ∧
      package.runningCompilerOutput.singletonEndpointCriterion =
        package.runningWitness.rawPacketFlowAndFineEndpointReady ∧
      package.runningCompilerOutput.recursiveRigidityOrProjectiveGeneration =
        package.runningWitness.recursiveOrProjectiveReady ∧
      package.runningCompilerOutput.matrixOrContractiveTransport =
        package.runningWitness.matrixOrContractiveTransportReady ∧
      package.runningCompilerOutput.schurTransportClosing =
        package.runningWitness.schurTransportReady := by
  have hlaw := package.runningLawSurface
  have hcriterion := package.endpointCriterionSurface
  have htransport := package.transportSurface
  rcases hlaw with ⟨hexact, hpacket⟩
  rcases hcriterion with ⟨hfine, hdressed, hsingle⟩
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

/-- The coherent dressed running package already carries both the running
readout surface and the corresponding generic running object. -/
theorem runningPackageSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (package : CoherentDressedRunningWitnessPackage
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface compiler) :
    (package.runningCompilerOutput.exactDiscreteRunningLaw =
        package.runningWitness.rawPacketFlowAndFineEndpointReady ∧
      package.runningCompilerOutput.packetFaithfulFixedSurface =
        package.runningWitness.rawPacketFlowAndFineEndpointReady ∧
      package.runningCompilerOutput.fineEndpointCriterion =
        package.runningWitness.rawPacketFlowAndFineEndpointReady ∧
      package.runningCompilerOutput.dressedEndpointTrichotomy =
        package.runningWitness.rawPacketFlowAndFineEndpointReady ∧
      package.runningCompilerOutput.singletonEndpointCriterion =
        package.runningWitness.rawPacketFlowAndFineEndpointReady ∧
      package.runningCompilerOutput.recursiveRigidityOrProjectiveGeneration =
        package.runningWitness.recursiveOrProjectiveReady ∧
      package.runningCompilerOutput.matrixOrContractiveTransport =
        package.runningWitness.matrixOrContractiveTransportReady ∧
      package.runningCompilerOutput.schurTransportClosing =
        package.runningWitness.schurTransportReady) ∧
      Nonempty BranchRunningTransportCompilerOutput := by
  exact ⟨package.runningCompilerOutputSurface, ⟨package.runningCompilerOutput⟩⟩

/-- The coherent dressed running package already determines the full generic
running surface on the coherent endpoint source. -/
theorem runningSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (package : CoherentDressedRunningWitnessPackage
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface compiler) :
    package.runningWitness.compilerOutput.exactDiscreteRunningLaw =
        package.runningWitness.rawPacketFlowAndFineEndpointReady ∧
      package.runningWitness.compilerOutput.packetFaithfulFixedSurface =
        package.runningWitness.rawPacketFlowAndFineEndpointReady ∧
      package.runningWitness.compilerOutput.fineEndpointCriterion =
        package.runningWitness.rawPacketFlowAndFineEndpointReady ∧
      package.runningWitness.compilerOutput.dressedEndpointTrichotomy =
        package.runningWitness.rawPacketFlowAndFineEndpointReady ∧
      package.runningWitness.compilerOutput.singletonEndpointCriterion =
        package.runningWitness.rawPacketFlowAndFineEndpointReady ∧
      package.runningWitness.compilerOutput.recursiveRigidityOrProjectiveGeneration =
        package.runningWitness.recursiveOrProjectiveReady ∧
      package.runningWitness.compilerOutput.matrixOrContractiveTransport =
        package.runningWitness.matrixOrContractiveTransportReady ∧
      package.runningWitness.compilerOutput.schurTransportClosing =
        package.runningWitness.schurTransportReady := by
  exact package.runningPackageSurface.1

/-- The coherent branch therefore acquires no separate running engine once the
coherent dressed running witness package has been supplied. -/
theorem runningCompilerOutput_nonempty
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (package : CoherentDressedRunningWitnessPackage
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface compiler) :
    Nonempty BranchRunningTransportCompilerOutput := by
  exact ⟨package.runningCompilerOutput⟩

end CoherentDressedRunningWitnessPackage

/-- The coherent branch witness adapter is the first specialization of the
generic witness-adapter interface. -/
structure CoherentBranchWitnessAdapterDatum
    {Channel State Threshold Profile Scalar Horizon : Type}
    (interface : CoherentDirectReturnInterface Channel Scalar)
    (compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar) where
  compiler_primitive_exact : compiler.primitive = interface.primitive
  primitiveWitness : BranchPrimitiveWitnessDatum compiler
  primitiveSearch :
    CoherentPrimitiveConstantSearchDatum
      Channel State Threshold Profile Scalar Horizon
  primitiveSearch_exact :
    primitiveSearch.surface.primitive = interface.primitive
  localWitness : CoherentLocalSchurWitnessDatum
    (Channel := Channel) (State := State) (Threshold := Threshold)
    (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface
  bridgeWitness : BranchBridgeWitnessDatum compiler
  endpointWitness : BranchEndpointWitnessDatum compiler

namespace CoherentBranchWitnessAdapterDatum

def toBranchWitnessAdapterDatum
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum : CoherentBranchWitnessAdapterDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface compiler) :
    BranchWitnessAdapterDatum compiler := by
  have localWitnessOnCompiler :
      BranchLocalSchurWitnessDatum
        (Channel := Channel) (Horizon := Horizon) (Scalar := Scalar)
        compiler.primitive := by
    simpa [datum.compiler_primitive_exact] using
      datum.localWitness.toBranchLocalWitnessDatum
  refine
    { primitiveWitness := datum.primitiveWitness
      localWitness := localWitnessOnCompiler
      bridgeWitness := datum.bridgeWitness
      endpointWitness := datum.endpointWitness }

/-- The coherent adapter carries the same generic mechanical output after
forgetting the coherent-only presentation. -/
def mechanicalOutput
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum : CoherentBranchWitnessAdapterDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface compiler) :
    ThreeStageBranchCompilerMechanicalOutput := by
  exact (datum.toBranchWitnessAdapterDatum).mechanicalOutput

/-- The coherent adapter therefore fixes the same primitive, bridge, and
endpoint outputs as the generic branch adapter. -/
theorem primitiveMechanicalSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum : CoherentBranchWitnessAdapterDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface compiler) :
    datum.mechanicalOutput.primitiveStageOutput =
      datum.primitiveWitness.primitiveStageOutput := by
  exact (datum.toBranchWitnessAdapterDatum).primitiveMechanicalSurface

theorem bridgeMechanicalSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum : CoherentBranchWitnessAdapterDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface compiler) :
    datum.mechanicalOutput.bareBridgeOutput =
      datum.bridgeWitness.bareBridgeOutput := by
  exact (datum.toBranchWitnessAdapterDatum).bridgeMechanicalSurface

theorem endpointMechanicalSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum : CoherentBranchWitnessAdapterDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface compiler) :
    datum.mechanicalOutput.dressedEndpointOutput =
      datum.endpointWitness.dressedEndpointOutput := by
  exact (datum.toBranchWitnessAdapterDatum).endpointMechanicalSurface

/-- The coherent adapter therefore fixes the same primitive, bridge, and
endpoint outputs as the generic branch adapter. -/
theorem mechanicalOutputSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum : CoherentBranchWitnessAdapterDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface compiler) :
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

/-- The coherent specialization already fixes the same primitive/bridge/endpoint
mechanical surface as the generic branch witness adapter. -/
theorem mechanicalSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum : CoherentBranchWitnessAdapterDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface compiler) :
    (datum.toBranchWitnessAdapterDatum).mechanicalOutput.primitiveStageOutput =
        datum.primitiveWitness.primitiveStageOutput ∧
      (datum.toBranchWitnessAdapterDatum).mechanicalOutput.bareBridgeOutput =
        datum.bridgeWitness.bareBridgeOutput ∧
      (datum.toBranchWitnessAdapterDatum).mechanicalOutput.dressedEndpointOutput =
        datum.endpointWitness.dressedEndpointOutput := by
  exact datum.mechanicalOutputSurface

/-- After the coherent adapter lift, the remaining branch-specific burden is
still exactly the generic primitive/local/bridge/endpoint witness production
package. -/
def remainingWitnessBurden
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum : CoherentBranchWitnessAdapterDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface compiler) :
    BranchWitnessAdapterDatum.RemainingBranchSpecificWitnessBurden := by
  exact (datum.toBranchWitnessAdapterDatum).remainingWitnessBurden

/-- The coherent remaining burden is exactly the generic remaining burden read
on the forgotten branch witness adapter. -/
theorem primitiveLocalWitnessSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum : CoherentBranchWitnessAdapterDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface compiler) :
    datum.remainingWitnessBurden.primitiveWitnessProduction =
        datum.primitiveWitness.primitiveStageOutput ∧
      datum.remainingWitnessBurden.localSchurWitnessProduction = True := by
  exact (datum.toBranchWitnessAdapterDatum).primitiveLocalWitnessSurface

theorem bridgeEndpointWitnessSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum : CoherentBranchWitnessAdapterDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface compiler) :
    datum.remainingWitnessBurden.bridgeWitnessProduction =
        datum.bridgeWitness.bridgeWitness ∧
      datum.remainingWitnessBurden.endpointWitnessProduction =
        datum.endpointWitness.compatibility := by
  exact (datum.toBranchWitnessAdapterDatum).bridgeEndpointWitnessSurface

/-- The coherent remaining burden is exactly the generic remaining burden read
on the forgotten branch witness adapter. -/
theorem remainingWitnessSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum : CoherentBranchWitnessAdapterDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface compiler) :
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

/-- The coherent branch witness adapter separates cleanly into the same
mechanical compiler surface and residual witness-production surface as the
generic branch adapter. -/
theorem adapterSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum : CoherentBranchWitnessAdapterDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface compiler) :
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
  exact ⟨datum.mechanicalOutputSurface, datum.remainingWitnessSurface⟩

/-- The coherent branch witness adapter already carries the full adapter
readout together with the coherent mechanical compiler object and the residual
branch-specific witness-production object. -/
theorem adapterWitnessSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum : CoherentBranchWitnessAdapterDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface compiler) :
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
      Nonempty BranchWitnessAdapterDatum.RemainingBranchSpecificWitnessBurden := by
  exact
    ⟨datum.adapterSurface,
      ⟨datum.mechanicalOutput⟩,
      ⟨datum.remainingWitnessBurden⟩⟩

/-- The coherent branch is therefore the first specialization of the generic
three-stage witness-adapter interface. -/
theorem mechanicalOutput_nonempty
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum : CoherentBranchWitnessAdapterDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface compiler) :
    Nonempty ThreeStageBranchCompilerMechanicalOutput := by
  exact ⟨datum.mechanicalOutput⟩

/-- The coherent specialization leaves exactly the same residual branch
witness-production burden as the generic adapter. -/
theorem remainingWitnessBurden_nonempty
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar}
    (datum : CoherentBranchWitnessAdapterDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface compiler) :
    Nonempty BranchWitnessAdapterDatum.RemainingBranchSpecificWitnessBurden := by
  exact ⟨datum.remainingWitnessBurden⟩

end CoherentBranchWitnessAdapterDatum

structure CoherentExactAlphaFacingAdapterDatum
    {Channel State Threshold Profile Scalar Horizon : Type}
    (interface : CoherentDirectReturnInterface Channel Scalar)
    (compiler : ThreeStageBranchCompilerDatum Channel Horizon Scalar) where
  adapter : CoherentBranchWitnessAdapterDatum
    (Channel := Channel) (State := State) (Threshold := Threshold)
    (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
    interface compiler
  exactEndpointRoute :
    adapter.endpointWitness.sourceForm =
      BranchEndpointSourceForm.eventIntegratedAtomicHorizon

end CoherenceCalculus
