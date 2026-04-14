import CoherenceCalculus.PartIV.ClosureCurrentFlagshipBridgeCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentFlagshipBoundaryCore

Sharp law-native boundary for the textbook flagship lanes.

`ClosureCurrentFlagshipBridgeCore` already removes all external matching data:
the no-stage completion law reconstructs its own selected bundle and active
completion surface, and the recognizable phase / wave / gauge / geometric
identities follow once the corresponding endpoint frontiers are read on that
same intrinsically selected bundle.

This file isolates that remaining seam explicitly. It does not claim that the
lane-specific endpoint frontier witnesses are already produced by the common
law-native completion package. Instead, it records the exact stronger statement
now justified on the public surface:

* the active Part IV completion surface is already internal to the no-stage
  completion law;
* the only remaining explicit flagship inputs are the four endpoint frontier
  witness bundles on that same law-native selected bundle.
-/

namespace ClosureCurrent

/-- Exact remaining phase endpoint witness data above the law-native selected
bundle. This splits the previous phase frontier into the endpoint-collapse
package plus the two auxiliary Chapter 5 / 7 corollary witnesses it still
needs. -/
structure PhaseEndpointWitness
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) where
  Field : Type
  Scalar : Type
  Channel : Type
  transportBase : AddMap
  selectedProjection : Projection
  collapse : PhaseLane.EndpointCollapse Time Carrier Law Field Scalar
  phaseCompatibleTower :
    PhaseCompatibleSchurTowerData transportBase selectedProjection
  observableScalarization :
    RealizedSelfAdjointScalarizationData Index Time Channel
  readOnSelectedBundle :
    data.selectedBundle.phaseCarrierReadOnSelectedBundle
      collapse.law.observer

/-- Exact remaining wave endpoint witness data above the law-native selected
bundle. This makes the nested wave frontier explicit as endpoint collapse,
transport generation, local internal datum, scalar recursion, and admissible
transport. -/
structure WaveEndpointWitness
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) where
  Field : Type
  Scalar : Type
  System : Type
  Vertex : Type
  PhaseClass : Type
  ClosureClass : Type
  WaveIndex : Type
  tower : HorizonTower
  collapse : WaveLane.EndpointCollapse Time Carrier Law Field Scalar
  selectedTransportGeneration :
    SelectedChannelTransportGenerationData System
  transportGeneratedScalarRecursive :
    TransportGeneratedScalarRecursiveData Time Vertex
  localInternalDatum :
    RealizedLocalInternalDatumForcingData
      PhaseClass Scalar ClosureClass
  admissibleTransport :
    TransportGeneratedAdmissibleFamily WaveIndex tower
  readOnSelectedBundle :
    data.selectedBundle.waveCarrierReadOnSelectedBundle
      collapse.law.observer

/-- Exact remaining gauge endpoint witness data above the law-native selected
bundle. -/
structure GaugeEndpointWitness
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) where
  Field : Type
  Source : Type
  Vertex : Type
  collapse : GaugeLane.EndpointCollapse Time Carrier Law Field Source
  selectedGaugeCovariance :
    SelectedChannelGaugeCovarianceData Time Vertex
  readOnSelectedBundle :
    data.selectedBundle.gaugeCarrierReadOnSelectedBundle
      collapse.law.observer

/-- Exact remaining geometric endpoint witness data above the law-native
selected bundle. -/
structure GeometricEndpointWitness
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) where
  Tensor : Type
  Scalar : Type
  Group : Type
  collapse : GeometricLane.EndpointCollapse Time Carrier Law Tensor Scalar
  symmetricTensorScalarization :
    Compiler.OrthogonalSymmetricTensorScalarizationData Scalar Tensor Group
  readOnSelectedBundle :
    data.selectedBundle.geometricCarrierReadOnSelectedBundle
      collapse.law.observer

/-- Aggregate exact endpoint witness package for the four textbook flagship
lanes on the law-native selected bundle. -/
structure FlagshipEndpointWitnesses
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) where
  phase : PhaseEndpointWitness data
  wave : WaveEndpointWitness data
  gauge : GaugeEndpointWitness data
  geometric : GeometricEndpointWitness data

/-- Repackage exact phase endpoint witness data into the existing frontier
interface. -/
def PhaseEndpointWitness.toFrontier
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateCompletionLaw Index Time Carrier Law}
    (witness : PhaseEndpointWitness data) :
    PhaseFrontier (Index := Index) data where
  Field := witness.Field
  Scalar := witness.Scalar
  Channel := witness.Channel
  frontier := {
    collapse := witness.collapse
    transportBase := witness.transportBase
    selectedProjection := witness.selectedProjection
    phaseCompatibleTower := witness.phaseCompatibleTower
    observableScalarization := witness.observableScalarization
  }
  readOnSelectedBundle := witness.readOnSelectedBundle

/-- Repackage a phase frontier back into the exact endpoint-witness form. -/
def PhaseFrontier.toEndpointWitness
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateCompletionLaw Index Time Carrier Law}
    (frontier : PhaseFrontier (Index := Index) data) :
    PhaseEndpointWitness data where
  Field := frontier.Field
  Scalar := frontier.Scalar
  Channel := frontier.Channel
  transportBase := frontier.frontier.transportBase
  selectedProjection := frontier.frontier.selectedProjection
  collapse := frontier.frontier.collapse
  phaseCompatibleTower := frontier.frontier.phaseCompatibleTower
  observableScalarization := frontier.frontier.observableScalarization
  readOnSelectedBundle := frontier.readOnSelectedBundle

/-- Repackage exact wave endpoint witness data into the existing frontier
interface. -/
def WaveEndpointWitness.toFrontier
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateCompletionLaw Index Time Carrier Law}
    (witness : WaveEndpointWitness data) :
    WaveFrontier (Index := Index) data where
  Field := witness.Field
  Scalar := witness.Scalar
  System := witness.System
  Vertex := witness.Vertex
  PhaseClass := witness.PhaseClass
  ClosureClass := witness.ClosureClass
  WaveIndex := witness.WaveIndex
  tower := witness.tower
  frontier := {
    frontier := {
      frontier := {
        collapse := witness.collapse
        selectedTransportGeneration := witness.selectedTransportGeneration
        transportGeneratedScalarRecursive := witness.transportGeneratedScalarRecursive
      }
      localInternalDatum := witness.localInternalDatum
    }
    admissibleTransport := witness.admissibleTransport
  }
  readOnSelectedBundle := witness.readOnSelectedBundle

/-- Repackage a wave frontier back into the exact endpoint-witness form. -/
def WaveFrontier.toEndpointWitness
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateCompletionLaw Index Time Carrier Law}
    (frontier : WaveFrontier (Index := Index) data) :
    WaveEndpointWitness data where
  Field := frontier.Field
  Scalar := frontier.Scalar
  System := frontier.System
  Vertex := frontier.Vertex
  PhaseClass := frontier.PhaseClass
  ClosureClass := frontier.ClosureClass
  WaveIndex := frontier.WaveIndex
  tower := frontier.tower
  collapse := frontier.frontier.frontier.frontier.collapse
  selectedTransportGeneration := frontier.frontier.frontier.frontier.selectedTransportGeneration
  transportGeneratedScalarRecursive := frontier.frontier.frontier.frontier.transportGeneratedScalarRecursive
  localInternalDatum := frontier.frontier.frontier.localInternalDatum
  admissibleTransport := frontier.frontier.admissibleTransport
  readOnSelectedBundle := frontier.readOnSelectedBundle

/-- Repackage exact gauge endpoint witness data into the existing frontier
interface. -/
def GaugeEndpointWitness.toFrontier
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateCompletionLaw Index Time Carrier Law}
    (witness : GaugeEndpointWitness data) :
    GaugeFrontier (Index := Index) data where
  Field := witness.Field
  Source := witness.Source
  Vertex := witness.Vertex
  frontier := {
    collapse := witness.collapse
    selectedGaugeCovariance := witness.selectedGaugeCovariance
  }
  readOnSelectedBundle := witness.readOnSelectedBundle

/-- Repackage a gauge frontier back into the exact endpoint-witness form. -/
def GaugeFrontier.toEndpointWitness
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateCompletionLaw Index Time Carrier Law}
    (frontier : GaugeFrontier (Index := Index) data) :
    GaugeEndpointWitness data where
  Field := frontier.Field
  Source := frontier.Source
  Vertex := frontier.Vertex
  collapse := frontier.frontier.collapse
  selectedGaugeCovariance := frontier.frontier.selectedGaugeCovariance
  readOnSelectedBundle := frontier.readOnSelectedBundle

/-- Repackage exact geometric endpoint witness data into the existing frontier
interface. -/
def GeometricEndpointWitness.toFrontier
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateCompletionLaw Index Time Carrier Law}
    (witness : GeometricEndpointWitness data) :
    GeometricFrontier (Index := Index) data where
  Tensor := witness.Tensor
  Scalar := witness.Scalar
  Group := witness.Group
  frontier := {
    collapse := witness.collapse
    symmetricTensorScalarization := witness.symmetricTensorScalarization
  }
  readOnSelectedBundle := witness.readOnSelectedBundle

/-- Repackage a geometric frontier back into the exact endpoint-witness form.
-/
def GeometricFrontier.toEndpointWitness
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateCompletionLaw Index Time Carrier Law}
    (frontier : GeometricFrontier (Index := Index) data) :
    GeometricEndpointWitness data where
  Tensor := frontier.Tensor
  Scalar := frontier.Scalar
  Group := frontier.Group
  collapse := frontier.frontier.collapse
  symmetricTensorScalarization := frontier.frontier.symmetricTensorScalarization
  readOnSelectedBundle := frontier.readOnSelectedBundle

/-- Repackage the exact endpoint witness data into the coarser frontier bundle
used by the previous flagship bridge theorem. -/
def FlagshipEndpointWitnesses.toFrontiers
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateCompletionLaw Index Time Carrier Law}
    (witnesses : FlagshipEndpointWitnesses data) :
    FlagshipFrontiers data where
  phase := witnesses.phase.toFrontier
  wave := witnesses.wave.toFrontier
  gauge := witnesses.gauge.toFrontier
  geometric := witnesses.geometric.toFrontier

/-- Repackage the coarser frontier bundle back into the exact endpoint-witness
form. -/
def FlagshipFrontiers.toEndpointWitnesses
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateCompletionLaw Index Time Carrier Law}
    (frontiers : FlagshipFrontiers data) :
    FlagshipEndpointWitnesses data where
  phase := frontiers.phase.toEndpointWitness
  wave := frontiers.wave.toEndpointWitness
  gauge := frontiers.gauge.toEndpointWitness
  geometric := frontiers.geometric.toEndpointWitness

/-- Repackaging the exact endpoint witness bundle into frontiers and back does
nothing. -/
theorem FlagshipEndpointWitnesses.toFrontiers_toEndpointWitnesses
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateCompletionLaw Index Time Carrier Law}
    (witnesses : FlagshipEndpointWitnesses data) :
    witnesses.toFrontiers.toEndpointWitnesses = witnesses := by
  cases witnesses
  rfl

/-- Repackaging the frontier bundle into exact endpoint witnesses and back does
nothing. -/
theorem FlagshipFrontiers.toEndpointWitnesses_toFrontiers
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateCompletionLaw Index Time Carrier Law}
    (frontiers : FlagshipFrontiers data) :
    frontiers.toEndpointWitnesses.toFrontiers = frontiers := by
  cases frontiers
  rfl

/-- The no-stage completion law already reconstructs the active Part IV
completion surface on its own selected datum. Relative to that internal
completion surface, the remaining flagship burden is exactly the four
lane-specific endpoint frontier witness bundles read on the same law-native
selected bundle. -/
theorem LocalEventFourStateCompletionLaw.frontierBoundarySurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    PartIVLawCompletionStatement data.toNaturalOperatorCompletion ∧
      (∀ frontiers : FlagshipFrontiers data,
        Nonempty
          (PhaseLane.RecognizableIdentity
            Time Carrier Law frontiers.phase.Field frontiers.phase.Scalar) ∧
        Nonempty
          (WaveLane.RecognizableIdentity
            Time Carrier Law frontiers.wave.Field frontiers.wave.Scalar) ∧
        Nonempty
          (GaugeLane.RecognizableIdentity
            Time Carrier Law frontiers.gauge.Field frontiers.gauge.Source) ∧
        Nonempty
          (GeometricLane.RecognizableIdentity
            Time Carrier Law
              frontiers.geometric.Tensor
              frontiers.geometric.Scalar)) := by
  obtain
    ⟨_hbundle, _hsector, _hbedrock, _haut, _hfiber, _hstate, _hreduced,
      _hschur, hcompletion⟩ := data.attachedSurface
  refine ⟨hcompletion, ?_⟩
  intro frontiers
  have hphase := data.phaseSurface frontiers.phase
  have hwave := data.waveSurface frontiers.wave
  have hgauge := data.gaugeSurface frontiers.gauge
  have hgeometric := data.geometricSurface frontiers.geometric
  rcases hphase with ⟨_hphaseForced, hphaseRecognizable⟩
  rcases hwave with ⟨_hwaveForced, hwaveRecognizable⟩
  rcases hgauge with ⟨_hgaugeForced, hgaugeRecognizable⟩
  rcases hgeometric with ⟨_hgeometricForced, hgeometricRecognizable⟩
  rcases hphaseRecognizable with ⟨phaseWitness⟩
  rcases hwaveRecognizable with ⟨waveWitness⟩
  rcases hgaugeRecognizable with ⟨gaugeWitness⟩
  rcases hgeometricRecognizable with ⟨geometricWitness⟩
  exact
    ⟨⟨phaseWitness⟩,
      ⟨⟨waveWitness⟩,
        ⟨⟨gaugeWitness⟩,
          ⟨geometricWitness⟩⟩⟩⟩

/-- Sharper exact-boundary form of the remaining flagship seam. Once the
law-native completion surface has closed, the only remaining explicit data are
the four lane endpoint-collapse witnesses together with the minimal auxiliary
corollary packages needed to rebuild the native frontier theorems. -/
theorem LocalEventFourStateCompletionLaw.endpointWitnessBoundarySurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    PartIVLawCompletionStatement data.toNaturalOperatorCompletion ∧
      (∀ witnesses : FlagshipEndpointWitnesses data,
        Nonempty
          (PhaseLane.RecognizableIdentity
            Time Carrier Law
            witnesses.phase.Field
            witnesses.phase.Scalar) ∧
        Nonempty
          (WaveLane.RecognizableIdentity
            Time Carrier Law
            witnesses.wave.Field
            witnesses.wave.Scalar) ∧
        Nonempty
          (GaugeLane.RecognizableIdentity
            Time Carrier Law
            witnesses.gauge.Field
            witnesses.gauge.Source) ∧
        Nonempty
          (GeometricLane.RecognizableIdentity
            Time Carrier Law
            witnesses.geometric.Tensor
            witnesses.geometric.Scalar)) := by
  obtain ⟨hcompletion, hboundary⟩ := data.frontierBoundarySurface
  refine ⟨hcompletion, ?_⟩
  intro witnesses
  simpa [FlagshipEndpointWitnesses.toFrontiers] using
    hboundary witnesses.toFrontiers

end ClosureCurrent

end CoherenceCalculus
