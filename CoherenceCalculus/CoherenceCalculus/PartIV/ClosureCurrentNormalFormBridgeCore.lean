import CoherenceCalculus.PartIV.ClosureCurrentCompletionBridgeCore
import CoherenceCalculus.PartIV.ClosureCurrentFlagshipBoundaryCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentNormalFormBridgeCore

Smaller bridge from split completion data to recognizable flagship normal
forms.

`ClosureCurrentCompletionBridgeCore` isolates a constructive bridge from the
detached current lane to a no-stage completion witness. The remaining open seam
on the flagship side is not the full endpoint witness bundle itself, but the
claim that one aligned completion package already forces the four recognizable
flagship forms. This file records the first honest bridge at that level:

* one split completion bridge on the detached current side;
* one phase, wave, gauge, and geometric sector-rigidity package on that same
  aligned completion.

From those data, the recognizable Schr\"odinger, wave/Klein--Gordon, Maxwell,
and Einstein identities already follow. Nothing here claims the common
completion law always forces those four sector-rigidity packages. It isolates
that remaining normal-form theorem exactly.
-/

namespace ClosureCurrent

/-- Phase-lane sector-rigidity package on the aligned completion datum carried
by one fixed completion bridge. -/
structure PhaseRigidityDatum
    (Index Time Carrier Law : Type)
    (completionBridge : NoStageCompletionBridge Index Time Carrier Law) where
  Field : Type
  Scalar : Type
  rigidity : PhaseLane.SectorRigidity Time Carrier Law Field Scalar
  usesCompletion :
    rigidity.orthogonalityRigidity.completion = completionBridge.completion

/-- Wave-lane sector-rigidity package on the aligned completion datum carried
by one fixed completion bridge. -/
structure WaveRigidityDatum
    (Index Time Carrier Law : Type)
    (completionBridge : NoStageCompletionBridge Index Time Carrier Law) where
  Field : Type
  Scalar : Type
  rigidity : WaveLane.SectorRigidity Time Carrier Law Field Scalar
  usesCompletion :
    rigidity.orthogonalityRigidity.completion = completionBridge.completion

/-- Gauge-lane sector-rigidity package on the aligned completion datum carried
by one fixed completion bridge. -/
structure GaugeRigidityDatum
    (Index Time Carrier Law : Type)
    (completionBridge : NoStageCompletionBridge Index Time Carrier Law) where
  Field : Type
  Source : Type
  rigidity : GaugeLane.SectorRigidity Time Carrier Law Field Source
  usesCompletion :
    rigidity.orthogonalityRigidity.completion = completionBridge.completion

/-- Geometric-lane sector-rigidity package on the aligned completion datum
carried by one fixed completion bridge. -/
structure GeometricRigidityDatum
    (Index Time Carrier Law : Type)
    (completionBridge : NoStageCompletionBridge Index Time Carrier Law) where
  Tensor : Type
  Scalar : Type
  rigidity : GeometricLane.SectorRigidity Time Carrier Law Tensor Scalar
  usesCompletion :
    rigidity.orthogonalityRigidity.completion = completionBridge.completion

/-- Exact phase-lane rigidity target above one fixed completion bridge. -/
def PhaseRigidityTarget
    {Index Time Carrier Law : Type}
    (completionBridge : NoStageCompletionBridge Index Time Carrier Law) : Prop :=
  Nonempty (PhaseRigidityDatum Index Time Carrier Law completionBridge)

/-- Exact wave-lane rigidity target above one fixed completion bridge. -/
def WaveRigidityTarget
    {Index Time Carrier Law : Type}
    (completionBridge : NoStageCompletionBridge Index Time Carrier Law) : Prop :=
  Nonempty (WaveRigidityDatum Index Time Carrier Law completionBridge)

/-- Exact gauge-lane rigidity target above one fixed completion bridge. -/
def GaugeRigidityTarget
    {Index Time Carrier Law : Type}
    (completionBridge : NoStageCompletionBridge Index Time Carrier Law) : Prop :=
  Nonempty (GaugeRigidityDatum Index Time Carrier Law completionBridge)

/-- Exact geometric-lane rigidity target above one fixed completion bridge. -/
def GeometricRigidityTarget
    {Index Time Carrier Law : Type}
    (completionBridge : NoStageCompletionBridge Index Time Carrier Law) : Prop :=
  Nonempty (GeometricRigidityDatum Index Time Carrier Law completionBridge)

/-- Smaller phase-lane normal-form datum above one fixed no-stage completion
witness. It keeps only the endpoint collapse on the witness's own selected
bundle together with the resulting recognizable Schrödinger identity. -/
structure PhaseRecognizableDatum
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law) where
  Field : Type
  Scalar : Type
  collapse : PhaseLane.EndpointCollapse Time Carrier Law Field Scalar
  readOnSelectedBundle :
    data.completionLaw.selectedBundle.phaseCarrierReadOnSelectedBundle
      collapse.law.observer
  recognizable :
    Nonempty (PhaseLane.RecognizableIdentity Time Carrier Law Field Scalar)

/-- Smaller wave-lane normal-form datum above one fixed no-stage completion
witness. It keeps only the endpoint collapse on the witness's own selected
bundle together with the resulting recognizable wave/Klein–Gordon identity. -/
structure WaveRecognizableDatum
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law) where
  Field : Type
  Scalar : Type
  collapse : WaveLane.EndpointCollapse Time Carrier Law Field Scalar
  readOnSelectedBundle :
    data.completionLaw.selectedBundle.waveCarrierReadOnSelectedBundle
      collapse.law.observer
  recognizable :
    Nonempty (WaveLane.RecognizableIdentity Time Carrier Law Field Scalar)

/-- Smaller gauge-lane normal-form datum above one fixed no-stage completion
witness. It keeps only the endpoint collapse on the witness's own selected
bundle together with the resulting recognizable Maxwell identity. -/
structure GaugeRecognizableDatum
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law) where
  Field : Type
  Source : Type
  collapse : GaugeLane.EndpointCollapse Time Carrier Law Field Source
  readOnSelectedBundle :
    data.completionLaw.selectedBundle.gaugeCarrierReadOnSelectedBundle
      collapse.law.observer
  recognizable :
    Nonempty (GaugeLane.RecognizableIdentity Time Carrier Law Field Source)

/-- Smaller geometric-lane normal-form datum above one fixed no-stage
completion witness. It keeps only the endpoint collapse on the witness's own
selected bundle together with the resulting recognizable Einstein identity. -/
structure GeometricRecognizableDatum
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law) where
  Tensor : Type
  Scalar : Type
  collapse : GeometricLane.EndpointCollapse Time Carrier Law Tensor Scalar
  readOnSelectedBundle :
    data.completionLaw.selectedBundle.geometricCarrierReadOnSelectedBundle
      collapse.law.observer
  recognizable :
    Nonempty (GeometricLane.RecognizableIdentity Time Carrier Law Tensor Scalar)

/-- Exact phase-lane recognizable target above one fixed no-stage completion
witness. -/
def PhaseRecognizableTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law) : Prop :=
  Nonempty (PhaseRecognizableDatum data)

/-- Exact wave-lane recognizable target above one fixed no-stage completion
witness. -/
def WaveRecognizableTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law) : Prop :=
  Nonempty (WaveRecognizableDatum data)

/-- Exact gauge-lane recognizable target above one fixed no-stage completion
witness. -/
def GaugeRecognizableTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law) : Prop :=
  Nonempty (GaugeRecognizableDatum data)

/-- Exact geometric-lane recognizable target above one fixed no-stage
completion witness. -/
def GeometricRecognizableTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law) : Prop :=
  Nonempty (GeometricRecognizableDatum data)

/-- Aggregate smaller recognizable flagship boundary target above one fixed
no-stage completion witness. It keeps only the four recognizable lane targets
on that witness's own selected bundle. -/
def FlagshipRecognizableBoundaryTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law) : Prop :=
  PhaseRecognizableTarget data ∧
    WaveRecognizableTarget data ∧
    GaugeRecognizableTarget data ∧
    GeometricRecognizableTarget data

/-- Exact phase-frontier target above one fixed no-stage completion witness.
This is the law-native input consumed by the completion-law phase surface. -/
def PhaseFrontierTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law) : Prop :=
  Nonempty (PhaseFrontier data.completionLaw)

/-- Exact wave-frontier target above one fixed no-stage completion witness.
This is the law-native input consumed by the completion-law wave surface. -/
def WaveFrontierTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law) : Prop :=
  Nonempty (WaveFrontier data.completionLaw)

/-- Exact gauge-frontier target above one fixed no-stage completion witness.
This is the law-native input consumed by the completion-law gauge surface. -/
def GaugeFrontierTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law) : Prop :=
  Nonempty (GaugeFrontier data.completionLaw)

/-- Exact geometric-frontier target above one fixed no-stage completion
witness. This is the law-native input consumed by the completion-law geometric
surface. -/
def GeometricFrontierTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law) : Prop :=
  Nonempty (GeometricFrontier data.completionLaw)

/-- Aggregate exact flagship boundary target above one fixed no-stage
completion witness. It records the four law-native frontier targets on that
same witness's own selected bundle. -/
def FlagshipBoundaryTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law) : Prop :=
  PhaseFrontierTarget data ∧
    WaveFrontierTarget data ∧
    GaugeFrontierTarget data ∧
    GeometricFrontierTarget data

/-- Aggregate exact flagship boundary target above one fixed no-stage
completion witness. It records the four exact lane-specific endpoint-witness
targets on that same witness. -/
def FlagshipExactBoundaryTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law) : Prop :=
  PhaseEndpointWitnessTarget data ∧
    WaveEndpointWitnessTarget data ∧
    GaugeEndpointWitnessTarget data ∧
    GeometricEndpointWitnessTarget data

/-- Split normal-form bridge above the detached completion bridge. The four
lane-specific sector-rigidity packages are required to live on the same
aligned active completion package carried by the completion bridge. -/
structure NormalFormBridge
    (Index Time Carrier Law : Type) where
  completionBridge : NoStageCompletionBridge Index Time Carrier Law
  PhaseField : Type
  PhaseScalar : Type
  phaseRigidity : PhaseLane.SectorRigidity Time Carrier Law PhaseField PhaseScalar
  phaseUsesCompletion :
    phaseRigidity.orthogonalityRigidity.completion =
      completionBridge.completion
  WaveField : Type
  WaveScalar : Type
  waveRigidity : WaveLane.SectorRigidity Time Carrier Law WaveField WaveScalar
  waveUsesCompletion :
    waveRigidity.orthogonalityRigidity.completion =
      completionBridge.completion
  GaugeField : Type
  GaugeSource : Type
  gaugeRigidity : GaugeLane.SectorRigidity Time Carrier Law GaugeField GaugeSource
  gaugeUsesCompletion :
    gaugeRigidity.orthogonalityRigidity.completion =
      completionBridge.completion
  GeometricTensor : Type
  GeometricScalar : Type
  geometricRigidity :
    GeometricLane.SectorRigidity
      Time Carrier Law GeometricTensor GeometricScalar
  geometricUsesCompletion :
    geometricRigidity.orthogonalityRigidity.completion =
      completionBridge.completion

namespace PhaseRigidityDatum

/-- Any actual phase-lane rigidity datum realizes the corresponding exact
phase target. -/
theorem target
    {Index Time Carrier Law : Type}
    {completionBridge : NoStageCompletionBridge Index Time Carrier Law}
    (data : PhaseRigidityDatum Index Time Carrier Law completionBridge) :
    PhaseRigidityTarget completionBridge := by
  exact ⟨data⟩

end PhaseRigidityDatum

namespace WaveRigidityDatum

/-- Any actual wave-lane rigidity datum realizes the corresponding exact wave
target. -/
theorem target
    {Index Time Carrier Law : Type}
    {completionBridge : NoStageCompletionBridge Index Time Carrier Law}
    (data : WaveRigidityDatum Index Time Carrier Law completionBridge) :
    WaveRigidityTarget completionBridge := by
  exact ⟨data⟩

end WaveRigidityDatum

namespace GaugeRigidityDatum

/-- Any actual gauge-lane rigidity datum realizes the corresponding exact gauge
target. -/
theorem target
    {Index Time Carrier Law : Type}
    {completionBridge : NoStageCompletionBridge Index Time Carrier Law}
    (data : GaugeRigidityDatum Index Time Carrier Law completionBridge) :
    GaugeRigidityTarget completionBridge := by
  exact ⟨data⟩

end GaugeRigidityDatum

namespace GeometricRigidityDatum

/-- Any actual geometric-lane rigidity datum realizes the corresponding exact
geometric target. -/
theorem target
    {Index Time Carrier Law : Type}
    {completionBridge : NoStageCompletionBridge Index Time Carrier Law}
    (data : GeometricRigidityDatum Index Time Carrier Law completionBridge) :
    GeometricRigidityTarget completionBridge := by
  exact ⟨data⟩

end GeometricRigidityDatum

namespace PhaseRecognizableDatum

/-- Any actual phase recognizable datum realizes the corresponding exact phase
normal-form target. -/
theorem target
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    {data : NoStageCompletionWitness law}
    (datum : PhaseRecognizableDatum data) :
    PhaseRecognizableTarget data := by
  exact ⟨datum⟩

end PhaseRecognizableDatum

namespace WaveRecognizableDatum

/-- Any actual wave recognizable datum realizes the corresponding exact wave
normal-form target. -/
theorem target
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    {data : NoStageCompletionWitness law}
    (datum : WaveRecognizableDatum data) :
    WaveRecognizableTarget data := by
  exact ⟨datum⟩

end WaveRecognizableDatum

namespace GaugeRecognizableDatum

/-- Any actual gauge recognizable datum realizes the corresponding exact gauge
normal-form target. -/
theorem target
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    {data : NoStageCompletionWitness law}
    (datum : GaugeRecognizableDatum data) :
    GaugeRecognizableTarget data := by
  exact ⟨datum⟩

end GaugeRecognizableDatum

namespace GeometricRecognizableDatum

/-- Any actual geometric recognizable datum realizes the corresponding exact
geometric normal-form target. -/
theorem target
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    {data : NoStageCompletionWitness law}
    (datum : GeometricRecognizableDatum data) :
    GeometricRecognizableTarget data := by
  exact ⟨datum⟩

end GeometricRecognizableDatum

namespace NoStageCompletionWitness

/-- An exact phase endpoint-witness target above one fixed no-stage completion
witness already realizes the corresponding law-native phase frontier target. -/
theorem phaseFrontierTargetOfEndpointTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hphase : PhaseEndpointWitnessTarget data) :
    PhaseFrontierTarget data := by
  rcases hphase with ⟨phase⟩
  exact ⟨phase.toFrontier⟩

/-- An exact wave endpoint-witness target above one fixed no-stage completion
witness already realizes the corresponding law-native wave frontier target. -/
theorem waveFrontierTargetOfEndpointTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hwave : WaveEndpointWitnessTarget data) :
    WaveFrontierTarget data := by
  rcases hwave with ⟨wave⟩
  exact ⟨wave.toFrontier⟩

/-- An exact gauge endpoint-witness target above one fixed no-stage completion
witness already realizes the corresponding law-native gauge frontier target. -/
theorem gaugeFrontierTargetOfEndpointTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hgauge : GaugeEndpointWitnessTarget data) :
    GaugeFrontierTarget data := by
  rcases hgauge with ⟨gauge⟩
  exact ⟨gauge.toFrontier⟩

/-- An exact geometric endpoint-witness target above one fixed no-stage
completion witness already realizes the corresponding law-native geometric
frontier target. -/
theorem geometricFrontierTargetOfEndpointTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hgeometric : GeometricEndpointWitnessTarget data) :
    GeometricFrontierTarget data := by
  rcases hgeometric with ⟨geometric⟩
  exact ⟨geometric.toFrontier⟩

/-- A law-native phase frontier target above one fixed no-stage completion
witness already realizes the corresponding exact phase endpoint-witness
target. -/
theorem phaseEndpointWitnessTargetOfFrontierTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hphase : PhaseFrontierTarget data) :
    PhaseEndpointWitnessTarget data := by
  rcases hphase with ⟨phase⟩
  exact ⟨phase.toEndpointWitness⟩

/-- A law-native wave frontier target above one fixed no-stage completion
witness already realizes the corresponding exact wave endpoint-witness
target. -/
theorem waveEndpointWitnessTargetOfFrontierTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hwave : WaveFrontierTarget data) :
    WaveEndpointWitnessTarget data := by
  rcases hwave with ⟨wave⟩
  exact ⟨wave.toEndpointWitness⟩

/-- A law-native gauge frontier target above one fixed no-stage completion
witness already realizes the corresponding exact gauge endpoint-witness
target. -/
theorem gaugeEndpointWitnessTargetOfFrontierTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hgauge : GaugeFrontierTarget data) :
    GaugeEndpointWitnessTarget data := by
  rcases hgauge with ⟨gauge⟩
  exact ⟨gauge.toEndpointWitness⟩

/-- A law-native geometric frontier target above one fixed no-stage completion
witness already realizes the corresponding exact geometric endpoint-witness
target. -/
theorem geometricEndpointWitnessTargetOfFrontierTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hgeometric : GeometricFrontierTarget data) :
    GeometricEndpointWitnessTarget data := by
  rcases hgeometric with ⟨geometric⟩
  exact ⟨geometric.toEndpointWitness⟩

/-- A phase frontier on the witness's own selected bundle already realizes the
smaller phase recognizable target. -/
theorem phaseRecognizableTargetOfFrontierTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hphase : PhaseFrontierTarget data) :
    PhaseRecognizableTarget data := by
  rcases hphase with ⟨frontier⟩
  have hsurface := data.completionLaw.phaseSurface frontier
  exact
    ⟨{ Field := frontier.Field
       Scalar := frontier.Scalar
       collapse := frontier.frontier.collapse
       readOnSelectedBundle := frontier.readOnSelectedBundle
       recognizable := hsurface.2 }⟩

/-- A wave frontier on the witness's own selected bundle already realizes the
smaller wave recognizable target. -/
theorem waveRecognizableTargetOfFrontierTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hwave : WaveFrontierTarget data) :
    WaveRecognizableTarget data := by
  rcases hwave with ⟨frontier⟩
  have hsurface := data.completionLaw.waveSurface frontier
  exact
    ⟨{ Field := frontier.Field
       Scalar := frontier.Scalar
       collapse := frontier.frontier.frontier.frontier.collapse
       readOnSelectedBundle := frontier.readOnSelectedBundle
       recognizable := hsurface.2 }⟩

/-- A gauge frontier on the witness's own selected bundle already realizes the
smaller gauge recognizable target. -/
theorem gaugeRecognizableTargetOfFrontierTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hgauge : GaugeFrontierTarget data) :
    GaugeRecognizableTarget data := by
  rcases hgauge with ⟨frontier⟩
  have hsurface := data.completionLaw.gaugeSurface frontier
  exact
    ⟨{ Field := frontier.Field
       Source := frontier.Source
       collapse := frontier.frontier.collapse
       readOnSelectedBundle := frontier.readOnSelectedBundle
       recognizable := hsurface.2 }⟩

/-- A geometric frontier on the witness's own selected bundle already realizes
the smaller geometric recognizable target. -/
theorem geometricRecognizableTargetOfFrontierTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hgeometric : GeometricFrontierTarget data) :
    GeometricRecognizableTarget data := by
  rcases hgeometric with ⟨frontier⟩
  have hsurface := data.completionLaw.geometricSurface frontier
  exact
    ⟨{ Tensor := frontier.Tensor
       Scalar := frontier.Scalar
       collapse := frontier.frontier.collapse
       readOnSelectedBundle := frontier.readOnSelectedBundle
       recognizable := hsurface.2 }⟩

/-- The four smaller recognizable lane targets package into one smaller
fixed-witness recognizable boundary target. -/
theorem flagshipRecognizableBoundaryTargetOfRecognizableTargets
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hphase : PhaseRecognizableTarget data)
    (hwave : WaveRecognizableTarget data)
    (hgauge : GaugeRecognizableTarget data)
    (hgeometric : GeometricRecognizableTarget data) :
    FlagshipRecognizableBoundaryTarget data := by
  exact ⟨hphase, hwave, hgauge, hgeometric⟩

/-- The four law-native frontier targets already realize the smaller
fixed-witness recognizable boundary target. -/
theorem flagshipRecognizableBoundaryTargetOfFrontierTargets
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hphase : PhaseFrontierTarget data)
    (hwave : WaveFrontierTarget data)
    (hgauge : GaugeFrontierTarget data)
    (hgeometric : GeometricFrontierTarget data) :
    FlagshipRecognizableBoundaryTarget data := by
  exact
    data.flagshipRecognizableBoundaryTargetOfRecognizableTargets
      (data.phaseRecognizableTargetOfFrontierTarget hphase)
      (data.waveRecognizableTargetOfFrontierTarget hwave)
      (data.gaugeRecognizableTargetOfFrontierTarget hgauge)
      (data.geometricRecognizableTargetOfFrontierTarget hgeometric)

/-- Four smaller recognizable lane targets above one fixed no-stage completion
witness already realize the direct normal-form target. -/
theorem normalFormTargetOfRecognizableTargets
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hphase : PhaseRecognizableTarget data)
    (hwave : WaveRecognizableTarget data)
    (hgauge : GaugeRecognizableTarget data)
    (hgeometric : GeometricRecognizableTarget data) :
    NormalFormTarget law := by
  rcases hphase with ⟨phase⟩
  rcases hwave with ⟨wave⟩
  rcases hgauge with ⟨gauge⟩
  rcases hgeometric with ⟨geometric⟩
  exact
    ⟨data,
      ⟨{ PhaseField := phase.Field
         PhaseScalar := phase.Scalar
         phase := phase.recognizable
         WaveField := wave.Field
         WaveScalar := wave.Scalar
         wave := wave.recognizable
         GaugeField := gauge.Field
         GaugeSource := gauge.Source
         gauge := gauge.recognizable
         GeometricTensor := geometric.Tensor
         GeometricScalar := geometric.Scalar
         geometric := geometric.recognizable }⟩⟩

/-- Surface theorem for the four smaller recognizable lane targets above one
fixed no-stage completion witness. -/
theorem normalFormTargetSurfaceOfRecognizableTargets
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hphase : PhaseRecognizableTarget data)
    (hwave : WaveRecognizableTarget data)
    (hgauge : GaugeRecognizableTarget data)
    (hgeometric : GeometricRecognizableTarget data) :
    ∃ normalForms : FlagshipNormalForms Time Carrier Law,
      data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
        data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          law.physicalPrinciple ∧
        PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
        Nonempty
          (PhaseLane.RecognizableIdentity
            Time Carrier Law
            normalForms.PhaseField
            normalForms.PhaseScalar) ∧
        Nonempty
          (WaveLane.RecognizableIdentity
            Time Carrier Law
            normalForms.WaveField
            normalForms.WaveScalar) ∧
        Nonempty
          (GaugeLane.RecognizableIdentity
            Time Carrier Law
            normalForms.GaugeField
            normalForms.GaugeSource) ∧
        Nonempty
          (GeometricLane.RecognizableIdentity
            Time Carrier Law
            normalForms.GeometricTensor
            normalForms.GeometricScalar) := by
  rcases hphase with ⟨phase⟩
  rcases hwave with ⟨wave⟩
  rcases hgauge with ⟨gauge⟩
  rcases hgeometric with ⟨geometric⟩
  let normalForms : FlagshipNormalForms Time Carrier Law :=
    { PhaseField := phase.Field
      PhaseScalar := phase.Scalar
      phase := phase.recognizable
      WaveField := wave.Field
      WaveScalar := wave.Scalar
      wave := wave.recognizable
      GaugeField := gauge.Field
      GaugeSource := gauge.Source
      gauge := gauge.recognizable
      GeometricTensor := geometric.Tensor
      GeometricScalar := geometric.Scalar
      geometric := geometric.recognizable }
  exact ⟨normalForms, data.normalFormSurface normalForms⟩

/-- A smaller fixed-witness recognizable boundary target already implies the
direct normal-form target. -/
theorem normalFormTargetOfRecognizableBoundaryTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hrecognizable : FlagshipRecognizableBoundaryTarget data) :
    NormalFormTarget law := by
  rcases hrecognizable with ⟨hphase, hwave, hgauge, hgeometric⟩
  exact
    data.normalFormTargetOfRecognizableTargets
      hphase hwave hgauge hgeometric

/-- Surface theorem for a smaller fixed-witness recognizable boundary target.
-/
theorem normalFormTargetSurfaceOfRecognizableBoundaryTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hrecognizable : FlagshipRecognizableBoundaryTarget data) :
    ∃ normalForms : FlagshipNormalForms Time Carrier Law,
      data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
        data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          law.physicalPrinciple ∧
        PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
        Nonempty
          (PhaseLane.RecognizableIdentity
            Time Carrier Law
            normalForms.PhaseField
            normalForms.PhaseScalar) ∧
        Nonempty
          (WaveLane.RecognizableIdentity
            Time Carrier Law
            normalForms.WaveField
            normalForms.WaveScalar) ∧
        Nonempty
          (GaugeLane.RecognizableIdentity
            Time Carrier Law
            normalForms.GaugeField
            normalForms.GaugeSource) ∧
        Nonempty
          (GeometricLane.RecognizableIdentity
            Time Carrier Law
            normalForms.GeometricTensor
            normalForms.GeometricScalar) := by
  rcases hrecognizable with ⟨hphase, hwave, hgauge, hgeometric⟩
  exact
    data.normalFormTargetSurfaceOfRecognizableTargets
      hphase hwave hgauge hgeometric

/-- Four law-native frontier targets above one fixed no-stage completion
witness already realize the direct normal-form target. -/
theorem normalFormTargetOfFrontierTargets
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hphase : PhaseFrontierTarget data)
    (hwave : WaveFrontierTarget data)
    (hgauge : GaugeFrontierTarget data)
    (hgeometric : GeometricFrontierTarget data) :
    NormalFormTarget law := by
  exact
    data.normalFormTargetOfRecognizableTargets
      (data.phaseRecognizableTargetOfFrontierTarget hphase)
      (data.waveRecognizableTargetOfFrontierTarget hwave)
      (data.gaugeRecognizableTargetOfFrontierTarget hgauge)
      (data.geometricRecognizableTargetOfFrontierTarget hgeometric)

/-- Surface theorem for the four law-native frontier targets above one fixed
no-stage completion witness. -/
theorem normalFormTargetSurfaceOfFrontierTargets
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hphase : PhaseFrontierTarget data)
    (hwave : WaveFrontierTarget data)
    (hgauge : GaugeFrontierTarget data)
    (hgeometric : GeometricFrontierTarget data) :
    ∃ normalForms : FlagshipNormalForms Time Carrier Law,
      data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
        data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          law.physicalPrinciple ∧
        PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
        Nonempty
          (PhaseLane.RecognizableIdentity
            Time Carrier Law
            normalForms.PhaseField
            normalForms.PhaseScalar) ∧
        Nonempty
          (WaveLane.RecognizableIdentity
            Time Carrier Law
            normalForms.WaveField
            normalForms.WaveScalar) ∧
        Nonempty
          (GaugeLane.RecognizableIdentity
            Time Carrier Law
            normalForms.GaugeField
            normalForms.GaugeSource) ∧
        Nonempty
          (GeometricLane.RecognizableIdentity
            Time Carrier Law
            normalForms.GeometricTensor
            normalForms.GeometricScalar) := by
  exact
    data.normalFormTargetSurfaceOfRecognizableTargets
      (data.phaseRecognizableTargetOfFrontierTarget hphase)
      (data.waveRecognizableTargetOfFrontierTarget hwave)
      (data.gaugeRecognizableTargetOfFrontierTarget hgauge)
      (data.geometricRecognizableTargetOfFrontierTarget hgeometric)

/-- The four law-native frontier targets above one fixed no-stage completion
witness already reassemble the aggregate endpoint-witness target. -/
theorem endpointWitnessTargetOfFrontierTargets
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hphase : PhaseFrontierTarget data)
    (hwave : WaveFrontierTarget data)
    (hgauge : GaugeFrontierTarget data)
    (hgeometric : GeometricFrontierTarget data) :
    EndpointWitnessTarget data := by
  exact
    data.endpointWitnessTargetOfLaneTargets
      (data.phaseEndpointWitnessTargetOfFrontierTarget hphase)
      (data.waveEndpointWitnessTargetOfFrontierTarget hwave)
      (data.gaugeEndpointWitnessTargetOfFrontierTarget hgauge)
      (data.geometricEndpointWitnessTargetOfFrontierTarget hgeometric)

/-- The four law-native frontier targets above one fixed no-stage completion
witness already recover the endpoint-complete flagship surface. -/
theorem flagshipSurfaceOfFrontierTargets
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hphase : PhaseFrontierTarget data)
    (hwave : WaveFrontierTarget data)
    (hgauge : GaugeFrontierTarget data)
    (hgeometric : GeometricFrontierTarget data) :
    ∃ endpointWitnesses : FlagshipEndpointWitnesses data.completionLaw,
      PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
      Nonempty
        (PhaseLane.RecognizableIdentity
          Time Carrier Law
          endpointWitnesses.phase.Field
          endpointWitnesses.phase.Scalar) ∧
      Nonempty
        (WaveLane.RecognizableIdentity
          Time Carrier Law
          endpointWitnesses.wave.Field
          endpointWitnesses.wave.Scalar) ∧
      Nonempty
        (GaugeLane.RecognizableIdentity
          Time Carrier Law
          endpointWitnesses.gauge.Field
          endpointWitnesses.gauge.Source) ∧
      Nonempty
        (GeometricLane.RecognizableIdentity
          Time Carrier Law
          endpointWitnesses.geometric.Tensor
          endpointWitnesses.geometric.Scalar) := by
  exact
    data.flagshipSurfaceOfLaneTargets
      (data.phaseEndpointWitnessTargetOfFrontierTarget hphase)
      (data.waveEndpointWitnessTargetOfFrontierTarget hwave)
      (data.gaugeEndpointWitnessTargetOfFrontierTarget hgauge)
      (data.geometricEndpointWitnessTargetOfFrontierTarget hgeometric)

/-- The four law-native frontier targets package into the exact fixed-witness
flagship boundary target. -/
theorem flagshipBoundaryTargetOfFrontierTargets
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hphase : PhaseFrontierTarget data)
    (hwave : WaveFrontierTarget data)
    (hgauge : GaugeFrontierTarget data)
    (hgeometric : GeometricFrontierTarget data) :
    FlagshipBoundaryTarget data := by
  exact ⟨hphase, hwave, hgauge, hgeometric⟩

/-- On one fixed no-stage completion witness, the aggregate frontier-side
boundary target is equivalent to carrying one aggregate flagship frontier
bundle on that same completion law. -/
theorem flagshipBoundaryTarget_iff_nonempty_frontiers
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law) :
    FlagshipBoundaryTarget data ↔
      Nonempty (FlagshipFrontiers data.completionLaw) := by
  constructor
  · intro hboundary
    rcases hboundary with ⟨hphase, hwave, hgauge, hgeometric⟩
    rcases hphase with ⟨phase⟩
    rcases hwave with ⟨wave⟩
    rcases hgauge with ⟨gauge⟩
    rcases hgeometric with ⟨geometric⟩
    exact ⟨{
      phase := phase
      wave := wave
      gauge := gauge
      geometric := geometric
    }⟩
  · intro hfrontiers
    rcases hfrontiers with ⟨frontiers⟩
    exact
      data.flagshipBoundaryTargetOfFrontierTargets
        ⟨frontiers.phase⟩
        ⟨frontiers.wave⟩
        ⟨frontiers.gauge⟩
        ⟨frontiers.geometric⟩

/-- The exact fixed-witness flagship boundary target already implies the
aggregate endpoint-witness target. -/
theorem endpointWitnessTargetOfBoundaryTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hboundary : FlagshipBoundaryTarget data) :
    EndpointWitnessTarget data := by
  rcases hboundary with ⟨hphase, hwave, hgauge, hgeometric⟩
  exact data.endpointWitnessTargetOfFrontierTargets hphase hwave hgauge hgeometric

/-- Conversely, an aggregate endpoint-witness target above one fixed no-stage
completion witness already determines the aggregate frontier-side boundary
target on that same witness. -/
theorem flagshipBoundaryTargetOfEndpointWitnessTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hendpoint : EndpointWitnessTarget data) :
    FlagshipBoundaryTarget data := by
  rcases hendpoint with ⟨witnesses⟩
  exact
    (data.flagshipBoundaryTarget_iff_nonempty_frontiers).2
      ⟨witnesses.toFrontiers⟩

/-- On one fixed no-stage completion witness, the aggregate endpoint-witness
target is equivalent to the aggregate frontier-side boundary target. -/
theorem endpointWitnessTarget_iff_flagshipBoundaryTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law) :
    EndpointWitnessTarget data ↔ FlagshipBoundaryTarget data := by
  constructor
  · exact data.flagshipBoundaryTargetOfEndpointWitnessTarget
  · exact data.endpointWitnessTargetOfBoundaryTarget

/-- The four exact endpoint-witness lane targets package into the exact
fixed-witness flagship boundary target. -/
theorem flagshipExactBoundaryTargetOfLaneTargets
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hphase : PhaseEndpointWitnessTarget data)
    (hwave : WaveEndpointWitnessTarget data)
    (hgauge : GaugeEndpointWitnessTarget data)
    (hgeometric : GeometricEndpointWitnessTarget data) :
    FlagshipExactBoundaryTarget data := by
  exact ⟨hphase, hwave, hgauge, hgeometric⟩

/-- The exact fixed-witness flagship boundary target reassembles the aggregate
endpoint-witness target. -/
theorem endpointWitnessTargetOfExactBoundaryTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hexact : FlagshipExactBoundaryTarget data) :
    EndpointWitnessTarget data := by
  rcases hexact with ⟨hphase, hwave, hgauge, hgeometric⟩
  exact data.endpointWitnessTargetOfLaneTargets hphase hwave hgauge hgeometric

/-- The exact fixed-witness flagship boundary target implies the frontier-side
fixed-witness boundary target. -/
theorem flagshipBoundaryTargetOfExactBoundaryTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hexact : FlagshipExactBoundaryTarget data) :
    FlagshipBoundaryTarget data := by
  rcases hexact with ⟨hphase, hwave, hgauge, hgeometric⟩
  exact
    ⟨data.phaseFrontierTargetOfEndpointTarget hphase,
      data.waveFrontierTargetOfEndpointTarget hwave,
      data.gaugeFrontierTargetOfEndpointTarget hgauge,
      data.geometricFrontierTargetOfEndpointTarget hgeometric⟩

/-- The frontier-side fixed-witness boundary target implies the exact
fixed-witness boundary target. -/
theorem flagshipExactBoundaryTargetOfBoundaryTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hboundary : FlagshipBoundaryTarget data) :
    FlagshipExactBoundaryTarget data := by
  rcases hboundary with ⟨hphase, hwave, hgauge, hgeometric⟩
  exact
    ⟨data.phaseEndpointWitnessTargetOfFrontierTarget hphase,
      data.waveEndpointWitnessTargetOfFrontierTarget hwave,
      data.gaugeEndpointWitnessTargetOfFrontierTarget hgauge,
      data.geometricEndpointWitnessTargetOfFrontierTarget hgeometric⟩

/-- The frontier-side fixed-witness boundary target already implies the
smaller recognizable boundary target. -/
theorem flagshipRecognizableBoundaryTargetOfBoundaryTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hboundary : FlagshipBoundaryTarget data) :
    FlagshipRecognizableBoundaryTarget data := by
  rcases hboundary with ⟨hphase, hwave, hgauge, hgeometric⟩
  exact
    data.flagshipRecognizableBoundaryTargetOfFrontierTargets
      hphase hwave hgauge hgeometric

/-- The exact fixed-witness boundary target already implies the smaller
recognizable boundary target. -/
theorem flagshipRecognizableBoundaryTargetOfExactBoundaryTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hexact : FlagshipExactBoundaryTarget data) :
    FlagshipRecognizableBoundaryTarget data := by
  exact
    data.flagshipRecognizableBoundaryTargetOfBoundaryTarget
      (data.flagshipBoundaryTargetOfExactBoundaryTarget hexact)

/-- Surface theorem for the frontier-side fixed-witness flagship boundary
target through the endpoint-complete flagship surface. -/
theorem flagshipSurfaceOfBoundaryTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hboundary : FlagshipBoundaryTarget data) :
    ∃ endpointWitnesses : FlagshipEndpointWitnesses data.completionLaw,
      PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
      Nonempty
        (PhaseLane.RecognizableIdentity
          Time Carrier Law
          endpointWitnesses.phase.Field
          endpointWitnesses.phase.Scalar) ∧
      Nonempty
        (WaveLane.RecognizableIdentity
          Time Carrier Law
          endpointWitnesses.wave.Field
          endpointWitnesses.wave.Scalar) ∧
      Nonempty
        (GaugeLane.RecognizableIdentity
          Time Carrier Law
          endpointWitnesses.gauge.Field
          endpointWitnesses.gauge.Source) ∧
      Nonempty
        (GeometricLane.RecognizableIdentity
          Time Carrier Law
          endpointWitnesses.geometric.Tensor
          endpointWitnesses.geometric.Scalar) := by
  rcases hboundary with ⟨hphase, hwave, hgauge, hgeometric⟩
  exact data.flagshipSurfaceOfFrontierTargets hphase hwave hgauge hgeometric

/-- Surface theorem for the exact fixed-witness flagship boundary target
through the endpoint-complete flagship surface. -/
theorem flagshipSurfaceOfExactBoundaryTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hexact : FlagshipExactBoundaryTarget data) :
    ∃ endpointWitnesses : FlagshipEndpointWitnesses data.completionLaw,
      PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
      Nonempty
        (PhaseLane.RecognizableIdentity
          Time Carrier Law
          endpointWitnesses.phase.Field
          endpointWitnesses.phase.Scalar) ∧
      Nonempty
        (WaveLane.RecognizableIdentity
          Time Carrier Law
          endpointWitnesses.wave.Field
          endpointWitnesses.wave.Scalar) ∧
      Nonempty
        (GaugeLane.RecognizableIdentity
          Time Carrier Law
          endpointWitnesses.gauge.Field
          endpointWitnesses.gauge.Source) ∧
      Nonempty
        (GeometricLane.RecognizableIdentity
          Time Carrier Law
          endpointWitnesses.geometric.Tensor
          endpointWitnesses.geometric.Scalar) := by
  exact data.flagshipSurface (data.endpointWitnessTargetOfExactBoundaryTarget hexact)

/-- The four exact lane-specific endpoint-witness targets above one fixed
no-stage completion witness already realize the direct normal-form target. -/
theorem normalFormTargetOfEndpointLaneTargets
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hphase : PhaseEndpointWitnessTarget data)
    (hwave : WaveEndpointWitnessTarget data)
    (hgauge : GaugeEndpointWitnessTarget data)
    (hgeometric : GeometricEndpointWitnessTarget data) :
    NormalFormTarget law := by
  exact
    data.normalFormTargetOfFrontierTargets
      (data.phaseFrontierTargetOfEndpointTarget hphase)
      (data.waveFrontierTargetOfEndpointTarget hwave)
      (data.gaugeFrontierTargetOfEndpointTarget hgauge)
      (data.geometricFrontierTargetOfEndpointTarget hgeometric)

/-- Surface theorem for the four exact lane-specific endpoint-witness targets
above one fixed no-stage completion witness. -/
theorem normalFormTargetSurfaceOfEndpointLaneTargets
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hphase : PhaseEndpointWitnessTarget data)
    (hwave : WaveEndpointWitnessTarget data)
    (hgauge : GaugeEndpointWitnessTarget data)
    (hgeometric : GeometricEndpointWitnessTarget data) :
    ∃ normalForms : FlagshipNormalForms Time Carrier Law,
      data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
        data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          law.physicalPrinciple ∧
        PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
        Nonempty
          (PhaseLane.RecognizableIdentity
            Time Carrier Law
            normalForms.PhaseField
            normalForms.PhaseScalar) ∧
        Nonempty
          (WaveLane.RecognizableIdentity
            Time Carrier Law
            normalForms.WaveField
            normalForms.WaveScalar) ∧
        Nonempty
          (GaugeLane.RecognizableIdentity
            Time Carrier Law
            normalForms.GaugeField
            normalForms.GaugeSource) ∧
        Nonempty
          (GeometricLane.RecognizableIdentity
            Time Carrier Law
            normalForms.GeometricTensor
            normalForms.GeometricScalar) := by
  exact
    data.normalFormTargetSurfaceOfFrontierTargets
      (data.phaseFrontierTargetOfEndpointTarget hphase)
      (data.waveFrontierTargetOfEndpointTarget hwave)
      (data.gaugeFrontierTargetOfEndpointTarget hgauge)
      (data.geometricFrontierTargetOfEndpointTarget hgeometric)

/-- The exact endpoint-witness target above one fixed no-stage completion
witness already realizes the direct normal-form target. -/
theorem normalFormTargetOfEndpointWitnessTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hendpoint : EndpointWitnessTarget data) :
    NormalFormTarget law := by
  rcases hendpoint with ⟨witnesses⟩
  exact
    data.normalFormTargetOfEndpointLaneTargets
      ⟨witnesses.phase⟩
      ⟨witnesses.wave⟩
      ⟨witnesses.gauge⟩
      ⟨witnesses.geometric⟩

/-- Surface theorem for the exact endpoint-witness target above one fixed
no-stage completion witness. -/
theorem normalFormTargetSurfaceOfEndpointWitnessTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hendpoint : EndpointWitnessTarget data) :
    ∃ normalForms : FlagshipNormalForms Time Carrier Law,
      data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
        data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          law.physicalPrinciple ∧
        PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
        Nonempty
          (PhaseLane.RecognizableIdentity
            Time Carrier Law
            normalForms.PhaseField
            normalForms.PhaseScalar) ∧
        Nonempty
          (WaveLane.RecognizableIdentity
            Time Carrier Law
            normalForms.WaveField
            normalForms.WaveScalar) ∧
        Nonempty
          (GaugeLane.RecognizableIdentity
            Time Carrier Law
            normalForms.GaugeField
            normalForms.GaugeSource) ∧
        Nonempty
          (GeometricLane.RecognizableIdentity
            Time Carrier Law
            normalForms.GeometricTensor
            normalForms.GeometricScalar) := by
  rcases hendpoint with ⟨witnesses⟩
  exact
    data.normalFormTargetSurfaceOfEndpointLaneTargets
      ⟨witnesses.phase⟩
      ⟨witnesses.wave⟩
      ⟨witnesses.gauge⟩
      ⟨witnesses.geometric⟩

/-- The exact fixed-witness flagship boundary target already implies the direct
normal-form target. -/
theorem normalFormTargetOfBoundaryTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hboundary : FlagshipBoundaryTarget data) :
    NormalFormTarget law := by
  rcases hboundary with ⟨hphase, hwave, hgauge, hgeometric⟩
  exact data.normalFormTargetOfFrontierTargets hphase hwave hgauge hgeometric

/-- The exact fixed-witness flagship boundary target already implies the direct
normal-form target. -/
theorem normalFormTargetOfExactBoundaryTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hexact : FlagshipExactBoundaryTarget data) :
    NormalFormTarget law := by
  rcases hexact with ⟨hphase, hwave, hgauge, hgeometric⟩
  exact data.normalFormTargetOfEndpointLaneTargets hphase hwave hgauge hgeometric

/-- Surface theorem for the exact fixed-witness flagship boundary target
through the direct normal-form surface. -/
theorem normalFormTargetSurfaceOfBoundaryTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hboundary : FlagshipBoundaryTarget data) :
    ∃ normalForms : FlagshipNormalForms Time Carrier Law,
      data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
        data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          law.physicalPrinciple ∧
        PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
        Nonempty
          (PhaseLane.RecognizableIdentity
            Time Carrier Law
            normalForms.PhaseField
            normalForms.PhaseScalar) ∧
        Nonempty
          (WaveLane.RecognizableIdentity
            Time Carrier Law
            normalForms.WaveField
            normalForms.WaveScalar) ∧
        Nonempty
          (GaugeLane.RecognizableIdentity
            Time Carrier Law
            normalForms.GaugeField
            normalForms.GaugeSource) ∧
        Nonempty
        (GeometricLane.RecognizableIdentity
          Time Carrier Law
          normalForms.GeometricTensor
          normalForms.GeometricScalar) := by
  rcases hboundary with ⟨hphase, hwave, hgauge, hgeometric⟩
  exact data.normalFormTargetSurfaceOfFrontierTargets hphase hwave hgauge hgeometric

/-- Surface theorem for the exact fixed-witness flagship boundary target
through the direct normal-form surface. -/
theorem normalFormTargetSurfaceOfExactBoundaryTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hexact : FlagshipExactBoundaryTarget data) :
    ∃ normalForms : FlagshipNormalForms Time Carrier Law,
      data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
        data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          law.physicalPrinciple ∧
        PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
        Nonempty
          (PhaseLane.RecognizableIdentity
            Time Carrier Law
            normalForms.PhaseField
            normalForms.PhaseScalar) ∧
        Nonempty
          (WaveLane.RecognizableIdentity
            Time Carrier Law
            normalForms.WaveField
            normalForms.WaveScalar) ∧
        Nonempty
          (GaugeLane.RecognizableIdentity
            Time Carrier Law
            normalForms.GaugeField
            normalForms.GaugeSource) ∧
        Nonempty
          (GeometricLane.RecognizableIdentity
            Time Carrier Law
            normalForms.GeometricTensor
            normalForms.GeometricScalar) := by
  rcases hexact with ⟨hphase, hwave, hgauge, hgeometric⟩
  exact data.normalFormTargetSurfaceOfEndpointLaneTargets hphase hwave hgauge hgeometric

end NoStageCompletionWitness

/-- Existence-level exact endpoint-witness target above one smaller
microscopic closure law. It says that the law carries one no-stage completion
witness, and that witness already carries the four exact lane-specific
endpoint-witness targets on its own selected bundle. This is the exact-side
existence-level form of the remaining closure-side flagship seam. -/
def FlagshipExactTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) : Prop :=
  ∃ data : NoStageCompletionWitness law, FlagshipExactBoundaryTarget data

/-- Existence-level smaller recognizable target above one smaller microscopic
closure law. It says that the law carries one no-stage completion witness, and
that witness already carries the four smaller recognizable lane targets on its
own selected bundle. This is the direct remaining theorem surface for the
normal-form branch. -/
def FlagshipRecognizableTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) : Prop :=
  ∃ data : NoStageCompletionWitness law, FlagshipRecognizableBoundaryTarget data

/-- Existence-level law-native frontier target above one smaller microscopic
closure law. It says that the law carries one no-stage completion witness, and
that witness carries the four law-native frontier targets on its own selected
bundle. This is the exact remaining theorem surface below the endpoint-witness
and closure targets. The smaller direct normal-form branch already factors
through `FlagshipRecognizableTarget`. -/
def FlagshipFrontierTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) : Prop :=
  ∃ data : NoStageCompletionWitness law, FlagshipBoundaryTarget data

namespace MicroscopicClosureLaw

/-- A fixed-witness exact endpoint-witness boundary target already yields the
existence-level exact endpoint-witness target. -/
theorem flagshipExactTargetOfExactBoundaryTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    {data : NoStageCompletionWitness law}
    (hexact : FlagshipExactBoundaryTarget data) :
    FlagshipExactTarget law := by
  exact ⟨data, hexact⟩

/-- A fixed-witness frontier-side boundary target already yields the
existence-level exact endpoint-witness target. -/
theorem flagshipExactTargetOfBoundaryTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    {data : NoStageCompletionWitness law}
    (hboundary : FlagshipBoundaryTarget data) :
    FlagshipExactTarget law := by
  exact
    law.flagshipExactTargetOfExactBoundaryTarget
      (data.flagshipExactBoundaryTargetOfBoundaryTarget hboundary)

/-- The existence-level exact endpoint-witness target already implies the
existence-level flagship target. -/
theorem flagshipTargetOfExactTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hexact : FlagshipExactTarget law) :
    FlagshipTarget law := by
  rcases hexact with ⟨data, hboundary⟩
  exact ⟨data, data.endpointWitnessTargetOfExactBoundaryTarget hboundary⟩

/-- Surface theorem for the existence-level exact endpoint-witness target
through the endpoint-complete flagship surface. -/
theorem flagshipSurfaceOfExactTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hexact : FlagshipExactTarget law) :
    ∃ data : NoStageCompletionWitness law,
      ∃ endpointWitnesses : FlagshipEndpointWitnesses data.completionLaw,
        data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
          data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple ∧
          PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.phase.Field
              endpointWitnesses.phase.Scalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.wave.Field
              endpointWitnesses.wave.Scalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.gauge.Field
              endpointWitnesses.gauge.Source) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.geometric.Tensor
              endpointWitnesses.geometric.Scalar) := by
  rcases hexact with ⟨data, hboundary⟩
  rcases data.flagshipSurfaceOfExactBoundaryTarget hboundary with
    ⟨endpointWitnesses, hcompletion, hphaseRec, hwaveRec, hgaugeRec,
      hgeometricRec⟩
  exact
    ⟨data,
      endpointWitnesses,
      data.sameBridge,
      data.samePhysicalPrinciple,
      hcompletion,
      hphaseRec,
      hwaveRec,
      hgaugeRec,
      hgeometricRec⟩

/-- A fixed-witness recognizable boundary target already yields the
existence-level recognizable target. -/
theorem flagshipRecognizableTargetOfRecognizableBoundaryTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    {data : NoStageCompletionWitness law}
    (hrecognizable : FlagshipRecognizableBoundaryTarget data) :
    FlagshipRecognizableTarget law := by
  exact ⟨data, hrecognizable⟩

/-- A fixed-witness frontier-side boundary target already yields the
existence-level recognizable target. -/
theorem flagshipRecognizableTargetOfBoundaryTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    {data : NoStageCompletionWitness law}
    (hboundary : FlagshipBoundaryTarget data) :
    FlagshipRecognizableTarget law := by
  exact
    law.flagshipRecognizableTargetOfRecognizableBoundaryTarget
      (data.flagshipRecognizableBoundaryTargetOfBoundaryTarget hboundary)

/-- A fixed-witness exact boundary target already yields the existence-level
recognizable target. -/
theorem flagshipRecognizableTargetOfExactBoundaryTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    {data : NoStageCompletionWitness law}
    (hexact : FlagshipExactBoundaryTarget data) :
    FlagshipRecognizableTarget law := by
  exact
    law.flagshipRecognizableTargetOfRecognizableBoundaryTarget
      (data.flagshipRecognizableBoundaryTargetOfExactBoundaryTarget hexact)

/-- The existence-level exact endpoint-witness target already yields the
smaller existence-level recognizable target. -/
theorem flagshipRecognizableTargetOfExactTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hexact : FlagshipExactTarget law) :
    FlagshipRecognizableTarget law := by
  rcases hexact with ⟨data, hboundary⟩
  exact
    law.flagshipRecognizableTargetOfExactBoundaryTarget hboundary

/-- A fixed-witness flagship boundary target already yields the existence-level
law-native frontier target. -/
theorem flagshipFrontierTargetOfBoundaryTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    {data : NoStageCompletionWitness law}
    (hboundary : FlagshipBoundaryTarget data) :
    FlagshipFrontierTarget law := by
  exact ⟨data, hboundary⟩

/-- The existence-level law-native frontier target already implies the
existence-level flagship target. -/
theorem flagshipTargetOfFrontierTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hfrontier : FlagshipFrontierTarget law) :
    FlagshipTarget law := by
  rcases hfrontier with ⟨data, hboundary⟩
  exact ⟨data, data.endpointWitnessTargetOfBoundaryTarget hboundary⟩

/-- The existence-level law-native frontier target already implies the
existence-level exact endpoint-witness target. -/
theorem flagshipExactTargetOfFrontierTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hfrontier : FlagshipFrontierTarget law) :
    FlagshipExactTarget law := by
  rcases hfrontier with ⟨data, hboundary⟩
  exact
    law.flagshipExactTargetOfBoundaryTarget hboundary

/-- Surface theorem for the existence-level law-native frontier target through
the endpoint-complete flagship surface. -/
theorem flagshipSurfaceOfFrontierTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hfrontier : FlagshipFrontierTarget law) :
    ∃ data : NoStageCompletionWitness law,
      ∃ endpointWitnesses : FlagshipEndpointWitnesses data.completionLaw,
        data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
          data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple ∧
          PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.phase.Field
              endpointWitnesses.phase.Scalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.wave.Field
              endpointWitnesses.wave.Scalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.gauge.Field
              endpointWitnesses.gauge.Source) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.geometric.Tensor
              endpointWitnesses.geometric.Scalar) := by
  rcases hfrontier with ⟨data, hboundary⟩
  rcases data.flagshipSurfaceOfBoundaryTarget hboundary with
    ⟨endpointWitnesses, hcompletion, hphaseRec, hwaveRec, hgaugeRec,
      hgeometricRec⟩
  exact
    ⟨data,
      endpointWitnesses,
      data.sameBridge,
      data.samePhysicalPrinciple,
      hcompletion,
      hphaseRec,
      hwaveRec,
      hgaugeRec,
      hgeometricRec⟩

/-- The existence-level law-native frontier target already yields the smaller
existence-level recognizable target. -/
theorem flagshipRecognizableTargetOfFrontierTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hfrontier : FlagshipFrontierTarget law) :
    FlagshipRecognizableTarget law := by
  rcases hfrontier with ⟨data, hboundary⟩
  exact
    law.flagshipRecognizableTargetOfBoundaryTarget hboundary

/-- The existence-level exact endpoint-witness target already implies the
direct normal-form target. -/
theorem normalFormTargetOfExactTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hexact : FlagshipExactTarget law) :
    NormalFormTarget law := by
  rcases hexact with ⟨data, hboundary⟩
  exact data.normalFormTargetOfExactBoundaryTarget hboundary

/-- Surface theorem for the existence-level exact endpoint-witness target
through the direct normal-form surface. -/
theorem normalFormTargetSurfaceOfExactTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hexact : FlagshipExactTarget law) :
    ∃ data : NoStageCompletionWitness law,
      ∃ normalForms : FlagshipNormalForms Time Carrier Law,
        data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
          data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple ∧
          PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              normalForms.PhaseField
              normalForms.PhaseScalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              normalForms.WaveField
              normalForms.WaveScalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GaugeField
              normalForms.GaugeSource) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GeometricTensor
              normalForms.GeometricScalar) := by
  rcases hexact with ⟨data, hboundary⟩
  exact ⟨data, data.normalFormTargetSurfaceOfExactBoundaryTarget hboundary⟩

/-- The existence-level recognizable target already implies the direct
normal-form target. -/
theorem normalFormTargetOfRecognizableTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hrecognizable : FlagshipRecognizableTarget law) :
    NormalFormTarget law := by
  rcases hrecognizable with ⟨data, hboundary⟩
  exact data.normalFormTargetOfRecognizableBoundaryTarget hboundary

/-- Surface theorem for the existence-level recognizable target through the
direct normal-form surface. -/
theorem normalFormTargetSurfaceOfRecognizableTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hrecognizable : FlagshipRecognizableTarget law) :
    ∃ data : NoStageCompletionWitness law,
      ∃ normalForms : FlagshipNormalForms Time Carrier Law,
        data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
          data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple ∧
          PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              normalForms.PhaseField
              normalForms.PhaseScalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              normalForms.WaveField
              normalForms.WaveScalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GaugeField
              normalForms.GaugeSource) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GeometricTensor
              normalForms.GeometricScalar) := by
  rcases hrecognizable with ⟨data, hboundary⟩
  exact ⟨data, data.normalFormTargetSurfaceOfRecognizableBoundaryTarget hboundary⟩

/-- The existence-level law-native frontier target already implies the direct
normal-form target. -/
theorem normalFormTargetOfFrontierTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hfrontier : FlagshipFrontierTarget law) :
    NormalFormTarget law := by
  exact
    law.normalFormTargetOfRecognizableTarget
      (law.flagshipRecognizableTargetOfFrontierTarget hfrontier)

/-- Surface theorem for the existence-level law-native frontier target through
the direct normal-form surface. -/
theorem normalFormTargetSurfaceOfFrontierTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hfrontier : FlagshipFrontierTarget law) :
    ∃ data : NoStageCompletionWitness law,
      ∃ normalForms : FlagshipNormalForms Time Carrier Law,
        data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
          data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple ∧
          PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              normalForms.PhaseField
              normalForms.PhaseScalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              normalForms.WaveField
              normalForms.WaveScalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GaugeField
              normalForms.GaugeSource) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GeometricTensor
              normalForms.GeometricScalar) := by
  exact
    law.normalFormTargetSurfaceOfRecognizableTarget
      (law.flagshipRecognizableTargetOfFrontierTarget hfrontier)

/-- Once origin closure and sector closure are in place, the existence-level
law-native frontier target already yields the full detached closure surface. -/
theorem fullClosureWitnessSurfaceOfFrontierTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (horigin : OriginClosureTarget law)
    (hsector : SectorClosureTarget law)
    (hfrontier : FlagshipFrontierTarget law) :
    ∃ data : NoStageCompletionWitness law,
      ∃ endpointWitnesses : FlagshipEndpointWitnesses data.completionLaw,
        data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
          data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple ∧
          Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
          Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
          realized_generator_carries_bedrock_law law.bridge.generator ∧
          AutonomousHorizon
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          horizonFiberInvariant
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.phase.Field
              endpointWitnesses.phase.Scalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.wave.Field
              endpointWitnesses.wave.Scalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.gauge.Field
              endpointWitnesses.gauge.Source) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.geometric.Tensor
              endpointWitnesses.geometric.Scalar) :=
  law.fullClosureWitnessSurface horigin hsector
    (law.flagshipTargetOfFrontierTarget hfrontier)

/-- Once origin closure and sector closure are in place, the existence-level
exact endpoint-witness target already yields the full detached closure
surface. -/
theorem fullClosureWitnessSurfaceOfExactTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (horigin : OriginClosureTarget law)
    (hsector : SectorClosureTarget law)
    (hexact : FlagshipExactTarget law) :
    ∃ data : NoStageCompletionWitness law,
      ∃ endpointWitnesses : FlagshipEndpointWitnesses data.completionLaw,
        data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
          data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple ∧
          Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
          Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
          realized_generator_carries_bedrock_law law.bridge.generator ∧
          AutonomousHorizon
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          horizonFiberInvariant
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.phase.Field
              endpointWitnesses.phase.Scalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.wave.Field
              endpointWitnesses.wave.Scalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.gauge.Field
              endpointWitnesses.gauge.Source) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.geometric.Tensor
              endpointWitnesses.geometric.Scalar) :=
  law.fullClosureWitnessSurface horigin hsector
    (law.flagshipTargetOfExactTarget hexact)

/-- Once origin closure and sector closure are in place, the existence-level
law-native frontier target already yields the full detached normal-form
surface. -/
theorem fullNormalFormSurfaceOfFrontierTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (horigin : OriginClosureTarget law)
    (hsector : SectorClosureTarget law)
    (hfrontier : FlagshipFrontierTarget law) :
    ∃ data : NoStageCompletionWitness law,
      ∃ normalForms : FlagshipNormalForms Time Carrier Law,
        data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
          data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple ∧
          Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
          Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
          realized_generator_carries_bedrock_law law.bridge.generator ∧
          AutonomousHorizon
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          horizonFiberInvariant
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              normalForms.PhaseField
              normalForms.PhaseScalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              normalForms.WaveField
              normalForms.WaveScalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GaugeField
              normalForms.GaugeSource) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GeometricTensor
              normalForms.GeometricScalar) :=
  law.fullNormalFormSurface horigin hsector
    (law.normalFormTargetOfRecognizableTarget
      (law.flagshipRecognizableTargetOfFrontierTarget hfrontier))

/-- Once origin closure and sector closure are in place, the smaller
existence-level recognizable target already yields the full detached
normal-form surface. -/
theorem fullNormalFormSurfaceOfRecognizableTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (horigin : OriginClosureTarget law)
    (hsector : SectorClosureTarget law)
    (hrecognizable : FlagshipRecognizableTarget law) :
    ∃ data : NoStageCompletionWitness law,
      ∃ normalForms : FlagshipNormalForms Time Carrier Law,
        data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
          data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple ∧
          Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
          Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
          realized_generator_carries_bedrock_law law.bridge.generator ∧
          AutonomousHorizon
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          horizonFiberInvariant
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              normalForms.PhaseField
              normalForms.PhaseScalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              normalForms.WaveField
              normalForms.WaveScalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GaugeField
              normalForms.GaugeSource) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GeometricTensor
              normalForms.GeometricScalar) :=
  law.fullNormalFormSurface horigin hsector
    (law.normalFormTargetOfRecognizableTarget hrecognizable)

/-- Once origin closure and sector closure are in place, the existence-level
exact endpoint-witness target already yields the full detached normal-form
surface. -/
theorem fullNormalFormSurfaceOfExactTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (horigin : OriginClosureTarget law)
    (hsector : SectorClosureTarget law)
    (hexact : FlagshipExactTarget law) :
    ∃ data : NoStageCompletionWitness law,
      ∃ normalForms : FlagshipNormalForms Time Carrier Law,
        data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
          data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple ∧
          Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
          Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
          realized_generator_carries_bedrock_law law.bridge.generator ∧
          AutonomousHorizon
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          horizonFiberInvariant
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              normalForms.PhaseField
              normalForms.PhaseScalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              normalForms.WaveField
              normalForms.WaveScalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GaugeField
              normalForms.GaugeSource) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GeometricTensor
              normalForms.GeometricScalar) :=
  law.fullNormalFormSurface horigin hsector
    (law.normalFormTargetOfExactTarget hexact)

/-- The existence-level flagship target already implies the direct normal-form
target. Any no-stage completion witness carrying its own endpoint witness
bundle already carries the recognizable flagship forms. -/
theorem normalFormTargetOfFlagshipTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hflagship : FlagshipTarget law) :
    NormalFormTarget law := by
  rcases hflagship with ⟨data, hendpoint⟩
  exact data.normalFormTargetOfEndpointWitnessTarget hendpoint

/-- Surface theorem for the existence-level flagship target through the direct
normal-form target. -/
theorem normalFormTargetSurfaceOfFlagshipTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hflagship : FlagshipTarget law) :
    ∃ data : NoStageCompletionWitness law,
      ∃ normalForms : FlagshipNormalForms Time Carrier Law,
        data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
          data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple ∧
          PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              normalForms.PhaseField
              normalForms.PhaseScalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              normalForms.WaveField
              normalForms.WaveScalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GaugeField
              normalForms.GaugeSource) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GeometricTensor
              normalForms.GeometricScalar) := by
  rcases hflagship with ⟨data, hendpoint⟩
  exact
    ⟨data, data.normalFormTargetSurfaceOfEndpointWitnessTarget hendpoint⟩

end MicroscopicClosureLaw

namespace NormalFormBridge

/-- The underlying proposition-level microscopic closure law carried by the
normal-form bridge. -/
def toMicroscopicClosureLaw
    {Index Time Carrier Law : Type}
    (data : NormalFormBridge Index Time Carrier Law) :
    MicroscopicClosureLaw Index Time Carrier Law :=
  data.completionBridge.toMicroscopicClosureLaw

/-- Repackage the concrete recognizable identities into the direct abstract
normal-form target package. -/
def toFlagshipNormalForms
    {Index Time Carrier Law : Type}
    (data : NormalFormBridge Index Time Carrier Law) :
    FlagshipNormalForms Time Carrier Law where
  PhaseField := data.PhaseField
  PhaseScalar := data.PhaseScalar
  phase := PhaseLane.recognizableIdentity data.phaseRigidity
  WaveField := data.WaveField
  WaveScalar := data.WaveScalar
  wave := WaveLane.recognizableIdentity data.waveRigidity
  GaugeField := data.GaugeField
  GaugeSource := data.GaugeSource
  gauge := GaugeLane.recognizableIdentity data.gaugeRigidity
  GeometricTensor := data.GeometricTensor
  GeometricScalar := data.GeometricScalar
  geometric := GeometricLane.recognizableIdentity data.geometricRigidity

/-- The origin-closure target still follows from the underlying completion
bridge. -/
theorem originClosureTarget
    {Index Time Carrier Law : Type}
    (data : NormalFormBridge Index Time Carrier Law) :
    OriginClosureTarget data.toMicroscopicClosureLaw := by
  exact data.completionBridge.originClosureTarget

/-- The sector-closure target still follows from the underlying completion
bridge. -/
theorem sectorClosureTarget
    {Index Time Carrier Law : Type}
    (data : NormalFormBridge Index Time Carrier Law) :
    SectorClosureTarget data.toMicroscopicClosureLaw := by
  exact data.completionBridge.sectorClosureTarget

/-- The no-stage completion target still follows from the underlying
completion bridge. -/
theorem completionTarget
    {Index Time Carrier Law : Type}
    (data : NormalFormBridge Index Time Carrier Law) :
    NoStageCompletionTarget data.toMicroscopicClosureLaw := by
  exact data.completionBridge.completionTarget

/-- The split normal-form bridge forces the direct recognizable flagship
target. -/
theorem normalFormTarget
    {Index Time Carrier Law : Type}
    (data : NormalFormBridge Index Time Carrier Law) :
    NormalFormTarget data.toMicroscopicClosureLaw := by
  exact
    ⟨data.completionBridge.toNoStageCompletionWitness,
      ⟨data.toFlagshipNormalForms⟩⟩

/-- Concrete surface carried by the split normal-form bridge: all four
sector-rigidity packages live on the same aligned completion datum, and the
recognizable flagship identities therefore already follow. -/
theorem recognizableSurface
    {Index Time Carrier Law : Type}
    (data : NormalFormBridge Index Time Carrier Law) :
    data.phaseRigidity.orthogonalityRigidity.completion =
        data.completionBridge.completion ∧
      data.waveRigidity.orthogonalityRigidity.completion =
        data.completionBridge.completion ∧
      data.gaugeRigidity.orthogonalityRigidity.completion =
        data.completionBridge.completion ∧
      data.geometricRigidity.orthogonalityRigidity.completion =
        data.completionBridge.completion ∧
      PartIVLawCompletionStatement
        data.completionBridge.toLocalEventFourStateCompletionLaw.toNaturalOperatorCompletion ∧
      Nonempty
        (PhaseLane.RecognizableIdentity
          Time Carrier Law data.PhaseField data.PhaseScalar) ∧
      Nonempty
        (WaveLane.RecognizableIdentity
          Time Carrier Law data.WaveField data.WaveScalar) ∧
      Nonempty
        (GaugeLane.RecognizableIdentity
          Time Carrier Law data.GaugeField data.GaugeSource) ∧
      Nonempty
        (GeometricLane.RecognizableIdentity
          Time Carrier Law data.GeometricTensor data.GeometricScalar) := by
  exact
    ⟨data.phaseUsesCompletion,
      data.waveUsesCompletion,
      data.gaugeUsesCompletion,
      data.geometricUsesCompletion,
      data.completionBridge.alignmentSurface.2.2,
      PhaseLane.recognizableIdentity data.phaseRigidity,
      WaveLane.recognizableIdentity data.waveRigidity,
      GaugeLane.recognizableIdentity data.gaugeRigidity,
      GeometricLane.recognizableIdentity data.geometricRigidity⟩

/-- Abstract normal-form target surface recovered from the split bridge. -/
theorem normalFormTargetSurface
    {Index Time Carrier Law : Type}
    (data : NormalFormBridge Index Time Carrier Law) :
    ∃ witness : NoStageCompletionWitness data.toMicroscopicClosureLaw,
      ∃ normalForms : FlagshipNormalForms Time Carrier Law,
        witness.completionLaw.fourStateLaw.framed.object.bridge =
            data.toMicroscopicClosureLaw.bridge ∧
          witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.toMicroscopicClosureLaw.physicalPrinciple ∧
          PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              normalForms.PhaseField
              normalForms.PhaseScalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              normalForms.WaveField
              normalForms.WaveScalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GaugeField
              normalForms.GaugeSource) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GeometricTensor
              normalForms.GeometricScalar) := by
  exact
    data.toMicroscopicClosureLaw.normalFormTargetSurface
      data.normalFormTarget

/-- Grouped surface carried by the split normal-form bridge: origin closure,
sector closure, the law-native completion surface, and the four recognizable
flagship identities all follow from one smaller bridge package. -/
theorem fullSurface
    {Index Time Carrier Law : Type}
    (data : NormalFormBridge Index Time Carrier Law) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
      realized_generator_carries_bedrock_law
        data.completionBridge.sectorLaw.bridge.generator ∧
      AutonomousHorizon
        data.completionBridge.sectorLaw.bridge.selectedBridge.observer.selection.realization.tower
        data.completionBridge.sectorLaw.bridge.selectedBridge.observer.selection.horizon
        data.completionBridge.sectorLaw.bridge.generator ∧
      horizonFiberInvariant
        data.completionBridge.sectorLaw.bridge.selectedBridge.observer.selection.realization.tower
        data.completionBridge.sectorLaw.bridge.selectedBridge.observer.selection.horizon
        data.completionBridge.sectorLaw.bridge.generator ∧
      PartIVLawCompletionStatement
        data.completionBridge.toLocalEventFourStateCompletionLaw.toNaturalOperatorCompletion ∧
      Nonempty
        (PhaseLane.RecognizableIdentity
          Time Carrier Law data.PhaseField data.PhaseScalar) ∧
      Nonempty
        (WaveLane.RecognizableIdentity
          Time Carrier Law data.WaveField data.WaveScalar) ∧
      Nonempty
        (GaugeLane.RecognizableIdentity
          Time Carrier Law data.GaugeField data.GaugeSource) ∧
      Nonempty
        (GeometricLane.RecognizableIdentity
          Time Carrier Law data.GeometricTensor data.GeometricScalar) := by
  obtain ⟨hbundle, hsector, hbedrock, haut, hfiber, _hgenmin, _hprofile⟩ :=
    data.completionBridge.sectorTargetSurface
  have hnormal := data.recognizableSurface
  exact
    ⟨hbundle,
      hsector,
      hbedrock,
      haut,
      hfiber,
      hnormal.2.2.2.2.1,
      hnormal.2.2.2.2.2.1,
      hnormal.2.2.2.2.2.2.1,
      hnormal.2.2.2.2.2.2.2.1,
      hnormal.2.2.2.2.2.2.2.2⟩

end NormalFormBridge

namespace NoStageCompletionBridge

/-- Reassemble the split normal-form bridge from one fixed completion bridge
and four lane-specific rigidity data on that same completion. -/
def toNormalFormBridge
    {Index Time Carrier Law : Type}
    (completionBridge : NoStageCompletionBridge Index Time Carrier Law)
    (phase : PhaseRigidityDatum Index Time Carrier Law completionBridge)
    (wave : WaveRigidityDatum Index Time Carrier Law completionBridge)
    (gauge : GaugeRigidityDatum Index Time Carrier Law completionBridge)
    (geometric : GeometricRigidityDatum Index Time Carrier Law completionBridge) :
    NormalFormBridge Index Time Carrier Law where
  completionBridge := completionBridge
  PhaseField := phase.Field
  PhaseScalar := phase.Scalar
  phaseRigidity := phase.rigidity
  phaseUsesCompletion := phase.usesCompletion
  WaveField := wave.Field
  WaveScalar := wave.Scalar
  waveRigidity := wave.rigidity
  waveUsesCompletion := wave.usesCompletion
  GaugeField := gauge.Field
  GaugeSource := gauge.Source
  gaugeRigidity := gauge.rigidity
  gaugeUsesCompletion := gauge.usesCompletion
  GeometricTensor := geometric.Tensor
  GeometricScalar := geometric.Scalar
  geometricRigidity := geometric.rigidity
  geometricUsesCompletion := geometric.usesCompletion

/-- The four exact lane-rigidity targets above one fixed completion bridge
already realize the direct normal-form target. -/
theorem normalFormTargetOfRigidityTargets
    {Index Time Carrier Law : Type}
    (completionBridge : NoStageCompletionBridge Index Time Carrier Law)
    (hphase : PhaseRigidityTarget completionBridge)
    (hwave : WaveRigidityTarget completionBridge)
    (hgauge : GaugeRigidityTarget completionBridge)
    (hgeometric : GeometricRigidityTarget completionBridge) :
    NormalFormTarget completionBridge.toMicroscopicClosureLaw := by
  rcases hphase with ⟨phase⟩
  rcases hwave with ⟨wave⟩
  rcases hgauge with ⟨gauge⟩
  rcases hgeometric with ⟨geometric⟩
  exact
    (completionBridge.toNormalFormBridge phase wave gauge geometric).normalFormTarget

/-- The direct recognizable flagship surface already follows from the four
exact lane-rigidity targets above one fixed completion bridge. -/
theorem normalFormTargetSurfaceOfRigidityTargets
    {Index Time Carrier Law : Type}
    (completionBridge : NoStageCompletionBridge Index Time Carrier Law)
    (hphase : PhaseRigidityTarget completionBridge)
    (hwave : WaveRigidityTarget completionBridge)
    (hgauge : GaugeRigidityTarget completionBridge)
    (hgeometric : GeometricRigidityTarget completionBridge) :
    ∃ witness : NoStageCompletionWitness completionBridge.toMicroscopicClosureLaw,
      ∃ normalForms : FlagshipNormalForms Time Carrier Law,
        witness.completionLaw.fourStateLaw.framed.object.bridge =
            completionBridge.toMicroscopicClosureLaw.bridge ∧
          witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            completionBridge.toMicroscopicClosureLaw.physicalPrinciple ∧
          PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              normalForms.PhaseField
              normalForms.PhaseScalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              normalForms.WaveField
              normalForms.WaveScalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GaugeField
              normalForms.GaugeSource) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GeometricTensor
              normalForms.GeometricScalar) := by
  exact
    completionBridge.toMicroscopicClosureLaw.normalFormTargetSurface
      (completionBridge.normalFormTargetOfRigidityTargets
        hphase hwave hgauge hgeometric)

/-- The full recognizable flagship surface already follows from the four exact
lane-rigidity targets above one fixed completion bridge. -/
theorem fullSurfaceOfRigidityTargets
    {Index Time Carrier Law : Type}
    (completionBridge : NoStageCompletionBridge Index Time Carrier Law)
    (hphase : PhaseRigidityTarget completionBridge)
    (hwave : WaveRigidityTarget completionBridge)
    (hgauge : GaugeRigidityTarget completionBridge)
    (hgeometric : GeometricRigidityTarget completionBridge) :
    ∃ witness : NoStageCompletionWitness completionBridge.toMicroscopicClosureLaw,
      ∃ normalForms : FlagshipNormalForms Time Carrier Law,
        witness.completionLaw.fourStateLaw.framed.object.bridge =
            completionBridge.toMicroscopicClosureLaw.bridge ∧
          witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            completionBridge.toMicroscopicClosureLaw.physicalPrinciple ∧
          Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
          Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
          realized_generator_carries_bedrock_law
            completionBridge.toMicroscopicClosureLaw.bridge.generator ∧
          AutonomousHorizon
            completionBridge.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
            completionBridge.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
            completionBridge.toMicroscopicClosureLaw.bridge.generator ∧
          horizonFiberInvariant
            completionBridge.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
            completionBridge.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
            completionBridge.toMicroscopicClosureLaw.bridge.generator ∧
          PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              normalForms.PhaseField
              normalForms.PhaseScalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              normalForms.WaveField
              normalForms.WaveScalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GaugeField
              normalForms.GaugeSource) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GeometricTensor
              normalForms.GeometricScalar) := by
  exact
    completionBridge.toMicroscopicClosureLaw.fullNormalFormSurface
      completionBridge.originClosureTarget
      completionBridge.sectorClosureTarget
      (completionBridge.normalFormTargetOfRigidityTargets
        hphase hwave hgauge hgeometric)

end NoStageCompletionBridge

end ClosureCurrent

end CoherenceCalculus
