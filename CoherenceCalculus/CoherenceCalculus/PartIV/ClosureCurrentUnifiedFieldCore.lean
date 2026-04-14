import CoherenceCalculus.PartIV.ClosureCurrentFlagshipStateFieldCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentUnifiedFieldCore

One explicit unified field package on the current flagship surface.

`ClosureCurrentFlagshipStateFieldCore` already shows that the recognizable
phase, wave, gauge, and geometric identities live on one same selected datum
under one same canonical selected state-field law on `State`.

This file does not add a stronger law. It gives that conclusion one explicit
mathematical package: one state-field law together with its four recognizable
flagship faces.
-/

namespace ClosureCurrent

/-- One explicit unified field package on the current flagship surface.

The package records the one canonical selected state-field law on `State`, the
fact that the current stronger realization languages already present that same
law exactly, and the four recognizable flagship identities on the same
selected datum. -/
structure UnifiedField
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) where
  law : SelectedStateFieldLaw
  lawSurface : SelectedStateFieldLawSurface data.completionLaw.fourStateLaw
  realizationSurface :
    SelectedStateFieldRealizationSurface data.completionLaw.fourStateLaw
  phaseIdentity :
    PhaseLane.RecognizableIdentity
      Time Carrier Law
      data.endpointWitnesses.phase.Field
      data.endpointWitnesses.phase.Scalar
  waveIdentity :
    WaveLane.RecognizableIdentity
      Time Carrier Law
      data.endpointWitnesses.wave.Field
      data.endpointWitnesses.wave.Scalar
  gaugeIdentity :
    GaugeLane.RecognizableIdentity
      Time Carrier Law
      data.endpointWitnesses.gauge.Field
      data.endpointWitnesses.gauge.Source
  geometricIdentity :
    GeometricLane.RecognizableIdentity
      Time Carrier Law
      data.endpointWitnesses.geometric.Tensor
      data.endpointWitnesses.geometric.Scalar
  law_eq : law = data.completionLaw.fourStateLaw.selectedStateFieldLaw

/-- Manuscript-facing unified field surface of the endpoint-complete no-stage
law. -/
def UnifiedFieldSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) : Prop :=
  Nonempty (UnifiedField data)

/-- The endpoint-complete no-stage law already yields one explicit unified
field package: one selected state-field law on `State`, exactly presented by
the current stronger realization languages, together with the recognizable
Schrödinger, wave/Klein-Gordon, Maxwell, and Einstein identities on the same
selected datum. -/
theorem LocalEventFourStateFlagshipLaw.unifiedFieldSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    UnifiedFieldSurface data := by
  obtain
    ⟨hlawSurface, hrealizationSurface, hphase, hwave, hgauge, hgeometric⟩ :=
    data.sharedStateFieldSurface
  obtain ⟨phaseIdentity⟩ := hphase
  obtain ⟨waveIdentity⟩ := hwave
  obtain ⟨gaugeIdentity⟩ := hgauge
  obtain ⟨geometricIdentity⟩ := hgeometric
  refine
    ⟨{ law := data.completionLaw.fourStateLaw.selectedStateFieldLaw
       lawSurface := hlawSurface
       realizationSurface := hrealizationSurface
       phaseIdentity := phaseIdentity
       waveIdentity := waveIdentity
       gaugeIdentity := gaugeIdentity
       geometricIdentity := geometricIdentity
       law_eq := rfl }⟩

end ClosureCurrent

end CoherenceCalculus
