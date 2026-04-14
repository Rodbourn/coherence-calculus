import CoherenceCalculus.PartIV.ClosureCurrentFlagshipAnalyticCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentFlagshipStateFieldCore

One shared selected state-field law beneath the recognizable flagship
identities.

`ClosureCurrentFlagshipAnalyticCore` already packages the strongest current
analytic flagship surface of the endpoint-complete no-stage law. In
particular, it contains:

* the one canonical selected state-field law on the concrete carrier `State`,
* the exact realization-target surface showing that the current stronger
  languages already present that same law,
* the recognizable phase/wave/gauge/geometric identities on that same datum.

This file isolates that shared state-field consequence. It does not claim a
final spatial differential PDE. It says only that, on the current flagship
surface, the recognizable textbook identities already sit on one and the same
selected state-field law.
-/

namespace ClosureCurrent

/-- Shared state-field surface of the endpoint-complete flagship law.

The recognizable flagship identities live on one same selected datum, and that
same datum already carries one canonical selected state-field law on `State`
which the current stronger realization languages all present exactly. -/
def FlagshipSharedStateFieldSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) : Prop :=
  let law := data.completionLaw.fourStateLaw
  SelectedStateFieldLawSurface law ∧
    SelectedStateFieldRealizationSurface law ∧
    Nonempty
      (PhaseLane.RecognizableIdentity
        Time Carrier Law
        data.endpointWitnesses.phase.Field
        data.endpointWitnesses.phase.Scalar) ∧
    Nonempty
      (WaveLane.RecognizableIdentity
        Time Carrier Law
        data.endpointWitnesses.wave.Field
        data.endpointWitnesses.wave.Scalar) ∧
    Nonempty
      (GaugeLane.RecognizableIdentity
        Time Carrier Law
        data.endpointWitnesses.gauge.Field
        data.endpointWitnesses.gauge.Source) ∧
    Nonempty
      (GeometricLane.RecognizableIdentity
        Time Carrier Law
        data.endpointWitnesses.geometric.Tensor
        data.endpointWitnesses.geometric.Scalar)

/-- The endpoint-complete no-stage law already places the recognizable
flagship identities on one same selected datum under one same selected
state-field law on the concrete carrier `State`. The current stronger
realization languages already present that same law exactly. -/
theorem LocalEventFourStateFlagshipLaw.sharedStateFieldSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    FlagshipSharedStateFieldSurface data := by
  obtain ⟨_hcompletion, hphase, hwave, hgauge, hgeometric⟩ := data.surface
  refine
    ⟨data.completionLaw.fourStateLaw.selectedStateFieldLawSurface,
      data.completionLaw.fourStateLaw.selectedStateFieldRealizationSurface,
      hphase, hwave, hgauge, hgeometric⟩

end ClosureCurrent

end CoherenceCalculus
