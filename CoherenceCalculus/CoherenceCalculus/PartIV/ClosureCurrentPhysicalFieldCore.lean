import CoherenceCalculus.PartIV.ClosureCurrentUnifiedBoundaryClassCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentPhysicalFieldCore

One classwise physical field on the current detached flagship surface.

`ClosureCurrentUnifiedBoundaryClassCore` already closes the remaining abstract
datum-choice seam: the endpoint-complete no-stage law determines one canonical
selected-horizon boundary field across the whole admissible realized class on
the concrete carrier `State`.

The only remaining public question is then whether the recognizable flagship
identities still sit on that same field, or whether they require additional
carrier-side state data. This file records the stronger answer: the present
phase, wave, gauge, and geometric identities are already faces of that same
classwise boundary field.
-/

namespace ClosureCurrent

/-- Manuscript-facing physical-field surface of the endpoint-complete no-stage
law. The same classwise selected-horizon boundary field on `State` already
carries the recognizable phase, wave, gauge, and geometric identities on the
same selected datum. -/
def PhysicalFieldSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) : Prop :=
  UnifiedBoundaryClassSurface data ∧
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

/-- The endpoint-complete no-stage law already yields one classwise physical
field on the concrete carrier `State`: the canonical selected-horizon boundary
field across the admissible realized class, together with the recognizable
phase, wave, gauge, and geometric flagship identities on that same selected
datum. -/
theorem LocalEventFourStateFlagshipLaw.physicalFieldSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    PhysicalFieldSurface data := by
  obtain ⟨hboundaryClass⟩ := data.unifiedBoundaryClassSurface
  obtain ⟨_hcompletion, hphase, hwave, hgauge, hgeometric⟩ := data.surface
  exact ⟨⟨hboundaryClass⟩, hphase, hwave, hgauge, hgeometric⟩

end ClosureCurrent

end CoherenceCalculus
