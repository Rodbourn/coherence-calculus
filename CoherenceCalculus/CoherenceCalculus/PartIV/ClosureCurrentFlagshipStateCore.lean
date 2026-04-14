import CoherenceCalculus.PartIV.ClosureCurrentFlagshipAnalyticCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentFlagshipStateCore

One shared selected state beneath the recognizable flagship identities.

`ClosureCurrentFlagshipAnalyticCore` already packages the strongest current
analytic flagship surface of the endpoint-complete no-stage law. In
particular, it contains:

* the one selected state object on the concrete carrier `State`,
* the exact realized-form collapse on the selected cut,
* the recognizable phase/wave/gauge/geometric identities on that same datum.

This file isolates the shared-state consequence. It does not claim a final
spatial differential PDE. It says only that, on the current flagship surface,
the public realization packages already agree pointwise with one and the same
selected state object.
-/

namespace ClosureCurrent

/-- Shared-state surface of the endpoint-complete flagship law.

The recognizable flagship identities live on one same selected datum, and the
current realization packages already collapse pointwise to one underlying
selected state object on `State`. -/
def FlagshipSharedStateSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) : Prop :=
  let law := data.completionLaw.fourStateLaw
  SelectedStateObjectSurface law ∧
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
        data.endpointWitnesses.geometric.Scalar) ∧
    (∀ realization : CompositeFlagshipRealization law,
      ∀ n : Nat,
        ∀ x : State,
          realization.flagship.velocity x = law.selectedStateObject.generator x ∧
            realization.differential.blockDatum.operator x =
              law.selectedStateObject.generator x ∧
            realization.differential.blockDatum.blockPP n x =
              law.selectedStateObject.generator x ∧
            realization.differential.blockDatum.blockPQ n x = State.zero ∧
            realization.differential.blockDatum.blockQP n x = State.zero ∧
            realization.differential.blockDatum.blockQQ n x = State.zero ∧
            realization.differential.flowDatum.effectiveOp n x =
              law.selectedStateObject.generator x ∧
            realization.derivative.derivativeDatum.derivative x =
              law.selectedStateObject.generator x ∧
            realization.derivative.derivativeDatum.restriction n x =
              law.selectedStateObject.project
                (law.selectedStateObject.generator x) ∧
            realization.derivative.derivativeDatum.observed n x =
              law.selectedStateObject.project
                (law.selectedStateObject.generator x) ∧
            realization.derivative.derivativeDatum.defect n x = State.zero ∧
            realization.flagship.density x = law.selectedStateObject.density x ∧
            realization.flagship.residual x =
              law.selectedStateObject.residual x ∧
            (realization.flagship.solution x ↔
              law.selectedStateObject.solution x))

/-- The endpoint-complete no-stage law already places the recognizable flagship
identities on one same selected datum under one same selected state object on
the concrete carrier `State`. Every current public realization package agrees
pointwise with that state object. -/
theorem LocalEventFourStateFlagshipLaw.sharedStateSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    FlagshipSharedStateSurface data := by
  have hstate :
      SelectedStateObjectSurface data.completionLaw.fourStateLaw :=
    data.completionLaw.fourStateLaw.selectedStateObjectSurface
  have hform :
      SelectedRealizedFormSurface data.completionLaw.fourStateLaw :=
    data.completionLaw.fourStateLaw.selectedRealizedFormSurface
  obtain ⟨_hcompletion, hphase, hwave, hgauge, hgeometric⟩ := data.surface
  obtain
    ⟨_hstateObj, _hproject, _hgenerator, _hdensity, _hresidual,
      _hautResidual, _hsolution, _hpde, _haction, _hevolution,
      hstateRealization⟩ := hstate
  obtain ⟨_hcomposite, hoperator, _hscalar⟩ := hform
  refine ⟨data.completionLaw.fourStateLaw.selectedStateObjectSurface,
    hphase, hwave, hgauge, hgeometric, ?_⟩
  intro realization n x
  have hop := hoperator realization n x
  have hstatex := hstateRealization realization x
  rcases hop with
    ⟨_hvel, hblockOp, hblockPP, hblockPQ, hblockQP, hblockQQ, hflow, hderiv,
      hrestrict, hobserved, hdefect⟩
  rcases hstatex with ⟨hvelState, hdensityState, hresidualState, hsolutionState⟩
  refine
    ⟨hvelState, hblockOp, hblockPP, hblockPQ, hblockQP, hblockQQ, hflow,
      hderiv, ?_, ?_, hdefect, hdensityState, hresidualState, hsolutionState⟩
  · calc
      realization.derivative.derivativeDatum.restriction n x =
          data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.observer.selection.selectedProjection
            (data.completionLaw.fourStateLaw.selectedAutonomousScalarLaw.generator x) := by
              exact hrestrict
      _ = data.completionLaw.fourStateLaw.selectedStateObject.project
            (data.completionLaw.fourStateLaw.selectedStateObject.generator x) := by
            rfl
  · calc
      realization.derivative.derivativeDatum.observed n x =
          data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.observer.selection.selectedProjection
            (data.completionLaw.fourStateLaw.selectedAutonomousScalarLaw.generator x) := by
              exact hobserved
      _ = data.completionLaw.fourStateLaw.selectedStateObject.project
            (data.completionLaw.fourStateLaw.selectedStateObject.generator x) := by
            rfl

end ClosureCurrent

end CoherenceCalculus
