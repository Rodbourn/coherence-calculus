import CoherenceCalculus.PartIII.ContinuumIdentificationCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumGoverningCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumFlowCore

Continuous effective-flow package of the selected governing law.

The detached analytic lane now has one common selected governing operator on
the least-motion cut. The next honest strengthening is not yet a PDE. It is
the generic Part III-type flow package attached to that operator:

* one constant selected interpolation datum on the chosen cut;
* one block-derivative package given by the actual `PP/PQ/QP/QQ` blocks of the
  selected quadratic law;
* one exact effective-flow datum whose flow already agrees with the matched
  selected generator.

This file packages that field/flow surface without adding any analytic
structure beyond the existing exact selected-cut calculus.
-/

namespace ClosureCurrent

/-- Constant selected-cut interpolation datum for the detached governing law. -/
def LocalEventFourStateLaw.selectedContinuousHorizonInterpolation
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ContinuousHorizonInterpolation Nat State :=
  let selection := data.framed.object.bridge.selectedBridge.observer.selection
  {
    projection := fun _ => selection.selectedProjection
    shadow := fun _ =>
      shadowProj selection.realization.tower selection.horizon
    operator_norm_C1 :=
      ∀ x : State,
        BridgeEventuallyEq
          (fun _ => selection.selectedProjection x)
          (selection.selectedProjection x) ∧
        BridgeEventuallyEq
          (fun _ => shadowProj selection.realization.tower selection.horizon x)
          (shadowProj selection.realization.tower selection.horizon x)
  }

/-- The constant selected interpolation is exact stagewise. -/
theorem LocalEventFourStateLaw.selectedContinuousHorizonInterpolation_exact
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    data.selectedContinuousHorizonInterpolation.operator_norm_C1 := by
  let selection := data.framed.object.bridge.selectedBridge.observer.selection
  intro x
  refine ⟨?_, ?_⟩
  · exact
      bridgeEventuallyEq_of_shift
        (fun h => selection.selectedProjection x)
        (selection.selectedProjection x)
        0
        (fun _ => rfl)
  · exact
      bridgeEventuallyEq_of_shift
        (fun h => shadowProj selection.realization.tower selection.horizon x)
        (shadowProj selection.realization.tower selection.horizon x)
        0
        (fun _ => rfl)

/-- Block-derivative datum of the selected quadratic law on the least-motion
cut. -/
def LocalEventFourStateLaw.selectedContinuousBlockDerivativeDatum
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ContinuousBlockDerivativeDatum Nat State :=
  let rep := data.toMinimalQuadraticRepresentative
  let selection := data.framed.object.bridge.selectedBridge.observer.selection
  let P := selection.selectedProjection
  {
    interpolation := data.selectedContinuousHorizonInterpolation
    operator := rep.stateForm.op
    blockPP := fun _ => blockPP P rep.stateForm.op
    blockPQ := fun _ => blockPQ P rep.stateForm.op
    blockQP := fun _ => blockQP P rep.stateForm.op
    blockQQ := fun _ => blockQQ P rep.stateForm.op
    derivative_PP :=
      ∀ _ : Nat, ∀ x : State,
        blockPP P rep.stateForm.op x =
          data.framed.object.bridge.generator.toFun x
    derivative_PQ :=
      ∀ _ : Nat, ∀ x : State,
        blockPQ P rep.stateForm.op x = State.zero
    derivative_QP :=
      ∀ _ : Nat, ∀ x : State,
        blockQP P rep.stateForm.op x = State.zero
    derivative_QQ :=
      ∀ _ : Nat, ∀ x : State,
        blockQQ P rep.stateForm.op x = State.zero
  }

/-- The `PP` block of the selected quadratic law is already the matched
selected generator. -/
theorem LocalEventFourStateLaw.selectedContinuousBlockDerivativeDatum_PP
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    data.selectedContinuousBlockDerivativeDatum.derivative_PP := by
  let rep := data.toMinimalQuadraticRepresentative
  let selection := data.framed.object.bridge.selectedBridge.observer.selection
  let P := selection.selectedProjection
  obtain
    ⟨_hadm, _hpsd, _heq, _hmin, _hmineq, _hstateForm, hgenerator⟩ :=
      data.minimalQuadraticRepresentativeSurface
  obtain
    ⟨_hadm, _hpsd, _hstateForm, _hcandidate, _hcut, _hmotion, _hstationary,
      _hgradComm, _hgradPQ, _hgradQP, hvis, _hcomm, _hzeroPQ, _hzeroQP⟩ :=
      data.stationaryQuadraticRepresentativeSurface
  intro _ x
  calc
    blockPP P rep.stateForm.op x = rep.stateForm.op x := by
      exact (hvis x).symm
    _ = data.framed.object.bridge.generator.toFun x := by
      exact hgenerator x

/-- The `PQ` block of the selected quadratic law vanishes exactly on the
least-motion cut. -/
theorem LocalEventFourStateLaw.selectedContinuousBlockDerivativeDatum_PQ
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    data.selectedContinuousBlockDerivativeDatum.derivative_PQ := by
  let rep := data.toMinimalQuadraticRepresentative
  let selection := data.framed.object.bridge.selectedBridge.observer.selection
  let P := selection.selectedProjection
  obtain
    ⟨_hadm, _hpsd, _hstateForm, _hcandidate, _hcut, _hmotion, _hstationary,
      _hgradComm, _hgradPQ, _hgradQP, _hvis, _hcomm, hzeroPQ, _hzeroQP⟩ :=
      data.stationaryQuadraticRepresentativeSurface
  intro _ x
  exact hzeroPQ x

/-- The `QP` block of the selected quadratic law vanishes exactly on the
least-motion cut. -/
theorem LocalEventFourStateLaw.selectedContinuousBlockDerivativeDatum_QP
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    data.selectedContinuousBlockDerivativeDatum.derivative_QP := by
  let rep := data.toMinimalQuadraticRepresentative
  let selection := data.framed.object.bridge.selectedBridge.observer.selection
  let P := selection.selectedProjection
  obtain
    ⟨_hadm, _hpsd, _hstateForm, _hcandidate, _hcut, _hmotion, _hstationary,
      _hgradComm, _hgradPQ, _hgradQP, _hvis, _hcomm, _hzeroPQ, hzeroQP⟩ :=
      data.stationaryQuadraticRepresentativeSurface
  intro _ x
  exact hzeroQP x

/-- The `QQ` block of the selected quadratic law vanishes exactly on the
least-motion cut. -/
theorem LocalEventFourStateLaw.selectedContinuousBlockDerivativeDatum_QQ
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    data.selectedContinuousBlockDerivativeDatum.derivative_QQ := by
  let rep := data.toMinimalQuadraticRepresentative
  let selection := data.framed.object.bridge.selectedBridge.observer.selection
  let P := selection.selectedProjection
  obtain
    ⟨_hadm, _hpsd, _hstateForm, _hcandidate, _hcut, _hmotion, _hstationary,
      _hgradComm, _hgradPQ, _hgradQP, hvis, _hcomm, _hzeroPQ, _hzeroQP⟩ :=
      data.stationaryQuadraticRepresentativeSurface
  intro _ x
  rw [blockQQ_apply]
  have hshadow :
      rep.stateForm.op (projectionShadow P x) = State.zero := by
    calc
      rep.stateForm.op (projectionShadow P x) =
          blockPP P rep.stateForm.op (projectionShadow P x) := by
            exact hvis (projectionShadow P x)
      _ = P (rep.stateForm.op (P (projectionShadow P x))) := by
            rw [operatorCompression_eq_blockPP]
      _ = P (rep.stateForm.op State.zero) := by
            rw [proj_shadow_orthogonal]
      _ = P State.zero := by
            rw [rep.stateForm.op.map_zero]
      _ = State.zero := by
            rw [P.map_zero]
  rw [hshadow]
  exact projectionShadow_zero P

/-- Exact effective-flow package of the selected governing law. The flow is
read as the exact effective selected law, which already agrees with the
matched selected generator on the least-motion cut. -/
def LocalEventFourStateLaw.selectedContinuousEffectiveFlowData
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ContinuousEffectiveFlowData Nat State :=
  let rep := data.toMinimalQuadraticRepresentative
  let bridge := data.framed.object.bridge.selectedBridge
  let selection := bridge.observer.selection
  let P := selection.selectedProjection
  let Rqq := canonicalSelectedShadowPropagator bridge
  {
    blockData := data.selectedContinuousBlockDerivativeDatum
    effectiveOp := fun _ => effectiveOp P rep.stateForm.op Rqq
    flow_is_C1 :=
      ∀ x : State,
        BridgeEventuallyEq
          (fun _ => effectiveOp P rep.stateForm.op Rqq x)
          (data.framed.object.bridge.generator.toFun x)
    flow_formula :=
      ∀ _ : Nat, ∀ x : State,
        effectiveOp P rep.stateForm.op Rqq x =
          blockPP P rep.stateForm.op x
  }

/-- The exact effective selected flow already agrees exactly with the matched
selected generator. -/
theorem LocalEventFourStateLaw.selectedContinuousEffectiveFlowData_C1
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    data.selectedContinuousEffectiveFlowData.flow_is_C1 := by
  let rep := data.toMinimalQuadraticRepresentative
  let bridge := data.framed.object.bridge.selectedBridge
  let selection := bridge.observer.selection
  let P := selection.selectedProjection
  let Rqq := canonicalSelectedShadowPropagator bridge
  obtain ⟨_hquadEff, hgoverning, _hscalarGov, _heffectiveScalarGov⟩ :=
    data.selectedGoverningSurface
  intro x
  exact
    bridgeEventuallyEq_of_shift
      (fun h => effectiveOp P rep.stateForm.op Rqq x)
      (data.framed.object.bridge.generator.toFun x)
      0
      (fun _ => hgoverning x)

/-- The exact effective selected flow is literally the `PP` block of the
selected quadratic law on the least-motion cut. -/
theorem LocalEventFourStateLaw.selectedContinuousEffectiveFlowData_formula
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    data.selectedContinuousEffectiveFlowData.flow_formula := by
  let rep := data.toMinimalQuadraticRepresentative
  let bridge := data.framed.object.bridge.selectedBridge
  let selection := bridge.observer.selection
  let P := selection.selectedProjection
  let Rqq := canonicalSelectedShadowPropagator bridge
  obtain ⟨_hselectedEff, hgoverning, _hscalarGov, _heffectiveScalarGov⟩ :=
    data.selectedGoverningSurface
  intro _ x
  calc
    effectiveOp P rep.stateForm.op Rqq x =
        data.framed.object.bridge.generator.toFun x := by
          exact hgoverning x
    _ = blockPP P rep.stateForm.op x := by
          symm
          exact data.selectedContinuousBlockDerivativeDatum_PP 0 x

/-- Generic Part III effective-flow wrapper instantiated on the detached
selected governing flow package. -/
def LocalEventFourStateLaw.selectedContinuousEffectiveFlow
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ContinuousEffectiveFlowData Nat State :=
  continuous_effective_flow data.selectedContinuousEffectiveFlowData

/-- Manuscript-facing field/flow surface of the selected governing law. -/
def SelectedGoverningFlowSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  data.selectedContinuousHorizonInterpolation.operator_norm_C1 ∧
    data.selectedContinuousBlockDerivativeDatum.derivative_PP ∧
    data.selectedContinuousBlockDerivativeDatum.derivative_PQ ∧
    data.selectedContinuousBlockDerivativeDatum.derivative_QP ∧
    data.selectedContinuousBlockDerivativeDatum.derivative_QQ ∧
    data.selectedContinuousEffectiveFlowData.flow_is_C1 ∧
    data.selectedContinuousEffectiveFlowData.flow_formula

/-- The selected governing operator already determines an exact Part III-type
continuous effective-flow package on the least-motion cut. -/
theorem LocalEventFourStateLaw.selectedGoverningFlowSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedGoverningFlowSurface data := by
  exact
    ⟨data.selectedContinuousHorizonInterpolation_exact,
      data.selectedContinuousBlockDerivativeDatum_PP,
      data.selectedContinuousBlockDerivativeDatum_PQ,
      data.selectedContinuousBlockDerivativeDatum_QP,
      data.selectedContinuousBlockDerivativeDatum_QQ,
      data.selectedContinuousEffectiveFlowData_C1,
      data.selectedContinuousEffectiveFlowData_formula⟩

end ClosureCurrent

end CoherenceCalculus
