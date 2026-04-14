import CoherenceCalculus.PartIV.ClosureCurrentContinuumMinimalCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumStationaryCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumEffectiveCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumEffectiveVariationalCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumGoverningCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumFlowCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumPromotionCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumFieldCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumFieldForceCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumRealizationCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumLedgerCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumGoalCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumScalarCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumFirstOrderCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumEvolutionCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumEvolutionRealizationCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumAutonomousScalarCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumFlagshipRealizationCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumLedgerGoalRealizationCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumDifferentialRealizationCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumDerivativeRealizationCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumVariationalRealizationCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumCompositeRealizationCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumFormCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumStateObjectCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumStateFieldCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumStateFieldRealizationCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumVariationalCore
import CoherenceCalculus.PartIV.ClosureCurrentFlagshipCompletionCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentFlagshipAnalyticCore

Strongest current analytic flagship surface of the detached law.

`ClosureCurrentContinuumVariationalCore` identifies the strongest current
analytic representative of the detached no-stage four-state law itself: an
admissible selected quadratic operator together with its exact scalarized
variational/transport triad.

`ClosureCurrentFlagshipCompletionCore` closes the remaining flagship seam by
packaging the exact endpoint witnesses needed for the phase, wave, gauge, and
geometric recognizable identities on the same intrinsically selected bundle.

This file combines those two already established surfaces without adding any
new analytic structure. The point is to expose one manuscript-facing theorem:
once the endpoint-complete no-stage law is assumed, the current formal surface
already carries both the strongest analytic representative now available and
the four recognizable textbook flagship identities on the same selected datum.
-/

namespace ClosureCurrent

/-- Proposition packaging the strongest current analytic flagship surface
carried by the endpoint-complete no-stage law. It combines:

* the internally reconstructed Part IV completion surface,
* the admissible selected quadratic representative and its exact scalarized
  variational/transport triad,
* the four recognizable textbook flagship identities on the same selected
  datum.

This is intentionally a packaging proposition rather than a stronger primitive:
it records the best analytic surface currently forced from the endpoint-complete
law without claiming a full PDE, Lagrangian, or Hamiltonian flow theory. -/
def AnalyticFlagshipSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) : Prop :=
  let law := data.completionLaw.fourStateLaw
  let rep := law.toMinimalQuadraticRepresentative
  let selection := law.framed.object.bridge.selectedBridge.observer.selection
  let P := selection.selectedProjection
  let proj := projectionDatum law
  PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
    Compiler.Admissible rep.stateForm ∧
    Compiler.QuadForm.IsPSD rep.stateForm ∧
    Compiler.QuadForm.IsGEquivariant' rep.symmetry rep.representation rep.stateForm ∧
    (∀ Q' : Compiler.QuadForm,
      Compiler.QuadForm.IsPSD Q' →
      Q' ≤ rep.stateForm →
      Q'.op = rep.stateForm.op) ∧
    (∀ Q' : Compiler.QuadForm,
      Compiler.QuadForm.IsGEquivariant' rep.symmetry rep.representation Q' →
      Compiler.QuadForm.IsPSD Q' →
      Q' ≤ rep.stateForm →
      Q'.op = rep.stateForm.op) ∧
    P = selectedCandidateProjection selection ∧
    P = selection.realization.tower.π selection.horizon ∧
    (∀ i : Fin (Nat.succ selection.candidates.size),
      observerMotionValue selection ≤
        selection.objective.eval (selection.candidates.elem i)) ∧
    isStationaryFor selection.gradient P ∧
    (∀ x : State,
      projectionCommutator (selection.gradient.gradient P) P x = State.zero) ∧
    hasZeroPQ P (selection.gradient.gradient P) ∧
    hasZeroQP P (selection.gradient.gradient P) ∧
    exactVisibleOnCut P rep.stateForm.op ∧
    commutesWithProjection P rep.stateForm.op ∧
    hasZeroPQ P rep.stateForm.op ∧
    hasZeroQP P rep.stateForm.op ∧
    (∀ x : State,
      rep.stateForm.op x =
        effectiveOp P rep.stateForm.op
          (canonicalSelectedShadowPropagator
            law.framed.object.bridge.selectedBridge) x) ∧
    (∀ x : State,
      effectiveOp P rep.stateForm.op
          (canonicalSelectedShadowPropagator
            law.framed.object.bridge.selectedBridge) x =
        law.framed.object.bridge.generator.toFun x) ∧
    law.selectedContinuousHorizonInterpolation.operator_norm_C1 ∧
    law.selectedContinuousBlockDerivativeDatum.derivative_PP ∧
    law.selectedContinuousBlockDerivativeDatum.derivative_PQ ∧
    law.selectedContinuousBlockDerivativeDatum.derivative_QP ∧
    law.selectedContinuousBlockDerivativeDatum.derivative_QQ ∧
    law.selectedContinuousEffectiveFlowData.flow_is_C1 ∧
    law.selectedContinuousEffectiveFlowData.flow_formula ∧
    SelectedFieldLawSurface law ∧
    SelectedFieldLawForcingSurface law ∧
    SelectedPromotionSurface law ∧
    (∀ x : State,
      schurComplement P rep.stateForm.op
          (canonicalSelectedShadowPropagator
            law.framed.object.bridge.selectedBridge) x = State.zero) ∧
    (∀ x : State,
      returnedResidual
          (residualReturnFieldOf P rep.stateForm.op
            (canonicalSelectedShadowPropagator
              law.framed.object.bridge.selectedBridge)) x =
        State.zero) ∧
    (∀ x : State,
      effectiveScalarResidual law x = scalarResidual law x) ∧
    (∀ x : State,
      effectiveScalarResidual law x =
        SignedCount.ofNat
          (State.pair x (law.framed.object.bridge.generator.toFun x))) ∧
    (∀ x : State,
      scalarResidual law x =
        SignedCount.ofNat
          (State.pair x (rep.stateForm.op x))) ∧
    (∀ x : State,
      scalarResidual law x =
        SignedCount.ofNat
          (State.pair x (law.framed.object.bridge.generator.toFun x))) ∧
    SelectedScalarLawSurface law ∧
    SelectedFirstOrderLawSurface law ∧
    SelectedEvolutionLawSurface law ∧
    SelectedEvolutionRealizationSurface law ∧
    SelectedAutonomousScalarLawSurface law ∧
    SelectedFlagshipRealizationSurface law ∧
    SelectedLedgerGoalFlagshipRealizationSurface law ∧
    SelectedDifferentialFlagshipRealizationSurface law ∧
    SelectedDerivativeSubsamplingFlagshipSurface law ∧
    SelectedVariationalFlagshipRealizationSurface law ∧
    SelectedCompositeFlagshipRealizationSurface law ∧
    SelectedRealizedFormSurface law ∧
    SelectedStateObjectSurface law ∧
    SelectedStateFieldLawSurface law ∧
    SelectedStateFieldRealizationSurface law ∧
    ((∀ q : State,
        (regularSystem law).lagrangianResidual q = SignedCount.zero) ↔
      (∀ p : State,
          (regularSystem law).hamiltonianResidual p = SignedCount.zero) ∧
        (∀ q : State,
          (regularSystem law).characteristicResidual q = SignedCount.zero)) ∧
    (EulerianPresentation (observerTransport law) ↔
      LagrangianPresentation (observerTransport law) ∧
        CharacteristicPresentation (observerTransport law)) ∧
    (CharacteristicPresentation proj.observer ↔
      ∀ q : State,
        proj.dynamics.characteristicResidual q = SignedCount.zero) ∧
    (∀ q : State,
      proj.observer.characteristicResidual q =
        proj.dynamics.characteristicResidual q) ∧
    proj.dynamics = regularSystem law ∧
    proj.observer = observerTransport law ∧
    rep.stateForm =
      selected_observed_law
        law.framed.object.bridge.selectedBridge.observer.selection ∧
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

/-- The endpoint-complete no-stage law already carries the strongest current
analytic flagship surface. The analytic representative and the recognizable
textbook identities are read on the same selected datum from the same assumed
law-side package. -/
theorem LocalEventFourStateFlagshipLaw.analyticSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    AnalyticFlagshipSurface data := by
  obtain
    ⟨hcompletion, hphase, hwave, hgauge, hgeometric⟩ := data.surface
  obtain
    ⟨hadm, hpsd, heq, hmin, hmineq, _hstateForm, _hgen⟩ :=
    data.completionLaw.fourStateLaw.minimalQuadraticRepresentativeSurface
  obtain
    ⟨_hadm', _hpsd', _hstateForm', hcandidate, hcut, hmotion, hstationary,
      hgradComm, hgradPQ, hgradQP, hvis, hcomm, hzeroPQ, hzeroQP⟩ :=
    data.completionLaw.fourStateLaw.stationaryQuadraticRepresentativeSurface
  obtain
    ⟨_hvis', heff, hschur, hreturn⟩ :=
    data.completionLaw.fourStateLaw.effectiveQuadraticRepresentativeSurface
  obtain
    ⟨_hselectedEff, hgoverning, _hscalarGov, _heffectiveScalarGov⟩ :=
    data.completionLaw.fourStateLaw.selectedGoverningSurface
  obtain
    ⟨hinterp, hPP, hPQ, hQP, hQQ, hflowC1, hflowFormula⟩ :=
    data.completionLaw.fourStateLaw.selectedGoverningFlowSurface
  have hfield :
      SelectedFieldLawSurface data.completionLaw.fourStateLaw :=
    data.completionLaw.fourStateLaw.selectedFieldLawSurface
  have hfieldForced :
      SelectedFieldLawForcingSurface data.completionLaw.fourStateLaw :=
    data.completionLaw.fourStateLaw.selectedFieldLawForcingSurface
  have hpromotion :
      SelectedPromotionSurface data.completionLaw.fourStateLaw :=
    data.completionLaw.fourStateLaw.selectedPromotionSurface
  have hscalarLaw :
      SelectedScalarLawSurface data.completionLaw.fourStateLaw :=
    data.completionLaw.fourStateLaw.selectedScalarLawSurface
  have hfirstOrder :
      SelectedFirstOrderLawSurface data.completionLaw.fourStateLaw :=
    data.completionLaw.fourStateLaw.selectedFirstOrderLawSurface
  have hevolution :
      SelectedEvolutionLawSurface data.completionLaw.fourStateLaw :=
    data.completionLaw.fourStateLaw.selectedEvolutionLawSurface
  have hevolutionRealization :
      SelectedEvolutionRealizationSurface data.completionLaw.fourStateLaw :=
    data.completionLaw.fourStateLaw.selectedEvolutionRealizationSurface
  have hautonomousScalar :
      SelectedAutonomousScalarLawSurface data.completionLaw.fourStateLaw :=
    data.completionLaw.fourStateLaw.selectedAutonomousScalarLawSurface
  have hflagshipRealization :
      SelectedFlagshipRealizationSurface data.completionLaw.fourStateLaw :=
    data.completionLaw.fourStateLaw.selectedFlagshipRealizationSurface
  have hledgerGoalRealization :
      SelectedLedgerGoalFlagshipRealizationSurface
        data.completionLaw.fourStateLaw :=
    data.completionLaw.fourStateLaw.selectedLedgerGoalFlagshipRealizationSurface
  have hdifferentialRealization :
      SelectedDifferentialFlagshipRealizationSurface
        data.completionLaw.fourStateLaw :=
    data.completionLaw.fourStateLaw.selectedDifferentialFlagshipRealizationSurface
  have hderivativeSubsampling :
      SelectedDerivativeSubsamplingFlagshipSurface
        data.completionLaw.fourStateLaw :=
    data.completionLaw.fourStateLaw.selectedDerivativeSubsamplingFlagshipSurface
  have hvariationalRealization :
      SelectedVariationalFlagshipRealizationSurface
        data.completionLaw.fourStateLaw :=
    data.completionLaw.fourStateLaw.selectedVariationalFlagshipRealizationSurface
  have hcompositeRealization :
      SelectedCompositeFlagshipRealizationSurface
        data.completionLaw.fourStateLaw :=
    data.completionLaw.fourStateLaw.selectedCompositeFlagshipRealizationSurface
  have hrealizedForm :
      SelectedRealizedFormSurface data.completionLaw.fourStateLaw :=
    data.completionLaw.fourStateLaw.selectedRealizedFormSurface
  have hstateObject :
      SelectedStateObjectSurface data.completionLaw.fourStateLaw :=
    data.completionLaw.fourStateLaw.selectedStateObjectSurface
  have hstateField :
      SelectedStateFieldLawSurface data.completionLaw.fourStateLaw :=
    data.completionLaw.fourStateLaw.selectedStateFieldLawSurface
  have hstateFieldRealization :
      SelectedStateFieldRealizationSurface data.completionLaw.fourStateLaw :=
    data.completionLaw.fourStateLaw.selectedStateFieldRealizationSurface
  obtain
    ⟨heffScalar, heffGen, _hdynEff, _hobsEff, _hprojEff, _hprojEqEff⟩ :=
    data.completionLaw.fourStateLaw.effectiveVariationalRepresentativeSurface
  obtain
    ⟨hquad, hscalarQuad, hscalarGen, hdynamics, hobserver, hprojection,
      hcharacteristic, hdyn, hobs, hstateForm⟩ :=
    data.completionLaw.fourStateLaw.variationalRepresentativeSurface
  exact
    ⟨hcompletion,
      hadm,
      hpsd,
      heq,
      hmin,
      hmineq,
      hcandidate,
      hcut,
      hmotion,
      hstationary,
      hgradComm,
      hgradPQ,
      hgradQP,
      hvis,
      hcomm,
      hzeroPQ,
      hzeroQP,
      heff,
      hgoverning,
      hinterp,
      hPP,
      hPQ,
      hQP,
      hQQ,
      hflowC1,
      hflowFormula,
      hfield,
      hfieldForced,
      hpromotion,
      hschur,
      hreturn,
      heffScalar,
      heffGen,
      hscalarQuad,
      hscalarGen,
      hscalarLaw,
      hfirstOrder,
      hevolution,
      hevolutionRealization,
      hautonomousScalar,
      hflagshipRealization,
      hledgerGoalRealization,
      hdifferentialRealization,
      hderivativeSubsampling,
      hvariationalRealization,
      hcompositeRealization,
      hrealizedForm,
      hstateObject,
      hstateField,
      hstateFieldRealization,
      hdynamics,
      hobserver,
      hprojection,
      hcharacteristic,
      hdyn,
      hobs,
      hstateForm,
      hphase,
      hwave,
      hgauge,
      hgeometric⟩

end ClosureCurrent

end CoherenceCalculus
