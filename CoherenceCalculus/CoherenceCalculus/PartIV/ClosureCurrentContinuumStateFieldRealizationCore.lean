import CoherenceCalculus.PartIV.ClosureCurrentContinuumStateFieldCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumDifferentialRealizationCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumDerivativeRealizationCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumVariationalRealizationCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumStateFieldRealizationCore

Realization target surface of the canonical selected state-field law.

`ClosureCurrentContinuumStateFieldCore` identifies one canonical
`State`-valued selected state-field law on the detached selected cut.
`ClosureCurrentContinuumDifferentialRealizationCore`,
`ClosureCurrentContinuumDerivativeRealizationCore`, and
`ClosureCurrentContinuumVariationalRealizationCore` give the current stronger
languages that any later PDE/action realization would naturally use.

This file closes the next honest seam. Those stronger languages are not
targeting different law objects. They are already exact presentations of the
same selected state-field law.
-/

namespace ClosureCurrent

/-- Realization-target surface of the canonical selected state-field law.

The current differential-flow, derivative-subsampling, and variational
languages already present one same selected state-field law on the detached
selected cut. -/
def SelectedStateFieldRealizationSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  SelectedStateFieldLawSurface data ∧
    (∀ realization : DifferentialFlagshipRealization data,
      ∀ n : Nat,
        ∀ x : State,
          realization.flagship.velocity x = data.selectedStateFieldLaw.generator x ∧
            realization.blockDatum.operator x =
              data.selectedStateFieldLaw.generator x ∧
            realization.blockDatum.blockPP n x =
              data.selectedStateFieldLaw.generator x ∧
            realization.blockDatum.blockPQ n x = State.zero ∧
            realization.blockDatum.blockQP n x = State.zero ∧
            realization.blockDatum.blockQQ n x = State.zero ∧
            realization.flowDatum.effectiveOp n x =
              data.selectedStateFieldLaw.generator x ∧
            (realization.flagship.solution x ↔
              data.selectedStateFieldLaw.solution x)) ∧
    (∀ realization : DerivativeSubsamplingFlagshipRealization data,
      ∀ n : Nat,
        ∀ x : State,
          realization.derivativeDatum.projection n x =
            data.selectedStateFieldLaw.project x ∧
          realization.derivativeDatum.derivative x =
            data.selectedStateFieldLaw.generator x ∧
          realization.derivativeDatum.restriction n x =
            data.selectedStateFieldLaw.project
              (data.selectedStateFieldLaw.generator x) ∧
          realization.derivativeDatum.observed n x =
            data.selectedStateFieldLaw.project
              (data.selectedStateFieldLaw.generator x) ∧
          realization.derivativeDatum.defect n x = State.zero ∧
          (realization.flagship.solution x ↔
            data.selectedStateFieldLaw.solution x)) ∧
    (∀ realization : VariationalFlagshipRealization data,
      ∀ x : State,
        realization.dynamics.lagrangianResidual x =
          data.selectedStateFieldLaw.residual x ∧
        realization.dynamics.hamiltonianResidual x =
          data.selectedStateFieldLaw.residual x ∧
        realization.dynamics.characteristicResidual x =
          data.selectedStateFieldLaw.residual x ∧
        realization.observer.eulerianResidual x =
          data.selectedStateFieldLaw.residual x ∧
        realization.observer.lagrangianResidual x =
          data.selectedStateFieldLaw.residual x ∧
        realization.observer.characteristicResidual x =
          data.selectedStateFieldLaw.residual x ∧
        realization.projection.observer.characteristicResidual x =
          data.selectedStateFieldLaw.residual x ∧
        (realization.flagship.solution x ↔
          data.selectedStateFieldLaw.solution x))

/-- The current differential and variational flagship languages are already
exact presentations of one same selected state-field law on the detached
selected cut. -/
theorem LocalEventFourStateLaw.selectedStateFieldRealizationSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedStateFieldRealizationSurface data := by
  have hstate : SelectedStateObjectSurface data := data.selectedStateObjectSurface
  have hfield : SelectedStateFieldLawSurface data := data.selectedStateFieldLawSurface
  have haut : SelectedAutonomousScalarLawSurface data := data.selectedAutonomousScalarLawSurface
  have hdiff : SelectedDifferentialFlagshipRealizationSurface data :=
    data.selectedDifferentialFlagshipRealizationSurface
  have hderiv : SelectedDerivativeSubsamplingFlagshipSurface data :=
    data.selectedDerivativeSubsamplingFlagshipSurface
  have hvar : SelectedVariationalFlagshipRealizationSurface data :=
    data.selectedVariationalFlagshipRealizationSurface
  obtain
    ⟨_hstateObj, hstateProjectField, _hstateGeneratorField, _hstateDensity,
      _hstateResidual, _hstateResidualAut, _hstateSolution, _hstatePDE,
      _hstateAction, _hstateEvolution, _hstateComposite⟩ := hstate
  obtain
    ⟨_hfieldObj, _hfieldProjectState, _hfieldFlowAut, _hfieldGeneratorState,
      hfieldGeneratorAut, _hfieldGeneratorField, _hfieldDensityState,
      _hfieldDensityAut, _hfieldResidualState, hfieldResidualAut,
      _hfieldSolutionState, hfieldSolutionEq, _hfieldPDE, _hfieldAction,
      _hfieldEvolution, _hfieldComposite⟩ := hfield
  obtain
    ⟨_hautForced, _hautFlow, _hautGeneratorField, _hautDensity,
      _hautDensityReal, _hautDensityGoal, _hautResidualField,
      _hautResidualDensity, hautSolutionEq, _hautPDE, _hautAction,
      _hautEvolution⟩ := haut
  obtain
    ⟨_hdiffObj, hdiffVelocity, hdiffOperator, hdiffBlockPP, hdiffBlockPQ,
      hdiffBlockQP, hdiffBlockQQ, hdiffFlow, hdiffSolutionAut, _hdiffPDE,
      _hdiffAction, _hdiffEvolution⟩ := hdiff
  obtain
    ⟨_hderivObj, hderivProjection, hderivDerivative, hderivRestriction,
      hderivObserved, hderivDefect, hderivSolutionAut, _hderivPDE,
      _hderivAction, _hderivEvolution⟩ := hderiv
  obtain
    ⟨_hvarObj, hvarLagrangian, hvarHamiltonian, hvarCharacteristic,
      hvarEulerian, hvarObserverLagrangian, hvarObserverCharacteristic,
      hvarProjectionCharacteristic, hvarSolutionAut, _hvarPDE, _hvarAction,
      _hvarEvolution⟩ := hvar
  have hfieldSolutionAut :
      ∀ x : State,
        data.selectedStateFieldLaw.solution x ↔
          data.selectedAutonomousScalarLaw.solution x := by
    intro x
    exact (hfieldSolutionEq x).trans (hautSolutionEq x).symm
  have hblockOperatorAut :
      ∀ x : State,
        data.selectedContinuousBlockDerivativeDatum.operator x =
          data.selectedAutonomousScalarLaw.generator x := by
    obtain
      ⟨_hadm, _hpsd, _heq, _hmin, _hmineq, _hstateForm, hgenerator⟩ :=
      data.minimalQuadraticRepresentativeSurface
    intro x
    calc
      data.selectedContinuousBlockDerivativeDatum.operator x =
          data.framed.object.bridge.generator.toFun x := by
            exact hgenerator x
      _ = data.selectedAutonomousScalarLaw.generator x := by
            rfl
  have hblockPPAut :
      ∀ n : Nat, ∀ x : State,
        data.selectedContinuousBlockDerivativeDatum.blockPP n x =
          data.selectedAutonomousScalarLaw.generator x := by
    intro n x
    calc
      data.selectedContinuousBlockDerivativeDatum.blockPP n x =
          data.framed.object.bridge.generator.toFun x := by
            exact data.selectedContinuousBlockDerivativeDatum_PP n x
      _ = data.selectedAutonomousScalarLaw.generator x := by
            rfl
  have hflowAut :
      ∀ n : Nat, ∀ x : State,
        data.selectedContinuousEffectiveFlowData.effectiveOp n x =
          data.selectedAutonomousScalarLaw.generator x := by
    have hfirst : SelectedFirstOrderLawSurface data := data.selectedFirstOrderLawSurface
    obtain
      ⟨_hforced, _hscalar, _hgoverningFlow, hflowOp, _hflowScalar, _hequation,
        _hpde, _haction⟩ := hfirst
    intro n x
    calc
      data.selectedContinuousEffectiveFlowData.effectiveOp n x =
          data.selectedFieldLaw.operator x := by
            exact hflowOp n x
      _ = data.selectedAutonomousScalarLaw.generator x := by
            rfl
  have hlagrangianAut :
      ∀ x : State,
        (regularSystem data).lagrangianResidual x =
          data.selectedAutonomousScalarLaw.residual x := by
    intro x
    calc
      (regularSystem data).lagrangianResidual x =
          data.selectedVariationalFlagshipRealization.flagship.residual x := by
            exact data.selectedVariationalFlagshipRealization.exact_lagrangian x
      _ = data.selectedAutonomousScalarLaw.residual x := by
            rfl
  have hhamiltonianAut :
      ∀ x : State,
        (regularSystem data).hamiltonianResidual x =
          data.selectedAutonomousScalarLaw.residual x := by
    intro x
    calc
      (regularSystem data).hamiltonianResidual x =
          data.selectedVariationalFlagshipRealization.flagship.residual x := by
            exact data.selectedVariationalFlagshipRealization.exact_hamiltonian x
      _ = data.selectedAutonomousScalarLaw.residual x := by
            rfl
  have hcharacteristicAut :
      ∀ x : State,
        (regularSystem data).characteristicResidual x =
          data.selectedAutonomousScalarLaw.residual x := by
    intro x
    calc
      (regularSystem data).characteristicResidual x =
          data.selectedVariationalFlagshipRealization.flagship.residual x := by
            exact data.selectedVariationalFlagshipRealization.exact_characteristic x
      _ = data.selectedAutonomousScalarLaw.residual x := by
            rfl
  have heulerianAut :
      ∀ x : State,
        (observerTransport data).eulerianResidual x =
          data.selectedAutonomousScalarLaw.residual x := by
    intro x
    calc
      (observerTransport data).eulerianResidual x =
          data.selectedVariationalFlagshipRealization.flagship.residual x := by
            exact data.selectedVariationalFlagshipRealization.exact_eulerian x
      _ = data.selectedAutonomousScalarLaw.residual x := by
            rfl
  have hobserverLagrangianAut :
      ∀ x : State,
        (observerTransport data).lagrangianResidual x =
          data.selectedAutonomousScalarLaw.residual x := by
    intro x
    calc
      (observerTransport data).lagrangianResidual x =
          data.selectedVariationalFlagshipRealization.flagship.residual x := by
            exact data.selectedVariationalFlagshipRealization.exact_observerLagrangian x
      _ = data.selectedAutonomousScalarLaw.residual x := by
            rfl
  have hobserverCharacteristicAut :
      ∀ x : State,
        (observerTransport data).characteristicResidual x =
          data.selectedAutonomousScalarLaw.residual x := by
    intro x
    calc
      (observerTransport data).characteristicResidual x =
          data.selectedVariationalFlagshipRealization.flagship.residual x := by
            exact data.selectedVariationalFlagshipRealization.exact_observerCharacteristic x
      _ = data.selectedAutonomousScalarLaw.residual x := by
            rfl
  have hprojectionCharacteristicAut :
      ∀ x : State,
        (projectionDatum data).observer.characteristicResidual x =
          data.selectedAutonomousScalarLaw.residual x := by
    intro x
    calc
      (projectionDatum data).observer.characteristicResidual x =
          (observerTransport data).characteristicResidual x := by
            rfl
      _ = data.selectedVariationalFlagshipRealization.flagship.residual x := by
            exact data.selectedVariationalFlagshipRealization.exact_observerCharacteristic x
      _ = data.selectedAutonomousScalarLaw.residual x := by
            rfl
  refine ⟨data.selectedStateFieldLawSurface, ?_, ?_, ?_⟩
  · intro realization n x
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · calc
        realization.flagship.velocity x = data.selectedAutonomousScalarLaw.generator x := by
          exact hdiffVelocity realization x
        _ = data.selectedStateFieldLaw.generator x := by
          symm
          exact hfieldGeneratorAut x
    · calc
        realization.blockDatum.operator x =
            data.selectedContinuousBlockDerivativeDatum.operator x := by
              exact hdiffOperator realization x
        _ = data.selectedAutonomousScalarLaw.generator x := by
              exact hblockOperatorAut x
        _ = data.selectedStateFieldLaw.generator x := by
              symm
              exact hfieldGeneratorAut x
    · calc
        realization.blockDatum.blockPP n x =
            data.selectedContinuousBlockDerivativeDatum.blockPP n x := by
              exact hdiffBlockPP realization n x
        _ = data.selectedAutonomousScalarLaw.generator x := by
              exact hblockPPAut n x
        _ = data.selectedStateFieldLaw.generator x := by
              symm
              exact hfieldGeneratorAut x
    · calc
        realization.blockDatum.blockPQ n x =
            data.selectedContinuousBlockDerivativeDatum.blockPQ n x := by
              exact hdiffBlockPQ realization n x
        _ = State.zero := by
              exact data.selectedContinuousBlockDerivativeDatum_PQ n x
    · calc
        realization.blockDatum.blockQP n x =
            data.selectedContinuousBlockDerivativeDatum.blockQP n x := by
              exact hdiffBlockQP realization n x
        _ = State.zero := by
              exact data.selectedContinuousBlockDerivativeDatum_QP n x
    · calc
        realization.blockDatum.blockQQ n x =
            data.selectedContinuousBlockDerivativeDatum.blockQQ n x := by
              exact hdiffBlockQQ realization n x
        _ = State.zero := by
              exact data.selectedContinuousBlockDerivativeDatum_QQ n x
    · calc
        realization.flowDatum.effectiveOp n x =
            data.selectedContinuousEffectiveFlowData.effectiveOp n x := by
              exact hdiffFlow realization n x
        _ = data.selectedAutonomousScalarLaw.generator x := by
              exact hflowAut n x
        _ = data.selectedStateFieldLaw.generator x := by
              symm
              exact hfieldGeneratorAut x
    · exact (hdiffSolutionAut realization x).trans (hfieldSolutionAut x).symm
  · intro realization n x
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · calc
        realization.derivativeDatum.projection n x =
            data.framed.object.bridge.selectedBridge.observer.selection.selectedProjection x := by
              exact hderivProjection realization n x
        _ = data.selectedFieldLaw.project x := by
              rfl
        _ = data.selectedStateObject.project x := by
              symm
              exact hstateProjectField x
        _ = data.selectedStateFieldLaw.project x := by
              rfl
    · calc
        realization.derivativeDatum.derivative x =
            data.selectedAutonomousScalarLaw.generator x := by
              exact hderivDerivative realization x
        _ = data.selectedStateFieldLaw.generator x := by
              symm
              exact hfieldGeneratorAut x
    · calc
        realization.derivativeDatum.restriction n x =
            data.framed.object.bridge.selectedBridge.observer.selection.selectedProjection
              (data.selectedAutonomousScalarLaw.generator x) := by
                exact hderivRestriction realization n x
        _ = data.selectedStateFieldLaw.project
              (data.selectedStateFieldLaw.generator x) := by
              rw [hfieldGeneratorAut x]
              rfl
    · calc
        realization.derivativeDatum.observed n x =
            data.framed.object.bridge.selectedBridge.observer.selection.selectedProjection
              (data.selectedAutonomousScalarLaw.generator x) := by
                exact hderivObserved realization n x
        _ = data.selectedStateFieldLaw.project
              (data.selectedStateFieldLaw.generator x) := by
              rw [hfieldGeneratorAut x]
              rfl
    · exact hderivDefect realization n x
    · exact (hderivSolutionAut realization x).trans (hfieldSolutionAut x).symm
  · intro realization x
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · calc
        realization.dynamics.lagrangianResidual x =
            (regularSystem data).lagrangianResidual x := by
              exact hvarLagrangian realization x
        _ = data.selectedAutonomousScalarLaw.residual x := by
              exact hlagrangianAut x
        _ = data.selectedStateFieldLaw.residual x := by
              symm
              exact hfieldResidualAut x
    · calc
        realization.dynamics.hamiltonianResidual x =
            (regularSystem data).hamiltonianResidual x := by
              exact hvarHamiltonian realization x
        _ = data.selectedAutonomousScalarLaw.residual x := by
              exact hhamiltonianAut x
        _ = data.selectedStateFieldLaw.residual x := by
              symm
              exact hfieldResidualAut x
    · calc
        realization.dynamics.characteristicResidual x =
            (regularSystem data).characteristicResidual x := by
              exact hvarCharacteristic realization x
        _ = data.selectedAutonomousScalarLaw.residual x := by
              exact hcharacteristicAut x
        _ = data.selectedStateFieldLaw.residual x := by
              symm
              exact hfieldResidualAut x
    · calc
        realization.observer.eulerianResidual x =
            (observerTransport data).eulerianResidual x := by
              exact hvarEulerian realization x
        _ = data.selectedAutonomousScalarLaw.residual x := by
              exact heulerianAut x
        _ = data.selectedStateFieldLaw.residual x := by
              symm
              exact hfieldResidualAut x
    · calc
        realization.observer.lagrangianResidual x =
            (observerTransport data).lagrangianResidual x := by
              exact hvarObserverLagrangian realization x
        _ = data.selectedAutonomousScalarLaw.residual x := by
              exact hobserverLagrangianAut x
        _ = data.selectedStateFieldLaw.residual x := by
              symm
              exact hfieldResidualAut x
    · calc
        realization.observer.characteristicResidual x =
            (observerTransport data).characteristicResidual x := by
              exact hvarObserverCharacteristic realization x
        _ = data.selectedAutonomousScalarLaw.residual x := by
              exact hobserverCharacteristicAut x
        _ = data.selectedStateFieldLaw.residual x := by
              symm
              exact hfieldResidualAut x
    · calc
        realization.projection.observer.characteristicResidual x =
            (projectionDatum data).observer.characteristicResidual x := by
              exact hvarProjectionCharacteristic realization x
        _ = data.selectedAutonomousScalarLaw.residual x := by
              exact hprojectionCharacteristicAut x
        _ = data.selectedStateFieldLaw.residual x := by
              symm
              exact hfieldResidualAut x
    · exact (hvarSolutionAut realization x).trans (hfieldSolutionAut x).symm

end ClosureCurrent

end CoherenceCalculus
