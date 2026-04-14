import CoherenceCalculus.PartIV.ClosureCurrentContinuumLedgerGoalRealizationCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumDifferentialRealizationCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumDerivativeRealizationCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumVariationalRealizationCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumCompositeRealizationCore

Combined stronger-realization contract on the detached selected cut.

The current detached selected cut already carries several exact contract layers
for any later stronger flagship language:

* the public flagship contract,
* the exact realization-ledger / adjoint-goal contract,
* the differential-flow contract,
* the derivative-subsampling contract,
* the variational / observer / Hamilton-Jacobi contract.

This file records the next honest collapse. Once those later languages are all
carried on one and the same selected realization, they no longer describe
independent data. They already collapse to one common:

* operator,
* density,
* residual,
* zero set.

So before any final spatial differential PDE or full action functional is
constructed, the exact combined pre-PDE contract is already fixed.
-/

namespace ClosureCurrent

private theorem selectedOperator_eq_generator
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ∀ x : State,
      data.selectedFieldLaw.operator x = data.selectedAutonomousScalarLaw.generator x := by
  have hsurface :
      SelectedAutonomousScalarLawSurface data := data.selectedAutonomousScalarLawSurface
  obtain
    ⟨_hforced, _hflow, hgenerator, _hdensity, _hdensityReal, _hdensityGoal,
      _hresidual, _hresidualDensity, _hsolutionEq, _hpde, _haction,
      _hevolution⟩ :=
    hsurface
  intro x
  symm
  exact hgenerator x

private theorem selectedGoal_eq_density
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ∀ x : State,
      goalError (data.selectedGoalCertificate x) = data.selectedQuadraticDensity x := by
  have hsurface :
      SelectedGoalSurface data := data.selectedGoalSurface
  obtain
    ⟨_hexactState, _halgebraic, _hgoalPair, hgoalDensity, _hsingleton,
      _hresidual⟩ :=
    hsurface
  exact hgoalDensity

/-- Combined stronger-realization language on the detached selected cut. All
component packages are required to live on the same flagship realization. -/
structure CompositeFlagshipRealization
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) where
  flagship : FlagshipRealization data
  ledgerGoal : LedgerGoalFlagshipRealization data
  differential : DifferentialFlagshipRealization data
  derivative : DerivativeSubsamplingFlagshipRealization data
  variational : VariationalFlagshipRealization data
  ledgerGoal_flagship : ledgerGoal.flagship = flagship
  differential_flagship : differential.flagship = flagship
  derivative_flagship : derivative.flagship = flagship
  variational_flagship : variational.flagship = flagship

/-- The canonical combined realization already carried by the detached selected
cut. -/
def LocalEventFourStateLaw.selectedCompositeFlagshipRealization
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    CompositeFlagshipRealization data where
  flagship := data.selectedFlagshipRealization
  ledgerGoal := data.selectedLedgerGoalFlagshipRealization
  differential := data.selectedDifferentialFlagshipRealization
  derivative := data.selectedDerivativeSubsamplingFlagshipRealization
  variational := data.selectedVariationalFlagshipRealization
  ledgerGoal_flagship := rfl
  differential_flagship := rfl
  derivative_flagship := rfl
  variational_flagship := rfl

/-- In any combined stronger realization, all state-valued operator surfaces
already collapse to the same selected generator. -/
theorem CompositeFlagshipRealization.operatorCollapse
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : CompositeFlagshipRealization data) :
    ∀ x : State,
      continuumResidual realization.ledgerGoal.realizationChain
          realization.ledgerGoal.trialPoint
          (realization.ledgerGoal.testPoint x) =
        data.selectedAutonomousScalarLaw.generator x ∧
      residualReal realization.ledgerGoal.realizationChain
          realization.ledgerGoal.trialPoint
          (realization.ledgerGoal.testPoint x) =
        data.selectedAutonomousScalarLaw.generator x ∧
      realization.differential.blockDatum.operator x =
        data.selectedAutonomousScalarLaw.generator x ∧
      realization.derivative.derivativeDatum.derivative x =
        data.selectedAutonomousScalarLaw.generator x ∧
      realization.flagship.velocity x =
        data.selectedAutonomousScalarLaw.generator x := by
  intro x
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc
      continuumResidual realization.ledgerGoal.realizationChain
          realization.ledgerGoal.trialPoint
          (realization.ledgerGoal.testPoint x) =
          continuumResidual data.selectedRealizationChain () x := by
            exact realization.ledgerGoal.continuumResidual_iff_selectedResidual x
      _ = data.selectedFieldLaw.operator x := by
            exact data.selectedContinuumResidual x
      _ = data.selectedAutonomousScalarLaw.generator x := by
            exact selectedOperator_eq_generator data x
  · calc
      residualReal realization.ledgerGoal.realizationChain
          realization.ledgerGoal.trialPoint
          (realization.ledgerGoal.testPoint x) =
      residualReal data.selectedRealizationChain () x := by
            exact realization.ledgerGoal.realizedResidual_iff_selectedResidual x
      _ = continuumResidual data.selectedRealizationChain () x := by
            exact
              no_hidden_crime data.selectedRealizationChain
                data.selectedRealizationExact () x
      _ = data.selectedFieldLaw.operator x := by
            exact data.selectedContinuumResidual x
      _ = data.selectedAutonomousScalarLaw.generator x := by
            exact selectedOperator_eq_generator data x
  · calc
      realization.differential.blockDatum.operator x =
          data.selectedContinuousBlockDerivativeDatum.operator x := by
            exact realization.differential.operator_iff_selectedBlockOperator x
      _ = data.selectedDifferentialFlagshipRealization.flagship.velocity x := by
            exact data.selectedDifferentialFlagshipRealization.exact_operator x
      _ = data.selectedAutonomousScalarLaw.generator x := by
            rfl
  · exact realization.derivative.derivative_iff_selectedGenerator x
  · exact realization.flagship.velocity_iff_selectedGenerator x

/-- In any combined stronger realization, all density-style surfaces already
collapse to the same selected quadratic density. -/
theorem CompositeFlagshipRealization.densityCollapse
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : CompositeFlagshipRealization data) :
    ∀ x : State,
      realization.flagship.density x = data.selectedQuadraticDensity x ∧
      State.pair x
          (residualReal realization.ledgerGoal.realizationChain
            realization.ledgerGoal.trialPoint
            (realization.ledgerGoal.testPoint x)) =
        data.selectedQuadraticDensity x ∧
      goalError (realization.ledgerGoal.goalCertificate x) =
        data.selectedQuadraticDensity x := by
  intro x
  refine ⟨?_, ?_, ?_⟩
  · calc
      realization.flagship.density x = data.selectedAutonomousScalarLaw.density x := by
        exact realization.flagship.density_iff_selectedDensity x
      _ = data.selectedQuadraticDensity x := by
        rfl
  · exact realization.ledgerGoal.realizedDensity_iff_selectedQuadraticDensity x
  · calc
      goalError (realization.ledgerGoal.goalCertificate x) =
          goalError (data.selectedGoalCertificate x) := by
            exact realization.ledgerGoal.goalError_iff_selectedGoal x
      _ = data.selectedQuadraticDensity x := by
            exact selectedGoal_eq_density data x

/-- In any combined stronger realization, all scalar-residual surfaces already
collapse to the same selected residual. -/
theorem CompositeFlagshipRealization.residualCollapse
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : CompositeFlagshipRealization data) :
    ∀ x : State,
      realization.flagship.residual x = data.selectedAutonomousScalarLaw.residual x ∧
      realization.variational.dynamics.lagrangianResidual x =
        data.selectedAutonomousScalarLaw.residual x ∧
      realization.variational.dynamics.hamiltonianResidual x =
        data.selectedAutonomousScalarLaw.residual x ∧
      realization.variational.dynamics.characteristicResidual x =
        data.selectedAutonomousScalarLaw.residual x ∧
      realization.variational.observer.eulerianResidual x =
        data.selectedAutonomousScalarLaw.residual x ∧
      realization.variational.observer.lagrangianResidual x =
        data.selectedAutonomousScalarLaw.residual x ∧
      realization.variational.observer.characteristicResidual x =
        data.selectedAutonomousScalarLaw.residual x ∧
      realization.variational.projection.observer.characteristicResidual x =
        data.selectedAutonomousScalarLaw.residual x := by
  intro x
  have hflag :
      realization.flagship.residual x = data.selectedAutonomousScalarLaw.residual x := by
    exact realization.flagship.residual_iff_selectedResidual x
  refine ⟨hflag, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      realization.variational.dynamics.lagrangianResidual x =
          realization.variational.flagship.residual x := by
            exact realization.variational.exact_lagrangian x
      _ = realization.flagship.residual x := by
            rw [realization.variational_flagship]
      _ = data.selectedAutonomousScalarLaw.residual x := hflag
  · calc
      realization.variational.dynamics.hamiltonianResidual x =
          realization.variational.flagship.residual x := by
            exact realization.variational.exact_hamiltonian x
      _ = realization.flagship.residual x := by
            rw [realization.variational_flagship]
      _ = data.selectedAutonomousScalarLaw.residual x := hflag
  · calc
      realization.variational.dynamics.characteristicResidual x =
          realization.variational.flagship.residual x := by
            exact realization.variational.exact_characteristic x
      _ = realization.flagship.residual x := by
            rw [realization.variational_flagship]
      _ = data.selectedAutonomousScalarLaw.residual x := hflag
  · calc
      realization.variational.observer.eulerianResidual x =
          realization.variational.flagship.residual x := by
            exact realization.variational.exact_eulerian x
      _ = realization.flagship.residual x := by
            rw [realization.variational_flagship]
      _ = data.selectedAutonomousScalarLaw.residual x := hflag
  · calc
      realization.variational.observer.lagrangianResidual x =
          realization.variational.flagship.residual x := by
            exact realization.variational.exact_observerLagrangian x
      _ = realization.flagship.residual x := by
            rw [realization.variational_flagship]
      _ = data.selectedAutonomousScalarLaw.residual x := hflag
  · calc
      realization.variational.observer.characteristicResidual x =
          realization.variational.flagship.residual x := by
            exact realization.variational.exact_observerCharacteristic x
      _ = realization.flagship.residual x := by
            rw [realization.variational_flagship]
      _ = data.selectedAutonomousScalarLaw.residual x := hflag
  · calc
      realization.variational.projection.observer.characteristicResidual x =
          realization.variational.observer.characteristicResidual x := by
            rw [realization.variational.projection_uses_observer]
      _ = realization.variational.flagship.residual x := by
            exact realization.variational.exact_observerCharacteristic x
      _ = realization.flagship.residual x := by
            rw [realization.variational_flagship]
      _ = data.selectedAutonomousScalarLaw.residual x := hflag

/-- In any combined stronger realization, every zero-set surface already
collapses to the same selected equation. -/
theorem CompositeFlagshipRealization.solutionCollapse
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : CompositeFlagshipRealization data) :
    ∀ x : State,
      (realization.flagship.solution x ↔ data.selectedFieldEquation x) ∧
      (realization.flagship.solution x ↔ data.selectedAutonomousScalarLaw.solution x) ∧
      (realization.flagship.solution x ↔ data.scalarPDERealization.solution x) ∧
      (realization.flagship.solution x ↔ data.scalarActionRealization.stationary x) ∧
      (realization.flagship.solution x ↔ data.selectedEvolutionLaw.solution x) := by
  intro x
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact realization.flagship.exact_selected_solution x
  · exact realization.flagship.solution_iff_selectedAutonomousScalarLaw x
  · exact realization.flagship.solution_iff_pdeSolution x
  · exact realization.flagship.solution_iff_actionStationary x
  · exact realization.flagship.solution_iff_evolutionSolution x

/-- Manuscript-facing exact combined pre-PDE contract on the detached selected
cut. Once a later stronger flagship language carries the current public,
ledger, differential, derivative, and variational packages on one same
selected realization, those packages already collapse to one operator, one
density, one residual, and one zero set. -/
def SelectedCompositeFlagshipRealizationSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  Nonempty (CompositeFlagshipRealization data) ∧
    (∀ realization : CompositeFlagshipRealization data,
      ∀ x : State,
        continuumResidual realization.ledgerGoal.realizationChain
            realization.ledgerGoal.trialPoint
            (realization.ledgerGoal.testPoint x) =
          data.selectedAutonomousScalarLaw.generator x ∧
        residualReal realization.ledgerGoal.realizationChain
            realization.ledgerGoal.trialPoint
            (realization.ledgerGoal.testPoint x) =
          data.selectedAutonomousScalarLaw.generator x ∧
        realization.differential.blockDatum.operator x =
          data.selectedAutonomousScalarLaw.generator x ∧
        realization.derivative.derivativeDatum.derivative x =
          data.selectedAutonomousScalarLaw.generator x ∧
        realization.flagship.velocity x =
          data.selectedAutonomousScalarLaw.generator x) ∧
    (∀ realization : CompositeFlagshipRealization data,
      ∀ x : State,
        realization.flagship.density x = data.selectedQuadraticDensity x ∧
        State.pair x
            (residualReal realization.ledgerGoal.realizationChain
              realization.ledgerGoal.trialPoint
              (realization.ledgerGoal.testPoint x)) =
          data.selectedQuadraticDensity x ∧
        goalError (realization.ledgerGoal.goalCertificate x) =
          data.selectedQuadraticDensity x) ∧
    (∀ realization : CompositeFlagshipRealization data,
      ∀ x : State,
        realization.flagship.residual x =
          data.selectedAutonomousScalarLaw.residual x ∧
        realization.variational.dynamics.lagrangianResidual x =
          data.selectedAutonomousScalarLaw.residual x ∧
        realization.variational.dynamics.hamiltonianResidual x =
          data.selectedAutonomousScalarLaw.residual x ∧
        realization.variational.dynamics.characteristicResidual x =
          data.selectedAutonomousScalarLaw.residual x ∧
        realization.variational.observer.eulerianResidual x =
          data.selectedAutonomousScalarLaw.residual x ∧
        realization.variational.observer.lagrangianResidual x =
          data.selectedAutonomousScalarLaw.residual x ∧
        realization.variational.observer.characteristicResidual x =
          data.selectedAutonomousScalarLaw.residual x ∧
        realization.variational.projection.observer.characteristicResidual x =
          data.selectedAutonomousScalarLaw.residual x) ∧
    (∀ realization : CompositeFlagshipRealization data,
      ∀ x : State,
        (realization.flagship.solution x ↔ data.selectedFieldEquation x) ∧
        (realization.flagship.solution x ↔
          data.selectedAutonomousScalarLaw.solution x) ∧
        (realization.flagship.solution x ↔ data.scalarPDERealization.solution x) ∧
        (realization.flagship.solution x ↔
          data.scalarActionRealization.stationary x) ∧
        (realization.flagship.solution x ↔ data.selectedEvolutionLaw.solution x))

/-- The detached selected cut already fixes the exact combined pre-PDE
contract. Any later stronger flagship language carrying all current realization
packages on one same selected realization is already forced to collapse to one
operator, one density, one residual, and one zero set. -/
theorem LocalEventFourStateLaw.selectedCompositeFlagshipRealizationSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedCompositeFlagshipRealizationSurface data := by
  refine ⟨⟨data.selectedCompositeFlagshipRealization⟩, ?_, ?_, ?_, ?_⟩
  · intro realization x
    exact realization.operatorCollapse x
  · intro realization x
    exact realization.densityCollapse x
  · intro realization x
    exact realization.residualCollapse x
  · intro realization x
    exact realization.solutionCollapse x

end ClosureCurrent

end CoherenceCalculus
