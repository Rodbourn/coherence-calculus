import CoherenceCalculus.PartIV.ClosureCurrentContinuumCompositeRealizationCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumFormCore

Best current realized-form boundary of the detached selected law.

`ClosureCurrentContinuumCompositeRealizationCore` already proves that any later
stronger flagship language carrying the current public, host-ledger,
differential-flow, derivative-subsampling, and variational packages on one
selected realization collapses to one operator, one density, one scalar
residual, and one zero set.

This file restates that collapse in the most law-shaped form now honestly
available. Any such later realization is already forced to be:

* first-order and autonomous on the selected cut,
* carried by the selected generator,
* block-diagonal with vanishing `PQ/QP/QQ` pieces,
* defect-free on the selected observed restriction,
* quadratic at the density level,
* and governed by the same common selected equation.

This is still not a spatial differential PDE or a full action functional. It
is the exact realized-form boundary that any later stronger differential
language must present.
-/

namespace ClosureCurrent

private theorem selectedQuadraticDensity_eq_generatorPair
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ∀ x : State,
      data.selectedQuadraticDensity x =
        State.pair x (data.selectedAutonomousScalarLaw.generator x) := by
  have hsurface :
      SelectedAutonomousScalarLawSurface data := data.selectedAutonomousScalarLawSurface
  obtain
    ⟨_hforced, _hflow, hgenerator, hdensity, _hdensityReal, _hdensityGoal,
      _hresidual, _hresidualDensity, _hsolutionEq, _hpde, _haction,
      _hevolution⟩ :=
    hsurface
  intro x
  calc
    data.selectedQuadraticDensity x = data.selectedAutonomousScalarLaw.density x := by
      symm
      exact hdensity x
    _ = State.pair x (data.selectedAutonomousScalarLaw.generator x) := by
      exact data.selectedAutonomousScalarLaw.density_eq x

/-- Manuscript-facing realized-form boundary of the detached selected law.

Any later stronger flagship language that carries all current realization
packages on one same selected cut is already forced to present one first-order
autonomous realized form:

* the same selected generator,
* the same block-diagonal differential-flow package,
* the same defect-free selected restriction,
* the same quadratic density,
* the same scalar residual,
* the same common zero set.
-/
def SelectedRealizedFormSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  Nonempty (CompositeFlagshipRealization data) ∧
    (∀ realization : CompositeFlagshipRealization data,
      ∀ n : Nat, ∀ x : State,
        realization.flagship.velocity x =
          data.selectedAutonomousScalarLaw.generator x ∧
        realization.differential.blockDatum.operator x =
          data.selectedAutonomousScalarLaw.generator x ∧
        realization.differential.blockDatum.blockPP n x =
          data.selectedAutonomousScalarLaw.generator x ∧
        realization.differential.blockDatum.blockPQ n x = State.zero ∧
        realization.differential.blockDatum.blockQP n x = State.zero ∧
        realization.differential.blockDatum.blockQQ n x = State.zero ∧
        realization.differential.flowDatum.effectiveOp n x =
          data.selectedAutonomousScalarLaw.generator x ∧
        realization.derivative.derivativeDatum.derivative x =
          data.selectedAutonomousScalarLaw.generator x ∧
        realization.derivative.derivativeDatum.restriction n x =
          data.framed.object.bridge.selectedBridge.observer.selection.selectedProjection
            (data.selectedAutonomousScalarLaw.generator x) ∧
        realization.derivative.derivativeDatum.observed n x =
          data.framed.object.bridge.selectedBridge.observer.selection.selectedProjection
            (data.selectedAutonomousScalarLaw.generator x) ∧
        realization.derivative.derivativeDatum.defect n x = State.zero) ∧
    (∀ realization : CompositeFlagshipRealization data,
      ∀ x : State,
        realization.flagship.density x =
          State.pair x (data.selectedAutonomousScalarLaw.generator x) ∧
        realization.flagship.density x = data.selectedQuadraticDensity x ∧
        realization.flagship.residual x =
          SignedCount.ofNat
            (State.pair x (data.selectedAutonomousScalarLaw.generator x)) ∧
        realization.flagship.residual x =
          data.selectedAutonomousScalarLaw.residual x ∧
        (realization.flagship.solution x ↔ data.selectedFieldEquation x) ∧
        (realization.flagship.solution x ↔
          data.scalarPDERealization.solution x) ∧
        (realization.flagship.solution x ↔
          data.scalarActionRealization.stationary x) ∧
        (realization.flagship.solution x ↔
          data.selectedEvolutionLaw.solution x))

/-- Once the current public, host-ledger, differential-flow,
derivative-subsampling, and variational packages are carried on one selected
realization, the eventual stronger flagship form is already fixed up to
differential language: it must present the same first-order autonomous
generator, the same vanishing mixed blocks and defect, the same quadratic
density, the same scalar residual, and the same common zero set. -/
theorem LocalEventFourStateLaw.selectedRealizedFormSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedRealizedFormSurface data := by
  refine ⟨⟨data.selectedCompositeFlagshipRealization⟩, ?_, ?_⟩
  · intro realization n x
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact realization.flagship.velocity_iff_selectedGenerator x
    · calc
        realization.differential.blockDatum.operator x =
            data.selectedContinuousBlockDerivativeDatum.operator x := by
              exact realization.differential.operator_iff_selectedBlockOperator x
        _ = data.selectedDifferentialFlagshipRealization.flagship.velocity x := by
              exact data.selectedDifferentialFlagshipRealization.exact_operator x
        _ = data.selectedAutonomousScalarLaw.generator x := by
              rfl
    · calc
        realization.differential.blockDatum.blockPP n x =
            data.selectedContinuousBlockDerivativeDatum.blockPP n x := by
              exact realization.differential.blockPP_iff_selectedBlockPP n x
        _ = data.selectedAutonomousScalarLaw.generator x := by
              exact data.selectedContinuousBlockDerivativeDatum_PP n x
    · calc
        realization.differential.blockDatum.blockPQ n x =
            data.selectedContinuousBlockDerivativeDatum.blockPQ n x := by
              exact realization.differential.blockPQ_iff_selectedBlockPQ n x
        _ = State.zero := by
              exact data.selectedContinuousBlockDerivativeDatum_PQ n x
    · calc
        realization.differential.blockDatum.blockQP n x =
            data.selectedContinuousBlockDerivativeDatum.blockQP n x := by
              exact realization.differential.blockQP_iff_selectedBlockQP n x
        _ = State.zero := by
              exact data.selectedContinuousBlockDerivativeDatum_QP n x
    · calc
        realization.differential.blockDatum.blockQQ n x =
            data.selectedContinuousBlockDerivativeDatum.blockQQ n x := by
              exact realization.differential.blockQQ_iff_selectedBlockQQ n x
        _ = State.zero := by
              exact data.selectedContinuousBlockDerivativeDatum_QQ n x
    · calc
        realization.differential.flowDatum.effectiveOp n x =
            data.selectedContinuousEffectiveFlowData.effectiveOp n x := by
              exact realization.differential.flow_iff_selectedEffectiveFlow n x
        _ = data.selectedAutonomousScalarLaw.generator x := by
              calc
                data.selectedContinuousEffectiveFlowData.effectiveOp n x =
                    data.selectedDifferentialFlagshipRealization.flagship.velocity x := by
                      exact data.selectedDifferentialFlagshipRealization.exact_flow n x
                _ = data.selectedAutonomousScalarLaw.generator x := by
                      rfl
    · exact realization.derivative.derivative_iff_selectedGenerator x
    · exact realization.derivative.restriction_iff_selectedGenerator n x
    · exact realization.derivative.observed_iff_selectedGenerator n x
    · exact realization.derivative.defect_iff_zero n x
  · intro realization x
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · calc
        realization.flagship.density x =
            State.pair x (realization.flagship.velocity x) := by
              exact realization.flagship.density_eq x
        _ = State.pair x (data.selectedAutonomousScalarLaw.generator x) := by
              rw [realization.flagship.velocity_iff_selectedGenerator x]
    · calc
        realization.flagship.density x = data.selectedAutonomousScalarLaw.density x := by
          exact realization.flagship.density_iff_selectedDensity x
        _ = data.selectedQuadraticDensity x := by
          calc
            data.selectedAutonomousScalarLaw.density x =
                State.pair x (data.selectedAutonomousScalarLaw.generator x) := by
                  exact data.selectedAutonomousScalarLaw.density_eq x
            _ = data.selectedQuadraticDensity x := by
                  symm
                  exact selectedQuadraticDensity_eq_generatorPair data x
    · calc
        realization.flagship.residual x =
            SignedCount.ofNat (realization.flagship.density x) := by
              exact realization.flagship.residual_eq x
        _ = SignedCount.ofNat
              (State.pair x (data.selectedAutonomousScalarLaw.generator x)) := by
                rw [realization.flagship.density_eq x]
                rw [realization.flagship.velocity_iff_selectedGenerator x]
    · exact realization.flagship.residual_iff_selectedResidual x
    · exact realization.flagship.exact_selected_solution x
    · exact realization.flagship.solution_iff_pdeSolution x
    · exact realization.flagship.solution_iff_actionStationary x
    · exact realization.flagship.solution_iff_evolutionSolution x

end ClosureCurrent

end CoherenceCalculus
