import CoherenceCalculus.PartIV.ClosureCurrentContinuumFlagshipRealizationCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumLedgerGoalRealizationCore

Exact realization-ledger / adjoint-goal contract for any later stronger
flagship realization.

`ClosureCurrentContinuumFlagshipRealizationCore` fixes the public law data of
any later stronger flagship form. The selected cut already carries more than
that public layer: it also carries one exact no-hidden-crime realization chain
and one exact adjoint-goal certificate.

This file records the next honest boundary on the host side. Any later stronger
flagship realization that claims those same exact ledger languages on the same
selected law is already forced to agree with the detached selected cut on:

* the continuum residual,
* the terminal realized residual,
* the realized density pairing,
* the exact solved state,
* the algebraic residual,
* the exact goal error.

This still does not build the final spatial differential PDE or the final
action functional. It fixes the exact host-realization contract that any such
later flagship language must satisfy.
-/

namespace ClosureCurrent

private theorem selectedGenerator_eq_operator
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ∀ x : State,
      data.selectedAutonomousScalarLaw.generator x = data.selectedFieldLaw.operator x := by
  have hsurface :
      SelectedAutonomousScalarLawSurface data := data.selectedAutonomousScalarLawSurface
  obtain
    ⟨_hforced, _hflow, hgenerator, _hdensity, _hdensityReal, _hdensityGoal,
      _hresidual, _hresidualDensity, _hsolutionEq, _hpde, _haction,
      _hevolution⟩ :=
    hsurface
  exact hgenerator

private theorem selectedGoal_exactState
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ∀ x : State,
      exactState (data.selectedGoalCertificate x) =
        State.add x (data.selectedFieldLaw.operator x) := by
  have hsurface :
      SelectedGoalSurface data := data.selectedGoalSurface
  obtain
    ⟨hexactState, _halgebraic, _hgoalPair, _hgoalDensity, _hsingleton,
      _hresidual⟩ :=
    hsurface
  exact hexactState

private theorem selectedGoal_algebraicResidual
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ∀ x : State,
      algebraicResidual (data.selectedGoalCertificate x) =
        data.selectedFieldLaw.operator x := by
  have hsurface :
      SelectedGoalSurface data := data.selectedGoalSurface
  obtain
    ⟨_hexactState, halgebraic, _hgoalPair, _hgoalDensity, _hsingleton,
      _hresidual⟩ :=
    hsurface
  exact halgebraic

/-- Minimal stronger flagship realization on the exact host side. It keeps the
same public flagship data, then adds:

* one exact no-hidden-crime realization chain for the canonical selected law;
* one exact adjoint-goal certificate whose solved state, algebraic residual,
  and goal error are read from the same flagship velocity and density.

The point is not to invent a new law. The point is to state the smallest
stronger realization language that reaches both the realization ledger and the
adjoint-goal ledger on the selected cut. -/
structure LedgerGoalFlagshipRealization
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) where
  flagship : FlagshipRealization data
  realizationChain : RealizationChain data.selectedRealizationLaw
  trialPoint : realizationChain.trialRealization
  testPoint : State → realizationChain.testRealization
  exact_realization : realizationExact realizationChain
  exact_continuumResidual :
    ∀ x : State,
      continuumResidual realizationChain trialPoint (testPoint x) =
        flagship.velocity x
  goalCertificate : State → AdjointGoalCertificate
  exact_exactState :
    ∀ x : State,
      exactState (goalCertificate x) = State.add x (flagship.velocity x)
  exact_algebraicResidual :
    ∀ x : State,
      algebraicResidual (goalCertificate x) = flagship.velocity x
  exact_goalError :
    ∀ x : State,
      goalError (goalCertificate x) = flagship.density x

/-- The canonical exact host-side realization already carried by the detached
selected cut. -/
def LocalEventFourStateLaw.selectedLedgerGoalFlagshipRealization
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    LedgerGoalFlagshipRealization data where
  flagship := data.selectedFlagshipRealization
  realizationChain := data.selectedRealizationChain
  trialPoint := ()
  testPoint := fun x => x
  exact_realization := data.selectedRealizationExact
  exact_continuumResidual := data.selectedContinuumResidual
  goalCertificate := data.selectedGoalCertificate
  exact_exactState := by
    intro x
    exact selectedGoal_exactState data x
  exact_algebraicResidual := by
    intro x
    exact selectedGoal_algebraicResidual data x
  exact_goalError := by
    have hsurface :
        SelectedGoalSurface data := data.selectedGoalSurface
    obtain
      ⟨_hexactState, _halgebraic, _hgoalPair, hgoalDensity, _hsingleton,
        _hresidual⟩ :=
      hsurface
    intro x
    calc
      goalError (data.selectedGoalCertificate x) = data.selectedQuadraticDensity x := by
        exact hgoalDensity x
      _ = data.selectedFlagshipRealization.density x := by
        rfl

/-- The realized residual in a ledger/goal flagship realization already equals
its flagship velocity. -/
theorem LedgerGoalFlagshipRealization.realizedResidual_iff_flagshipVelocity
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : LedgerGoalFlagshipRealization data) :
    ∀ x : State,
      residualReal realization.realizationChain realization.trialPoint
          (realization.testPoint x) =
        realization.flagship.velocity x := by
  intro x
  calc
    residualReal realization.realizationChain realization.trialPoint
        (realization.testPoint x) =
        continuumResidual realization.realizationChain realization.trialPoint
          (realization.testPoint x) := by
          exact
            no_hidden_crime realization.realizationChain
              realization.exact_realization realization.trialPoint
              (realization.testPoint x)
    _ = realization.flagship.velocity x := by
          exact realization.exact_continuumResidual x

/-- Ledger/goal flagship realizations already have the same continuum residual
as the selected realization chain. -/
theorem LedgerGoalFlagshipRealization.continuumResidual_iff_selectedResidual
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : LedgerGoalFlagshipRealization data) :
    ∀ x : State,
      continuumResidual realization.realizationChain realization.trialPoint
          (realization.testPoint x) =
        continuumResidual data.selectedRealizationChain () x := by
  intro x
  calc
    continuumResidual realization.realizationChain realization.trialPoint
        (realization.testPoint x) =
        realization.flagship.velocity x := by
          exact realization.exact_continuumResidual x
    _ = data.selectedAutonomousScalarLaw.generator x := by
          exact realization.flagship.velocity_iff_selectedGenerator x
    _ = data.selectedFieldLaw.operator x := by
          exact selectedGenerator_eq_operator data x
    _ = continuumResidual data.selectedRealizationChain () x := by
          symm
          exact data.selectedContinuumResidual x

/-- Ledger/goal flagship realizations already have the same terminal realized
residual as the selected realization chain. -/
theorem LedgerGoalFlagshipRealization.realizedResidual_iff_selectedResidual
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : LedgerGoalFlagshipRealization data) :
    ∀ x : State,
      residualReal realization.realizationChain realization.trialPoint
          (realization.testPoint x) =
        residualReal data.selectedRealizationChain () x := by
  intro x
  calc
    residualReal realization.realizationChain realization.trialPoint
        (realization.testPoint x) =
        continuumResidual realization.realizationChain realization.trialPoint
          (realization.testPoint x) := by
          exact
            no_hidden_crime realization.realizationChain
              realization.exact_realization realization.trialPoint
              (realization.testPoint x)
    _ = continuumResidual data.selectedRealizationChain () x := by
          exact realization.continuumResidual_iff_selectedResidual x
    _ = residualReal data.selectedRealizationChain () x := by
          symm
          exact
            no_hidden_crime data.selectedRealizationChain
              data.selectedRealizationExact () x

/-- Ledger/goal flagship realizations already yield the same realized density
pairing as the selected quadratic density. -/
theorem LedgerGoalFlagshipRealization.realizedDensity_iff_selectedQuadraticDensity
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : LedgerGoalFlagshipRealization data) :
    ∀ x : State,
      State.pair x
          (residualReal realization.realizationChain realization.trialPoint
            (realization.testPoint x)) =
        data.selectedQuadraticDensity x := by
  intro x
  calc
    State.pair x
          (residualReal realization.realizationChain realization.trialPoint
            (realization.testPoint x)) =
        State.pair x (realization.flagship.velocity x) := by
          rw [realization.realizedResidual_iff_flagshipVelocity x]
    _ = realization.flagship.density x := by
          symm
          exact realization.flagship.density_eq x
    _ = data.selectedAutonomousScalarLaw.density x := by
          exact realization.flagship.density_iff_selectedDensity x
    _ = data.selectedQuadraticDensity x := by
          rfl

/-- Ledger/goal flagship realizations already have the same exact solved state
as the selected adjoint-goal certificate. -/
theorem LedgerGoalFlagshipRealization.exactState_iff_selectedGoal
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : LedgerGoalFlagshipRealization data) :
    ∀ x : State,
      exactState (realization.goalCertificate x) =
        exactState (data.selectedGoalCertificate x) := by
  intro x
  calc
    exactState (realization.goalCertificate x) =
        State.add x (realization.flagship.velocity x) := by
          exact realization.exact_exactState x
    _ = State.add x (data.selectedAutonomousScalarLaw.generator x) := by
          rw [realization.flagship.velocity_iff_selectedGenerator x]
    _ = State.add x (data.selectedFieldLaw.operator x) := by
          rw [selectedGenerator_eq_operator data x]
    _ = exactState (data.selectedGoalCertificate x) := by
          symm
          exact selectedGoal_exactState data x

/-- Ledger/goal flagship realizations already have the same algebraic
residual as the selected adjoint-goal certificate. -/
theorem LedgerGoalFlagshipRealization.algebraicResidual_iff_selectedGoal
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : LedgerGoalFlagshipRealization data) :
    ∀ x : State,
      algebraicResidual (realization.goalCertificate x) =
        algebraicResidual (data.selectedGoalCertificate x) := by
  intro x
  calc
    algebraicResidual (realization.goalCertificate x) =
        realization.flagship.velocity x := by
          exact realization.exact_algebraicResidual x
    _ = data.selectedAutonomousScalarLaw.generator x := by
          exact realization.flagship.velocity_iff_selectedGenerator x
    _ = data.selectedFieldLaw.operator x := by
          exact selectedGenerator_eq_operator data x
    _ = algebraicResidual (data.selectedGoalCertificate x) := by
          symm
          exact selectedGoal_algebraicResidual data x

/-- Ledger/goal flagship realizations already have the same exact goal error
as the selected adjoint-goal certificate. -/
theorem LedgerGoalFlagshipRealization.goalError_iff_selectedGoal
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : LedgerGoalFlagshipRealization data) :
    ∀ x : State,
      goalError (realization.goalCertificate x) =
        goalError (data.selectedGoalCertificate x) := by
  intro x
  calc
    goalError (realization.goalCertificate x) =
        realization.flagship.density x := by
          exact realization.exact_goalError x
    _ = goalError (data.selectedGoalCertificate x) := by
          exact realization.flagship.density_iff_goalError x

/-- Ledger/goal flagship realizations already identify the goal error with the
realized density pairing of their own terminal residual. -/
theorem LedgerGoalFlagshipRealization.goalError_iff_realizedDensity
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : LedgerGoalFlagshipRealization data) :
    ∀ x : State,
      goalError (realization.goalCertificate x) =
        State.pair x
          (residualReal realization.realizationChain realization.trialPoint
            (realization.testPoint x)) := by
  intro x
  calc
    goalError (realization.goalCertificate x) = realization.flagship.density x := by
      exact realization.exact_goalError x
    _ = State.pair x (realization.flagship.velocity x) := by
      exact realization.flagship.density_eq x
    _ =
        State.pair x
          (residualReal realization.realizationChain realization.trialPoint
            (realization.testPoint x)) := by
      rw [realization.realizedResidual_iff_flagshipVelocity x]

/-- Ledger/goal flagship realizations already have the same solution set as
the autonomous scalar law. -/
theorem LedgerGoalFlagshipRealization.solution_iff_selectedAutonomousScalarLaw
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : LedgerGoalFlagshipRealization data) :
    ∀ x : State,
      realization.flagship.solution x ↔ data.selectedAutonomousScalarLaw.solution x :=
  realization.flagship.solution_iff_selectedAutonomousScalarLaw

/-- Manuscript-facing exact host-realization contract for any later stronger
flagship realization. -/
def SelectedLedgerGoalFlagshipRealizationSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  Nonempty (LedgerGoalFlagshipRealization data) ∧
    (∀ realization : LedgerGoalFlagshipRealization data,
      realizationExact realization.realizationChain) ∧
    (∀ realization : LedgerGoalFlagshipRealization data,
      ∀ x : State,
        continuumResidual realization.realizationChain realization.trialPoint
            (realization.testPoint x) =
          continuumResidual data.selectedRealizationChain () x) ∧
    (∀ realization : LedgerGoalFlagshipRealization data,
      ∀ x : State,
        residualReal realization.realizationChain realization.trialPoint
            (realization.testPoint x) =
          residualReal data.selectedRealizationChain () x) ∧
    (∀ realization : LedgerGoalFlagshipRealization data,
      ∀ x : State,
        State.pair x
            (residualReal realization.realizationChain realization.trialPoint
              (realization.testPoint x)) =
          data.selectedQuadraticDensity x) ∧
    (∀ realization : LedgerGoalFlagshipRealization data,
      ∀ x : State,
        exactState (realization.goalCertificate x) =
          exactState (data.selectedGoalCertificate x)) ∧
    (∀ realization : LedgerGoalFlagshipRealization data,
      ∀ x : State,
        algebraicResidual (realization.goalCertificate x) =
          algebraicResidual (data.selectedGoalCertificate x)) ∧
    (∀ realization : LedgerGoalFlagshipRealization data,
      ∀ x : State,
        goalError (realization.goalCertificate x) =
          goalError (data.selectedGoalCertificate x)) ∧
    (∀ realization : LedgerGoalFlagshipRealization data,
      ∀ x : State,
        goalError (realization.goalCertificate x) =
          State.pair x
            (residualReal realization.realizationChain realization.trialPoint
              (realization.testPoint x))) ∧
    (∀ realization : LedgerGoalFlagshipRealization data,
      ∀ x : State,
        realization.flagship.solution x ↔ data.selectedAutonomousScalarLaw.solution x)

/-- Any later stronger flagship realization that claims an exact
no-hidden-crime realization chain and an exact adjoint-goal certificate is
already forced to agree with the detached selected cut on those host-side
ledger surfaces. -/
theorem LocalEventFourStateLaw.selectedLedgerGoalFlagshipRealizationSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedLedgerGoalFlagshipRealizationSurface data := by
  refine
    ⟨⟨data.selectedLedgerGoalFlagshipRealization⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩
  · intro realization
    exact realization.exact_realization
  · intro realization x
    exact realization.continuumResidual_iff_selectedResidual x
  · intro realization x
    exact realization.realizedResidual_iff_selectedResidual x
  · intro realization x
    exact realization.realizedDensity_iff_selectedQuadraticDensity x
  · intro realization x
    exact realization.exactState_iff_selectedGoal x
  · intro realization x
    exact realization.algebraicResidual_iff_selectedGoal x
  · intro realization x
    exact realization.goalError_iff_selectedGoal x
  · intro realization x
    exact realization.goalError_iff_realizedDensity x
  · intro realization x
    exact realization.solution_iff_selectedAutonomousScalarLaw x

end ClosureCurrent

end CoherenceCalculus
