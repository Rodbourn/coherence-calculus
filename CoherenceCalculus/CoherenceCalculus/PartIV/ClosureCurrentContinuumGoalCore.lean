import CoherenceCalculus.PartIV.ClosureCurrentContinuumLedgerCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumGoalCore

Exact adjoint-goal ledger of the detached selected quadratic density.

`ClosureCurrentContinuumLedgerCore` already shows that the forced selected
operator law has a canonical exact realization chain with no hidden crime.
This file sharpens the same surface in the direction already supported by the
rebuilt realization calculus: the selected quadratic density is also the exact
goal-error ledger of a canonical adjoint-goal certificate on the selected cut.

No new analytic structure is added. The certificate uses the identity operator
and records the selected operator only through the explicit right-hand side and
its singleton residual ledger.
-/

namespace ClosureCurrent

private def identityInverse : HasInverse AddMap.id where
  inv := AddMap.id
  left_inv := by
    intro x
    rfl
  right_inv := by
    intro x
    rfl

/-- Canonical adjoint-goal certificate whose exact goal error is the selected
quadratic density on the detached selected cut. -/
def LocalEventFourStateLaw.selectedGoalCertificate
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law)
    (x : State) :
    AdjointGoalCertificate where
  operator := AddMap.id
  inverse := identityInverse
  rhs := State.add x (data.selectedFieldLaw.operator x)
  computedState := x
  goalVector := x
  adjointWeight := x
  residualTerms := [data.selectedFieldLaw.operator x]
  adjoint_identity := by
    intro y
    rfl
  residual_split := by
    calc
      State.sub (State.add x (data.selectedFieldLaw.operator x)) x
          = data.selectedFieldLaw.operator x := by
              exact State.sub_eq_right_of_add_left rfl
      _ = stateListSum [data.selectedFieldLaw.operator x] := by
            simp [stateListSum, State.add_zero]
  weighted_residual_split := by
    calc
      State.pair x (State.sub (State.add x (data.selectedFieldLaw.operator x)) x)
          = State.pair x (data.selectedFieldLaw.operator x) := by
              rw [State.sub_eq_right_of_add_left rfl]
      _ =
          goalContributionSum
            (List.map (fun r => State.pair x r) [data.selectedFieldLaw.operator x]) := by
            simp [goalContributionSum]

/-- Manuscript-facing exact adjoint-goal surface of the detached selected
quadratic density. -/
def SelectedGoalSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  (∀ x : State,
      exactState (data.selectedGoalCertificate x) =
        State.add x (data.selectedFieldLaw.operator x)) ∧
    (∀ x : State,
      algebraicResidual (data.selectedGoalCertificate x) =
        data.selectedFieldLaw.operator x) ∧
    (∀ x : State,
      goalError (data.selectedGoalCertificate x) =
        State.pair x (algebraicResidual (data.selectedGoalCertificate x))) ∧
    (∀ x : State,
      goalError (data.selectedGoalCertificate x) =
        data.selectedQuadraticDensity x) ∧
    (∀ x : State,
      goalError (data.selectedGoalCertificate x) =
        goalContributionSum [data.selectedQuadraticDensity x]) ∧
    (∀ x : State,
      data.selectedFieldLaw.residual x =
        SignedCount.ofNat (goalError (data.selectedGoalCertificate x)))

/-- The detached selected quadratic density is already the exact goal-error
ledger of a canonical adjoint-goal certificate on the selected cut. -/
theorem LocalEventFourStateLaw.selectedGoalSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedGoalSurface data := by
  have halg :
      ∀ x : State,
        algebraicResidual (data.selectedGoalCertificate x) =
          data.selectedFieldLaw.operator x := by
    intro x
    unfold algebraicResidual LocalEventFourStateLaw.selectedGoalCertificate
      identityInverse
    exact State.sub_eq_right_of_add_left rfl
  have hgoal :
      ∀ x : State,
        goalError (data.selectedGoalCertificate x) =
          data.selectedQuadraticDensity x := by
    intro x
    have hpair :
        goalError (data.selectedGoalCertificate x) =
          State.pair x (algebraicResidual (data.selectedGoalCertificate x)) :=
      (exact_goal_error_ledger_identity (data.selectedGoalCertificate x)).1
    calc
      goalError (data.selectedGoalCertificate x) =
          State.pair x (algebraicResidual (data.selectedGoalCertificate x)) := hpair
      _ = State.pair x (data.selectedFieldLaw.operator x) := by
            rw [halg x]
      _ = data.selectedQuadraticDensity x := by
            rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rfl
  · exact halg
  · intro x
    exact (exact_goal_error_ledger_identity (data.selectedGoalCertificate x)).1
  · exact hgoal
  · intro x
    have hsplit :
        goalError (data.selectedGoalCertificate x) =
          goalContributionSum
            (List.map
              (fun r => State.pair x r)
              [data.selectedFieldLaw.operator x]) :=
      (exact_goal_error_ledger_identity (data.selectedGoalCertificate x)).2
    simpa [LocalEventFourStateLaw.selectedQuadraticDensity, goalContributionSum] using hsplit
  · intro x
    calc
      data.selectedFieldLaw.residual x =
          SignedCount.ofNat (data.selectedQuadraticDensity x) := by
            exact data.selectedScalarDensitySurface.2.1 x
      _ = SignedCount.ofNat (goalError (data.selectedGoalCertificate x)) := by
            rw [(hgoal x).symm]

end ClosureCurrent

end CoherenceCalculus
