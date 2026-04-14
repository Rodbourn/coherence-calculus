import CoherenceCalculus.PartIV.ClosureCurrentContinuumGoalCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumScalarCore

One canonical scalar law object on the detached selected cut.

`ClosureCurrentContinuumGoalCore` leaves the current scalar flagship surface
spread across several honest but separate statements:

* the selected equation and its PDE/action realization boundary,
* the canonical scalar PDE-form and action-form realizations,
* the explicit selected quadratic density,
* the exact no-hidden-crime realization ledger,
* the exact adjoint-goal ledger.

This file does not add a new law. It packages those already established
surfaces into one manuscript-facing theorem: before any genuinely differential
PDE or full action functional appears, the detached selected cut already
carries one canonical scalar law object.
-/

namespace ClosureCurrent

/-- One canonical scalar law object on the detached selected cut. The same
selected equation, scalar PDE-form realization, scalar action-form
realization, density scalarization, exact realized residual, and exact
adjoint-goal ledger are all presentations of the same scalar law. -/
def SelectedScalarLawSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  SelectedEquationRealizationSurface data ∧
    SelectedEquationExistenceSurface data ∧
    SelectedScalarRealizationSurface data ∧
    SelectedScalarDensitySurface data ∧
    SelectedLedgerSurface data ∧
    SelectedGoalSurface data ∧
    (∀ x : State,
      data.selectedQuadraticDensity x =
        State.pair x (residualReal data.selectedRealizationChain () x)) ∧
    (∀ x : State,
      goalError (data.selectedGoalCertificate x) =
        data.selectedQuadraticDensity x) ∧
    (∀ x : State,
      data.selectedFieldLaw.residual x =
        data.scalarPDERealization.equation x ∧
      data.scalarPDERealization.equation x =
        data.scalarActionRealization.eulerLagrange x ∧
      data.scalarActionRealization.eulerLagrange x =
        SignedCount.ofNat (data.selectedQuadraticDensity x) ∧
      data.scalarActionRealization.eulerLagrange x =
        SignedCount.ofNat
          (State.pair x (residualReal data.selectedRealizationChain () x)) ∧
      data.scalarActionRealization.eulerLagrange x =
        SignedCount.ofNat
          (goalError (data.selectedGoalCertificate x))) ∧
    (∀ x : State,
      data.selectedFieldEquation x ↔
        data.scalarPDERealization.solution x ∧
          data.scalarActionRealization.stationary x ∧
          SignedCount.ofNat (data.selectedQuadraticDensity x) = SignedCount.zero ∧
          SignedCount.ofNat
            (State.pair x (residualReal data.selectedRealizationChain () x)) =
              SignedCount.zero ∧
          SignedCount.ofNat (goalError (data.selectedGoalCertificate x)) =
            SignedCount.zero)

/-- The detached selected cut already carries one canonical scalar law object.
The selected equation, scalar PDE/action realizations, explicit density, exact
realized residual, and exact adjoint-goal ledger are all presentations of the
same scalar law. -/
theorem LocalEventFourStateLaw.selectedScalarLawSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedScalarLawSurface data := by
  have hrealization :
      SelectedEquationRealizationSurface data :=
    data.selectedEquationRealizationSurface
  have hexistence :
      SelectedEquationExistenceSurface data :=
    data.selectedEquationExistenceSurface
  have hscalar :
      SelectedScalarRealizationSurface data :=
    data.selectedScalarRealizationSurface
  have hdensity :
      SelectedScalarDensitySurface data :=
    data.selectedScalarDensitySurface
  have hledger :
      SelectedLedgerSurface data :=
    data.selectedLedgerSurface
  have hgoal :
      SelectedGoalSurface data :=
    data.selectedGoalSurface
  have hscalarSurface := hscalar
  have hdensitySurface := hdensity
  have hledgerSurface := hledger
  have hgoalSurface := hgoal
  obtain ⟨hpdeResidual, hactionResidual, _hpdeAction⟩ := hscalarSurface
  obtain
    ⟨_hdensityOp, hresDensity, _hpdeDensity, hactionDensity, _hpdeActionDensity⟩ :=
    hdensitySurface
  obtain
    ⟨_hexactLedger, _hrealContinuum, _hcontinuumOperator, _hrealOperator,
      hdensityReal, hresReal⟩ :=
    hledgerSurface
  obtain
    ⟨_hexactState, _halgebraic, _hgoalPair, hgoalDensity, _hgoalSingleton,
      hresGoal⟩ :=
    hgoalSurface
  refine
    ⟨hrealization, hexistence, hscalar, hdensity, hledger, hgoal,
      hdensityReal, hgoalDensity, ?_, ?_⟩
  · intro x
    refine ⟨(hpdeResidual x).symm, ?_, ?_, ?_, ?_⟩
    · calc
        data.scalarPDERealization.equation x =
            data.selectedFieldLaw.residual x := by
              exact hpdeResidual x
        _ = data.scalarActionRealization.eulerLagrange x := by
              exact (hactionResidual x).symm
    · exact hactionDensity x
    · calc
        data.scalarActionRealization.eulerLagrange x =
            data.selectedFieldLaw.residual x := by
              exact hactionResidual x
        _ =
            SignedCount.ofNat
              (State.pair x (residualReal data.selectedRealizationChain () x)) := by
              exact hresReal x
    · calc
        data.scalarActionRealization.eulerLagrange x =
            data.selectedFieldLaw.residual x := by
              exact hactionResidual x
        _ = SignedCount.ofNat (goalError (data.selectedGoalCertificate x)) := by
              exact hresGoal x
  · intro x
    constructor
    · intro hx
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact (data.scalarPDERealization.solution_iff_selectedEquation x).2 hx
      · exact (data.scalarActionRealization.stationary_iff_selectedEquation x).2 hx
      · calc
          SignedCount.ofNat (data.selectedQuadraticDensity x) =
              data.selectedFieldLaw.residual x := by
                exact (hresDensity x).symm
          _ = SignedCount.zero := by
                simpa [LocalEventFourStateLaw.selectedFieldEquation] using hx
      · calc
          SignedCount.ofNat
              (State.pair x (residualReal data.selectedRealizationChain () x)) =
              data.selectedFieldLaw.residual x := by
                exact (hresReal x).symm
          _ = SignedCount.zero := by
                simpa [LocalEventFourStateLaw.selectedFieldEquation] using hx
      · calc
          SignedCount.ofNat (goalError (data.selectedGoalCertificate x)) =
              data.selectedFieldLaw.residual x := by
                exact (hresGoal x).symm
          _ = SignedCount.zero := by
                simpa [LocalEventFourStateLaw.selectedFieldEquation] using hx
    · intro h
      exact (data.scalarPDERealization.solution_iff_selectedEquation x).1 h.1

end ClosureCurrent

end CoherenceCalculus
