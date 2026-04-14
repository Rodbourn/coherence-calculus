import CoherenceCalculus.PartIV.ClosureCurrentContinuumAutonomousScalarCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumFlagshipRealizationCore

Contract surface for any later stronger flagship realization.

`ClosureCurrentContinuumAutonomousScalarCore` identifies the strongest current
law object honestly forced on the detached selected cut: one uniquely forced
autonomous scalar law carrying the selected flow, selected operator, selected
quadratic density, and selected scalar residual.

This file records the next honest consequence. Any later stronger flagship
language that claims to realize this law and exposes the same public data:

* a velocity field,
* a scalar density,
* a scalar residual,
* a solution set,

is already forced to agree with the autonomous scalar law on all four of those
public surfaces. This does not yet build a genuinely spatial differential PDE
or a full action functional. It fixes the contract that any such later
realization must satisfy.
-/

namespace ClosureCurrent

/-- Minimal public realization surface for any later stronger flagship form of
the detached selected law. -/
structure FlagshipRealization
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) where
  velocity : State → State
  density : State → Nat
  residual : State → SignedCount
  solution : State → Prop
  admissible_velocity : data.stateDynamics.limitClass.admissible velocity
  density_eq : ∀ x : State, density x = State.pair x (velocity x)
  residual_eq : ∀ x : State, residual x = SignedCount.ofNat (density x)
  solution_eq : ∀ x : State, solution x ↔ residual x = SignedCount.zero
  exact_selected_solution : ∀ x : State, solution x ↔ data.selectedFieldEquation x

/-- The canonical flagship realization read directly from the autonomous scalar
law. -/
def LocalEventFourStateLaw.selectedFlagshipRealization
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    FlagshipRealization data where
  velocity := data.selectedAutonomousScalarLaw.generator
  density := data.selectedAutonomousScalarLaw.density
  residual := data.selectedAutonomousScalarLaw.residual
  solution := data.selectedAutonomousScalarLaw.solution
  admissible_velocity := by
    exact data.selectedAutonomousScalarLaw_admissible
  density_eq := data.selectedAutonomousScalarLaw.density_eq
  residual_eq := data.selectedAutonomousScalarLaw.residual_eq
  solution_eq := by
    intro x
    rfl
  exact_selected_solution := by
    have hsurface :
        SelectedAutonomousScalarLawSurface data := data.selectedAutonomousScalarLawSurface
    obtain
      ⟨_hforced, _hflow, _hgenerator, _hdensity, _hdensityReal, _hdensityGoal,
        _hresidual, _hresidualDensity, hsolutionEq, _hpde, _haction,
        _hevolution⟩ :=
      hsurface
    intro x
    exact hsolutionEq x

/-- Any flagship realization has the same velocity as the autonomous scalar
law. -/
theorem FlagshipRealization.velocity_iff_selectedGenerator
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : FlagshipRealization data) :
    ∀ x : State,
      realization.velocity x = data.selectedAutonomousScalarLaw.generator x := by
  intro x
  exact data.stateDynamics.limitClass_pointwise_forcing
    realization.admissible_velocity x

/-- Any flagship realization has the same density as the autonomous scalar law. -/
theorem FlagshipRealization.density_iff_selectedDensity
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : FlagshipRealization data) :
    ∀ x : State,
      realization.density x = data.selectedAutonomousScalarLaw.density x := by
  intro x
  calc
    realization.density x = State.pair x (realization.velocity x) := by
      exact realization.density_eq x
    _ = State.pair x (data.selectedAutonomousScalarLaw.generator x) := by
      rw [realization.velocity_iff_selectedGenerator x]
    _ = data.selectedAutonomousScalarLaw.density x := by
      symm
      exact data.selectedAutonomousScalarLaw.density_eq x

/-- Any flagship realization has the same residual as the autonomous scalar
law. -/
theorem FlagshipRealization.residual_iff_selectedResidual
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : FlagshipRealization data) :
    ∀ x : State,
      realization.residual x = data.selectedAutonomousScalarLaw.residual x := by
  intro x
  calc
    realization.residual x = SignedCount.ofNat (realization.density x) := by
      exact realization.residual_eq x
    _ = SignedCount.ofNat (data.selectedAutonomousScalarLaw.density x) := by
      rw [realization.density_iff_selectedDensity x]
    _ = data.selectedAutonomousScalarLaw.residual x := by
      symm
      exact data.selectedAutonomousScalarLaw.residual_eq x

/-- Any flagship realization has the same solution set as the autonomous scalar
law. -/
theorem FlagshipRealization.solution_iff_selectedAutonomousScalarLaw
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : FlagshipRealization data) :
    ∀ x : State,
      realization.solution x ↔ data.selectedAutonomousScalarLaw.solution x := by
  have hsurface :
      SelectedAutonomousScalarLawSurface data := data.selectedAutonomousScalarLawSurface
  obtain
    ⟨_hforced, _hflow, _hgenerator, _hdensity, _hdensityReal, _hdensityGoal,
      _hresidual, _hresidualDensity, hsolutionEq, _hpde, _haction,
      _hevolution⟩ :=
    hsurface
  intro x
  constructor
  · intro hx
    exact (hsolutionEq x).2
      ((realization.exact_selected_solution x).1 hx)
  · intro hx
    exact (realization.exact_selected_solution x).2
      ((hsolutionEq x).1 hx)

/-- Any flagship realization has the same density as the explicit
realized-residual pairing. -/
theorem FlagshipRealization.density_iff_realizedResidual
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : FlagshipRealization data) :
    ∀ x : State,
      realization.density x =
        State.pair x (residualReal data.selectedRealizationChain () x) := by
  have hsurface :
      SelectedAutonomousScalarLawSurface data := data.selectedAutonomousScalarLawSurface
  obtain
    ⟨_hforced, _hflow, _hgenerator, _hdensity, hdensityReal, _hdensityGoal,
      _hresidual, _hresidualDensity, _hsolutionEq, _hpde, _haction,
      _hevolution⟩ :=
    hsurface
  intro x
  calc
    realization.density x = data.selectedAutonomousScalarLaw.density x := by
      exact realization.density_iff_selectedDensity x
    _ = State.pair x (residualReal data.selectedRealizationChain () x) := by
      exact hdensityReal x

/-- Any flagship realization has the same density as the exact adjoint-goal
error. -/
theorem FlagshipRealization.density_iff_goalError
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : FlagshipRealization data) :
    ∀ x : State,
      realization.density x = goalError (data.selectedGoalCertificate x) := by
  have hsurface :
      SelectedAutonomousScalarLawSurface data := data.selectedAutonomousScalarLawSurface
  obtain
    ⟨_hforced, _hflow, _hgenerator, _hdensity, _hdensityReal, hdensityGoal,
      _hresidual, _hresidualDensity, _hsolutionEq, _hpde, _haction,
      _hevolution⟩ :=
    hsurface
  intro x
  calc
    realization.density x = data.selectedAutonomousScalarLaw.density x := by
      exact realization.density_iff_selectedDensity x
    _ = goalError (data.selectedGoalCertificate x) := by
      exact hdensityGoal x

/-- Any flagship realization has the same solution set as the canonical scalar
PDE-form realization. -/
theorem FlagshipRealization.solution_iff_pdeSolution
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : FlagshipRealization data) :
    ∀ x : State,
      realization.solution x ↔ data.scalarPDERealization.solution x := by
  have hsurface :
      SelectedAutonomousScalarLawSurface data := data.selectedAutonomousScalarLawSurface
  obtain
    ⟨_hforced, _hflow, _hgenerator, _hdensity, _hdensityReal, _hdensityGoal,
      _hresidual, _hresidualDensity, _hsolutionEq, hpde, _haction,
      _hevolution⟩ :=
    hsurface
  intro x
  exact (realization.solution_iff_selectedAutonomousScalarLaw x).trans
    (hpde x)

/-- Any flagship realization has the same solution set as the canonical scalar
action-form realization. -/
theorem FlagshipRealization.solution_iff_actionStationary
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : FlagshipRealization data) :
    ∀ x : State,
      realization.solution x ↔ data.scalarActionRealization.stationary x := by
  have hsurface :
      SelectedAutonomousScalarLawSurface data := data.selectedAutonomousScalarLawSurface
  obtain
    ⟨_hforced, _hflow, _hgenerator, _hdensity, _hdensityReal, _hdensityGoal,
      _hresidual, _hresidualDensity, _hsolutionEq, _hpde, haction,
      _hevolution⟩ :=
    hsurface
  intro x
  exact (realization.solution_iff_selectedAutonomousScalarLaw x).trans
    (haction x)

/-- Any flagship realization has the same solution set as the autonomous
evolution law. -/
theorem FlagshipRealization.solution_iff_evolutionSolution
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : FlagshipRealization data) :
    ∀ x : State,
      realization.solution x ↔ data.selectedEvolutionLaw.solution x := by
  have hsurface :
      SelectedAutonomousScalarLawSurface data := data.selectedAutonomousScalarLawSurface
  obtain
    ⟨_hforced, _hflow, _hgenerator, _hdensity, _hdensityReal, _hdensityGoal,
      _hresidual, _hresidualDensity, _hsolutionEq, _hpde, _haction,
      hevolution⟩ :=
    hsurface
  intro x
  exact (realization.solution_iff_selectedAutonomousScalarLaw x).trans
    (hevolution x)

/-- Manuscript-facing contract surface for any later stronger flagship
realization. -/
def SelectedFlagshipRealizationSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  Nonempty (FlagshipRealization data) ∧
    (∀ realization : FlagshipRealization data,
      ∀ x : State,
        realization.velocity x = data.selectedAutonomousScalarLaw.generator x) ∧
    (∀ realization : FlagshipRealization data,
      ∀ x : State,
        realization.density x = data.selectedAutonomousScalarLaw.density x) ∧
    (∀ realization : FlagshipRealization data,
      ∀ x : State,
        realization.density x =
          State.pair x (residualReal data.selectedRealizationChain () x)) ∧
    (∀ realization : FlagshipRealization data,
      ∀ x : State,
        realization.density x = goalError (data.selectedGoalCertificate x)) ∧
    (∀ realization : FlagshipRealization data,
      ∀ x : State,
        realization.residual x = data.selectedAutonomousScalarLaw.residual x) ∧
    (∀ realization : FlagshipRealization data,
      ∀ x : State,
        realization.solution x ↔ data.selectedAutonomousScalarLaw.solution x) ∧
    (∀ realization : FlagshipRealization data,
      ∀ x : State,
        realization.solution x ↔ data.scalarPDERealization.solution x) ∧
    (∀ realization : FlagshipRealization data,
      ∀ x : State,
        realization.solution x ↔ data.scalarActionRealization.stationary x) ∧
    (∀ realization : FlagshipRealization data,
      ∀ x : State,
        realization.solution x ↔ data.selectedEvolutionLaw.solution x)

/-- Any later stronger flagship realization that exposes a velocity field, a
scalar density, a scalar residual, and a solution set is already forced to
agree with the autonomous scalar law on all four public surfaces. -/
theorem LocalEventFourStateLaw.selectedFlagshipRealizationSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedFlagshipRealizationSurface data := by
  refine ⟨⟨data.selectedFlagshipRealization⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro realization x
    exact realization.velocity_iff_selectedGenerator x
  · intro realization x
    exact realization.density_iff_selectedDensity x
  · intro realization x
    exact realization.density_iff_realizedResidual x
  · intro realization x
    exact realization.density_iff_goalError x
  · intro realization x
    exact realization.residual_iff_selectedResidual x
  · intro realization x
    exact realization.solution_iff_selectedAutonomousScalarLaw x
  · intro realization x
    exact realization.solution_iff_pdeSolution x
  · intro realization x
    exact realization.solution_iff_actionStationary x
  · intro realization x
    exact realization.solution_iff_evolutionSolution x

end ClosureCurrent

end CoherenceCalculus
