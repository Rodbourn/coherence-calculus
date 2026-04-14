import CoherenceCalculus.PartIV.ClosureCurrentContinuumEquationCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumRealizationCore

Realization surfaces of the forced selected equation.

`ClosureCurrentContinuumEquationCore` identifies the strongest current honest
equation surface on the detached selected cut: one uniquely forced scalar
equation

`r_sel(x) = 0`.

This file does two things and keeps the boundary between them explicit.

* First, it proves the rigidity statement: any later PDE-form or
  action-principle flagship language must realize that same selected equation.
* Second, it records the strongest current existence theorem now honestly
  available: canonical scalar PDE-form and scalar action-form realizations,
  together with the concrete selected quadratic density whose signed-count
  scalarization gives those residual fields.

This is still not a spatial differential PDE or a full action functional.
The point is only to expose the strongest current realization surface already
forced by the detached selected law itself.
-/

namespace ClosureCurrent

/-- A PDE realization of the detached selected equation. The realization is
kept minimal: one residual type, one zero element, and the exact zero-set
identification with the forced selected equation. -/
structure PDERealization
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) where
  Residual : Type
  zero : Residual
  equation : State → Residual
  exact_zero_set : ∀ x : State, equation x = zero ↔ data.selectedFieldEquation x

/-- The solution set of a PDE realization. -/
def PDERealization.solution
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : PDERealization data) :
    State → Prop :=
  fun x => realization.equation x = realization.zero

/-- An action realization of the detached selected equation. Again the
interface is minimal: one residual type, one zero element, and the exact
stationary-set identification with the forced selected equation. -/
structure ActionRealization
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) where
  Residual : Type
  zero : Residual
  eulerLagrange : State → Residual
  exact_zero_set :
    ∀ x : State, eulerLagrange x = zero ↔ data.selectedFieldEquation x

/-- The stationary set of an action realization. -/
def ActionRealization.stationary
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : ActionRealization data) :
    State → Prop :=
  fun x => realization.eulerLagrange x = realization.zero

/-- A PDE realization has exactly the same solution set as the forced selected
equation. -/
theorem PDERealization.solution_iff_selectedEquation
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : PDERealization data) :
    ∀ x : State, realization.solution x ↔ data.selectedFieldEquation x :=
  realization.exact_zero_set

/-- An action realization has exactly the same stationary set as the forced
selected equation. -/
theorem ActionRealization.stationary_iff_selectedEquation
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : ActionRealization data) :
    ∀ x : State, realization.stationary x ↔ data.selectedFieldEquation x :=
  realization.exact_zero_set

/-- Any PDE realization and any action realization of the detached selected
equation already have the same solution set. -/
theorem PDERealization.solution_iff_actionStationary
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (pde : PDERealization data)
    (action : ActionRealization data) :
    ∀ x : State, pde.solution x ↔ action.stationary x := by
  intro x
  constructor
  · intro hx
    exact (action.stationary_iff_selectedEquation x).2
      ((pde.solution_iff_selectedEquation x).1 hx)
  · intro hx
    exact (pde.solution_iff_selectedEquation x).2
      ((action.stationary_iff_selectedEquation x).1 hx)

/-- Manuscript-facing realization boundary of the detached selected equation.
The selected operator-residual law and its common equation are already forced,
and any later PDE or action realization must share that same zero set. -/
def SelectedEquationRealizationSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  SelectedFieldLawForcingSurface data ∧
    SelectedFieldEquationSurface data ∧
    (∀ realization : PDERealization data,
      ∀ x : State, realization.solution x ↔ data.selectedFieldEquation x) ∧
    (∀ realization : ActionRealization data,
      ∀ x : State, realization.stationary x ↔ data.selectedFieldEquation x) ∧
    (∀ pde : PDERealization data,
      ∀ action : ActionRealization data,
        ∀ x : State, pde.solution x ↔ action.stationary x)

/-- Any later PDE or action-principle flagship form of the detached selected
law must realize the same uniquely forced selected equation. It does not add a
new law; it only presents the same zero set in a different analytic language.
-/
theorem LocalEventFourStateLaw.selectedEquationRealizationSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedEquationRealizationSurface data := by
  refine ⟨data.selectedFieldLawForcingSurface, data.selectedFieldEquationSurface, ?_, ?_, ?_⟩
  · intro realization x
    exact realization.solution_iff_selectedEquation x
  · intro realization x
    exact realization.stationary_iff_selectedEquation x
  · intro pde action x
    exact pde.solution_iff_actionStationary action x

/-- The canonical scalar PDE-form realization of the detached selected
equation. This is the strongest current honest PDE existence statement: the
residual field is exactly the already forced selected scalar residual. -/
def LocalEventFourStateLaw.scalarPDERealization
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    PDERealization data where
  Residual := SignedCount
  zero := SignedCount.zero
  equation := data.selectedFieldLaw.residual
  exact_zero_set := by
    intro x
    rfl

/-- The canonical scalar action-form realization of the detached selected
equation. At the current honest surface this is an Euler--Lagrange residual
field, not yet a full action functional. -/
def LocalEventFourStateLaw.scalarActionRealization
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ActionRealization data where
  Residual := SignedCount
  zero := SignedCount.zero
  eulerLagrange := data.selectedFieldLaw.residual
  exact_zero_set := by
    intro x
    rfl

/-- Manuscript-facing existence surface for the current PDE-form and
action-form realizations of the detached selected equation. -/
def SelectedEquationExistenceSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  Nonempty (PDERealization data) ∧
    Nonempty (ActionRealization data) ∧
    (∀ x : State,
      data.scalarPDERealization.equation x = data.selectedFieldLaw.residual x) ∧
    (∀ x : State,
      data.scalarActionRealization.eulerLagrange x = data.selectedFieldLaw.residual x) ∧
    (∀ x : State,
      data.scalarPDERealization.solution x ↔ data.selectedFieldEquation x) ∧
    (∀ x : State,
      data.scalarActionRealization.stationary x ↔ data.selectedFieldEquation x) ∧
    (∀ x : State,
      data.scalarPDERealization.solution x ↔
        data.scalarActionRealization.stationary x)

/-- Manuscript-facing identification of the current PDE-form and action-form
realizations with one common scalar residual field. -/
def SelectedScalarRealizationSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  (∀ x : State,
      data.scalarPDERealization.equation x = data.selectedFieldLaw.residual x) ∧
    (∀ x : State,
      data.scalarActionRealization.eulerLagrange x = data.selectedFieldLaw.residual x) ∧
    (∀ x : State,
      data.scalarPDERealization.equation x =
        data.scalarActionRealization.eulerLagrange x)

/-- The detached selected equation already admits canonical scalar PDE-form and
action-form realizations. These are existence results for realizations, not yet
for a spatial differential PDE or a full action functional. -/
theorem LocalEventFourStateLaw.selectedEquationExistenceSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedEquationExistenceSurface data := by
  refine ⟨⟨data.scalarPDERealization⟩, ⟨data.scalarActionRealization⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    rfl
  · intro x
    exact data.scalarPDERealization.solution_iff_selectedEquation x
  · intro x
    exact data.scalarActionRealization.stationary_iff_selectedEquation x
  · intro x
    exact data.scalarPDERealization.solution_iff_actionStationary
      data.scalarActionRealization x

/-- The current PDE-form and action-form realizations are not different
analytic laws. They are exactly the same scalar residual field read in two
presentation languages. -/
theorem LocalEventFourStateLaw.selectedScalarRealizationSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedScalarRealizationSurface data := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    rfl
  · intro x
    rfl

/-- Concrete quadratic density on the selected state space whose signed-count
scalarization is the forced selected residual. This is still weaker than a
full action functional: it records only the explicit pointwise density already
present on the current detached selected cut. -/
def LocalEventFourStateLaw.selectedQuadraticDensity
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    State → Nat :=
  fun x => State.pair x (data.selectedFieldLaw.operator x)

/-- The canonical scalar PDE-form and action-form realizations are both the
signed-count scalarization of one concrete selected quadratic density. -/
def SelectedScalarDensitySurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  (∀ x : State,
      data.selectedQuadraticDensity x =
        State.pair x (data.selectedFieldLaw.operator x)) ∧
    (∀ x : State,
      data.selectedFieldLaw.residual x =
        SignedCount.ofNat (data.selectedQuadraticDensity x)) ∧
    (∀ x : State,
      data.scalarPDERealization.equation x =
        SignedCount.ofNat (data.selectedQuadraticDensity x)) ∧
    (∀ x : State,
      data.scalarActionRealization.eulerLagrange x =
        SignedCount.ofNat (data.selectedQuadraticDensity x)) ∧
    (∀ x : State,
      data.scalarPDERealization.equation x =
        data.scalarActionRealization.eulerLagrange x)

/-- The current scalar flagship realizations already come from one concrete
selected quadratic density on the selected state space. -/
theorem LocalEventFourStateLaw.selectedScalarDensitySurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedScalarDensitySurface data := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    rfl
  · intro x
    rfl
  · intro x
    rfl
  · intro x
    rfl

end ClosureCurrent

end CoherenceCalculus
