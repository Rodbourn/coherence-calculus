import CoherenceCalculus.PartIV.ClosureCurrentContinuumEvolutionCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumRealizationCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumEvolutionRealizationCore

Evolution-form realizations of the canonical autonomous selected law.

`ClosureCurrentContinuumEvolutionCore` upgrades the detached selected cut to a
uniquely forced autonomous evolution law. `ClosureCurrentContinuumRealizationCore`
shows that any later PDE-form or action-form flagship language must present the
same selected equation.

This file inserts the honest intermediate realization boundary. Before any
spatial differential PDE appears, the detached selected cut already has a
canonical evolution-form realization language:

* one velocity field, namely the forced selected generator;
* one scalar residual field, namely the governing selected residual;
* one solution set, namely the selected equation.

So any later stronger differential flagship form must in particular realize
this same autonomous evolution law, not merely its zero set.
-/

namespace ClosureCurrent

/-- An evolution-form realization of the detached selected law. The interface is
minimal: one velocity field, one scalar residual field, and the exact solution
set identification with the forced selected equation. -/
structure EvolutionRealization
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) where
  velocity : State → State
  residual : State → SignedCount
  exact_velocity : ∀ x : State, velocity x = data.selectedEvolutionLaw.generator x
  exact_zero_set : ∀ x : State, residual x = SignedCount.zero ↔ data.selectedFieldEquation x

/-- The solution set of an evolution-form realization. -/
def EvolutionRealization.solution
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : EvolutionRealization data) :
    State → Prop :=
  fun x => realization.residual x = SignedCount.zero

/-- Any evolution-form realization has exactly the same solution set as the
forced selected equation. -/
theorem EvolutionRealization.solution_iff_selectedEquation
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : EvolutionRealization data) :
    ∀ x : State, realization.solution x ↔ data.selectedFieldEquation x :=
  realization.exact_zero_set

/-- Any evolution-form realization uses exactly the same velocity field as the
forced autonomous selected evolution law. -/
theorem EvolutionRealization.velocity_iff_selectedGenerator
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : EvolutionRealization data) :
    ∀ x : State, realization.velocity x = data.selectedEvolutionLaw.generator x :=
  realization.exact_velocity

/-- Any evolution-form realization has the same solution set as the canonical
autonomous evolution law. -/
theorem EvolutionRealization.solution_iff_selectedEvolution
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : EvolutionRealization data) :
    ∀ x : State, realization.solution x ↔ data.selectedEvolutionLaw.solution x := by
  obtain
    ⟨_hforced, _hflow, _hgen, _hres, _hscalar, hsolution, _hpde, _haction⟩ :=
    data.selectedEvolutionLawSurface
  intro x
  constructor
  · intro hx
    exact (hsolution x).2
      ((realization.solution_iff_selectedEquation x).1 hx)
  · intro hx
    exact (realization.solution_iff_selectedEquation x).2
      ((hsolution x).1 hx)

/-- Any evolution-form realization has the same solution set as any PDE-form
realization of the detached selected law. -/
theorem EvolutionRealization.solution_iff_pdeSolution
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : EvolutionRealization data)
    (pde : PDERealization data) :
    ∀ x : State, realization.solution x ↔ pde.solution x := by
  intro x
  constructor
  · intro hx
    exact (pde.solution_iff_selectedEquation x).2
      ((realization.solution_iff_selectedEquation x).1 hx)
  · intro hx
    exact (realization.solution_iff_selectedEquation x).2
      ((pde.solution_iff_selectedEquation x).1 hx)

/-- Any evolution-form realization has the same solution set as any action-form
realization of the detached selected law. -/
theorem EvolutionRealization.solution_iff_actionStationary
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : EvolutionRealization data)
    (action : ActionRealization data) :
    ∀ x : State, realization.solution x ↔ action.stationary x := by
  intro x
  constructor
  · intro hx
    exact (action.stationary_iff_selectedEquation x).2
      ((realization.solution_iff_selectedEquation x).1 hx)
  · intro hx
    exact (realization.solution_iff_selectedEquation x).2
      ((action.stationary_iff_selectedEquation x).1 hx)

/-- The canonical evolution-form realization of the detached selected law. -/
def LocalEventFourStateLaw.selectedEvolutionRealization
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    EvolutionRealization data where
  velocity := data.selectedEvolutionLaw.generator
  residual := data.selectedEvolutionLaw.residual
  exact_velocity := by
    intro x
    rfl
  exact_zero_set := by
    obtain
      ⟨_hforced, _hflow, _hgen, _hres, _hscalar, hsolution, _hpde, _haction⟩ :=
      data.selectedEvolutionLawSurface
    intro x
    exact hsolution x

/-- Manuscript-facing evolution-realization surface of the detached selected
law. The autonomous selected law already admits a canonical evolution-form
realization, and every such realization shares the same velocity field and the
same solution set as the current scalar PDE/action realizations. -/
def SelectedEvolutionRealizationSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  Nonempty (EvolutionRealization data) ∧
    (∀ realization : EvolutionRealization data,
      ∀ x : State, realization.velocity x = data.selectedEvolutionLaw.generator x) ∧
    (∀ realization : EvolutionRealization data,
      ∀ x : State, realization.solution x ↔ data.selectedFieldEquation x) ∧
    (∀ realization : EvolutionRealization data,
      ∀ x : State, realization.solution x ↔ data.selectedEvolutionLaw.solution x) ∧
    (∀ realization : EvolutionRealization data,
      ∀ x : State, realization.solution x ↔ data.scalarPDERealization.solution x) ∧
    (∀ realization : EvolutionRealization data,
      ∀ x : State, realization.solution x ↔ data.scalarActionRealization.stationary x) ∧
    (∀ x : State,
      data.selectedEvolutionRealization.velocity x = data.selectedEvolutionLaw.generator x) ∧
    (∀ x : State,
      data.selectedEvolutionRealization.solution x ↔ data.selectedFieldEquation x)

/-- The detached selected cut already admits a canonical evolution-form
realization of its uniquely forced autonomous evolution law. -/
theorem LocalEventFourStateLaw.selectedEvolutionRealizationSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedEvolutionRealizationSurface data := by
  refine ⟨⟨data.selectedEvolutionRealization⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro realization x
    exact realization.velocity_iff_selectedGenerator x
  · intro realization x
    exact realization.solution_iff_selectedEquation x
  · intro realization x
    exact realization.solution_iff_selectedEvolution x
  · intro realization x
    exact realization.solution_iff_pdeSolution data.scalarPDERealization x
  · intro realization x
    exact realization.solution_iff_actionStationary data.scalarActionRealization x
  · intro x
    rfl
  · intro x
    exact data.selectedEvolutionRealization.solution_iff_selectedEquation x

end ClosureCurrent

end CoherenceCalculus
