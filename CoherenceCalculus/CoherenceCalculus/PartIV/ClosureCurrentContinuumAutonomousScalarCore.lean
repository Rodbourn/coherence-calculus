import CoherenceCalculus.PartIV.ClosureCurrentContinuumEvolutionRealizationCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumScalarCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumAutonomousScalarCore

One autonomous scalar law on the detached selected cut.

`ClosureCurrentContinuumEvolutionRealizationCore` already upgrades the detached
selected cut to a uniquely forced autonomous evolution law together with its
canonical evolution-form realization language. `ClosureCurrentContinuumScalarCore`
already packages the same selected cut as one canonical scalar law object with
an explicit quadratic density, an exact realization ledger, and an exact
adjoint-goal ledger.

This file collapses those two surfaces to one public law object. The point is
not to add a new law. The point is to show that the current flagship surface
already carries one uniquely forced autonomous scalar law whose:

* flow is the selected evolution flow,
* generator is the selected operator,
* density is the selected quadratic density,
* residual is the selected scalar residual,
* zero set is the common selected equation.

So before any genuinely spatial differential PDE appears, the detached selected
cut already has one honest candidate for the theory's current flagship law
object.
-/

namespace ClosureCurrent

/-- Autonomous scalar law on the detached selected cut. It records one
stage-parameterized flow, one common generator, one scalar density, and one
scalar residual. The remaining fields certify that the flow is already
autonomous and that the residual is exactly the scalarization of the density. -/
structure AutonomousScalarLaw where
  flow : Nat → State → State
  generator : State → State
  density : State → Nat
  residual : State → SignedCount
  stage_constant : ∀ n : Nat, ∀ x : State, flow n x = generator x
  density_eq : ∀ x : State, density x = State.pair x (generator x)
  residual_eq : ∀ x : State, residual x = SignedCount.ofNat (density x)

/-- Two autonomous scalar laws are equal once their public fields agree. -/
theorem AutonomousScalarLaw.ext
    {law law' : AutonomousScalarLaw}
    (hflow : law.flow = law'.flow)
    (hgenerator : law.generator = law'.generator)
    (hdensity : law.density = law'.density)
    (hresidual : law.residual = law'.residual) :
    law = law' := by
  cases law
  cases law'
  cases hflow
  cases hgenerator
  cases hdensity
  cases hresidual
  simp

/-- Zero set of an autonomous scalar law. -/
def AutonomousScalarLaw.solution
    (law : AutonomousScalarLaw) :
    State → Prop :=
  fun x => law.residual x = SignedCount.zero

/-- The canonical autonomous scalar law already carried by the detached
selected cut. -/
def LocalEventFourStateLaw.selectedAutonomousScalarLaw
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    AutonomousScalarLaw where
  flow := data.selectedEvolutionLaw.flow
  generator := data.selectedEvolutionLaw.generator
  density := data.selectedQuadraticDensity
  residual := data.selectedEvolutionLaw.residual
  stage_constant := data.selectedEvolutionLaw.stage_constant
  density_eq := by
    intro x
    rfl
  residual_eq := by
    have hdensity :
        SelectedScalarDensitySurface data := data.selectedScalarDensitySurface
    intro x
    exact hdensity.2.1 x

/-- Admissible autonomous scalar laws for the detached selected cut. Since
autonomy, density, and scalarization are built into the law object itself, the
only remaining forcing clause is that the generator lies in the same forced
continuum class. -/
def LocalEventFourStateLaw.selectedAutonomousScalarLawClass
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ContinuumLimitClass AutonomousScalarLaw where
  admissible := fun law =>
    data.stateDynamics.limitClass.admissible law.generator

/-- The canonical autonomous scalar law is admissible for its forcing class. -/
theorem LocalEventFourStateLaw.selectedAutonomousScalarLaw_admissible
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    data.selectedAutonomousScalarLawClass.admissible
      data.selectedAutonomousScalarLaw := by
  obtain
    ⟨hstate, _hscalar, _heffectiveScalar, _hreg, _hobs, _hproj, _hprojEq,
      _hpromo⟩ := data.selectedFieldLawSurface
  have hstateEq :
      data.stateDynamics.continuumLaw = data.selectedAutonomousScalarLaw.generator := by
    funext x
    exact hstate x
  simpa [hstateEq] using data.stateDynamics.continuumLaw_admissible

/-- Any admissible autonomous scalar law is already forced to equal the
canonical autonomous scalar law carried by the detached selected cut. -/
theorem LocalEventFourStateLaw.selectedAutonomousScalarLaw_pointwise_forcing
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law)
    {law : AutonomousScalarLaw}
    (hlaw : data.selectedAutonomousScalarLawClass.admissible law) :
    law = data.selectedAutonomousScalarLaw := by
  have hgenerator :
      law.generator = data.selectedAutonomousScalarLaw.generator := by
    funext x
    exact data.stateDynamics.limitClass_pointwise_forcing hlaw x
  have hflow :
      law.flow = data.selectedAutonomousScalarLaw.flow := by
    funext n
    funext x
    calc
      law.flow n x = law.generator x := by
        exact law.stage_constant n x
      _ = data.selectedAutonomousScalarLaw.generator x := by
        rw [hgenerator]
      _ = data.selectedAutonomousScalarLaw.flow n x := by
        symm
        exact data.selectedAutonomousScalarLaw.stage_constant n x
  have hdensity :
      law.density = data.selectedAutonomousScalarLaw.density := by
    funext x
    calc
      law.density x = State.pair x (law.generator x) := by
        exact law.density_eq x
      _ = State.pair x (data.selectedAutonomousScalarLaw.generator x) := by
        rw [hgenerator]
      _ = data.selectedAutonomousScalarLaw.density x := by
        symm
        exact data.selectedAutonomousScalarLaw.density_eq x
  have hresidual :
      law.residual = data.selectedAutonomousScalarLaw.residual := by
    funext x
    calc
      law.residual x = SignedCount.ofNat (law.density x) := by
        exact law.residual_eq x
      _ = SignedCount.ofNat (data.selectedAutonomousScalarLaw.density x) := by
        rw [hdensity]
      _ = data.selectedAutonomousScalarLaw.residual x := by
        symm
        exact data.selectedAutonomousScalarLaw.residual_eq x
  exact AutonomousScalarLaw.ext hflow hgenerator hdensity hresidual

/-- Manuscript-facing forcing surface of the autonomous scalar law. -/
def SelectedAutonomousScalarLawForcingSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  ForcedContinuumLaw
    data.selectedAutonomousScalarLawClass
    data.selectedAutonomousScalarLaw

/-- The autonomous scalar law is uniquely forced on the detached selected cut. -/
theorem LocalEventFourStateLaw.selectedAutonomousScalarLawForcingSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedAutonomousScalarLawForcingSurface data := by
  exact
    discrete_to_continuum_forcing_principle
      data.selectedAutonomousScalarLawClass
      data.selectedAutonomousScalarLaw
      data.selectedAutonomousScalarLaw_admissible
      (fun law hlaw => data.selectedAutonomousScalarLaw_pointwise_forcing hlaw)

/-- Manuscript-facing autonomous scalar flagship surface of the detached
selected cut. The selected evolution law, the selected scalar law, the exact
realization ledger, and the exact adjoint-goal ledger already collapse to one
uniquely forced autonomous scalar law object. -/
def SelectedAutonomousScalarLawSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  SelectedAutonomousScalarLawForcingSurface data ∧
    (∀ n : Nat, ∀ x : State,
      data.selectedAutonomousScalarLaw.flow n x = data.selectedFieldLaw.operator x) ∧
    (∀ x : State,
      data.selectedAutonomousScalarLaw.generator x = data.selectedFieldLaw.operator x) ∧
    (∀ x : State,
      data.selectedAutonomousScalarLaw.density x = data.selectedQuadraticDensity x) ∧
    (∀ x : State,
      data.selectedAutonomousScalarLaw.density x =
        State.pair x (residualReal data.selectedRealizationChain () x)) ∧
    (∀ x : State,
      data.selectedAutonomousScalarLaw.density x =
        goalError (data.selectedGoalCertificate x)) ∧
    (∀ x : State,
      data.selectedAutonomousScalarLaw.residual x = data.selectedFieldLaw.residual x) ∧
    (∀ x : State,
      data.selectedAutonomousScalarLaw.residual x =
        SignedCount.ofNat (data.selectedAutonomousScalarLaw.density x)) ∧
    (∀ x : State,
      data.selectedAutonomousScalarLaw.solution x ↔ data.selectedFieldEquation x) ∧
    (∀ x : State,
      data.selectedAutonomousScalarLaw.solution x ↔
        data.scalarPDERealization.solution x) ∧
    (∀ x : State,
      data.selectedAutonomousScalarLaw.solution x ↔
        data.scalarActionRealization.stationary x) ∧
    (∀ x : State,
      data.selectedAutonomousScalarLaw.solution x ↔
        data.selectedEvolutionLaw.solution x)

/-- The detached selected cut already carries one uniquely forced autonomous
scalar law. Its flow is the exact selected evolution flow, its density is the
selected quadratic density, its residual is the selected scalar residual, and
its zero set is the common selected equation. -/
theorem LocalEventFourStateLaw.selectedAutonomousScalarLawSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedAutonomousScalarLawSurface data := by
  have hforced :
      SelectedAutonomousScalarLawForcingSurface data := by
    exact data.selectedAutonomousScalarLawForcingSurface
  have hevolution :
      SelectedEvolutionLawSurface data := by
    exact data.selectedEvolutionLawSurface
  have hscalar :
      SelectedScalarLawSurface data := by
    exact data.selectedScalarLawSurface
  obtain
    ⟨_hrealization, _hexistence, _hscalarReal, _hdensity, _hledger, _hgoal,
      hdensityReal, hgoalDensity, _hpointwise, _hzeros⟩ :=
    hscalar
  have hsolutionEvolution :
      ∀ x : State,
        data.selectedAutonomousScalarLaw.solution x ↔
          data.selectedEvolutionLaw.solution x := by
    intro x
    rfl
  obtain
    ⟨_hforcedEvolution, hflow, _hgenerator, _hresidual, _hscalarResidual,
      hsolutionEq, hpde, haction⟩ :=
    hevolution
  refine ⟨hforced, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n x
    exact hflow n x
  · intro x
    rfl
  · intro x
    rfl
  · intro x
    exact hdensityReal x
  · intro x
    exact (hgoalDensity x).symm
  · intro x
    rfl
  · intro x
    exact data.selectedAutonomousScalarLaw.residual_eq x
  · intro x
    exact (hsolutionEvolution x).trans (hsolutionEq x)
  · intro x
    exact (hsolutionEvolution x).trans (hpde x)
  · intro x
    exact (hsolutionEvolution x).trans (haction x)
  · exact hsolutionEvolution

end ClosureCurrent

end CoherenceCalculus
