import CoherenceCalculus.PartIV.ClosureCurrentContinuumFlagshipRealizationCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumVariationalCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumVariationalRealizationCore

Variational contract for any later stronger flagship realization.

`ClosureCurrentContinuumFlagshipRealizationCore` fixes the public law data of
any later stronger flagship form. `ClosureCurrentContinuumVariationalCore`
already shows that the detached selected cut carries one exact scalarized
variational/observer/Hamilton-Jacobi triad.

This file adds the next honest boundary theorem on the action side. Any later
stronger flagship realization that claims that same Chapter 7-style
variational presentation is already forced to use the same Lagrangian,
Hamiltonian, characteristic, Eulerian, observer-characteristic, and projected
characteristic residuals, and therefore the same common zero set.

This still does not build a full action functional. It fixes the exact
variational contract that any such later action-like realization must satisfy.
-/

namespace ClosureCurrent

private theorem selectedAutonomousResidual_eq_scalarResidual
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ∀ x : State,
      data.selectedAutonomousScalarLaw.residual x = scalarResidual data x := by
  obtain
    ⟨_hadm, _hscalarOp, hscalarGenerator, _hdynamics, _hobserver, _hprojection,
      _hobserverCharacteristic, _hdynEq, _hobsEq, _hstateForm⟩ :=
      data.variationalRepresentativeSurface
  intro x
  calc
    data.selectedAutonomousScalarLaw.residual x =
        SignedCount.ofNat (data.selectedAutonomousScalarLaw.density x) := by
          exact data.selectedAutonomousScalarLaw.residual_eq x
    _ = SignedCount.ofNat
          (State.pair x (data.selectedAutonomousScalarLaw.generator x)) := by
            rw [data.selectedAutonomousScalarLaw.density_eq x]
    _ = SignedCount.ofNat
          (State.pair x (data.framed.object.bridge.generator.toFun x)) := by
            rfl
    _ = scalarResidual data x := by
          symm
          exact hscalarGenerator x

/-- Minimal Chapter 7-style variational realization of a later stronger
flagship language. It extends the public flagship realization by one dynamics
triad, one observer-side transport triad, and one Hamilton-Jacobi projection
bridge, all read from the same realized flagship residual. -/
structure VariationalFlagshipRealization
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) where
  flagship : FlagshipRealization data
  dynamics : RegularVariationalSystem State State
  observer : ConservativeTransportDatum State State
  projection : HamiltonJacobiProjectionDatum State State
  exact_lagrangian :
    ∀ q : State, dynamics.lagrangianResidual q = flagship.residual q
  exact_hamiltonian :
    ∀ p : State, dynamics.hamiltonianResidual p = flagship.residual p
  exact_characteristic :
    ∀ q : State, dynamics.characteristicResidual q = flagship.residual q
  exact_eulerian :
    ∀ x : State, observer.eulerianResidual x = flagship.residual x
  exact_observerLagrangian :
    ∀ a : State, observer.lagrangianResidual a = flagship.residual a
  exact_observerCharacteristic :
    ∀ a : State, observer.characteristicResidual a = flagship.residual a
  projection_uses_dynamics : projection.dynamics = dynamics
  projection_uses_observer : projection.observer = observer

/-- The canonical variational realization already carried by the detached
selected cut. -/
def LocalEventFourStateLaw.selectedVariationalFlagshipRealization
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    VariationalFlagshipRealization data where
  flagship := data.selectedFlagshipRealization
  dynamics := regularSystem data
  observer := observerTransport data
  projection := projectionDatum data
  exact_lagrangian := by
    intro q
    calc
      (regularSystem data).lagrangianResidual q = scalarResidual data q := by
        rfl
      _ = data.selectedAutonomousScalarLaw.residual q := by
            exact (selectedAutonomousResidual_eq_scalarResidual data q).symm
      _ = data.selectedFlagshipRealization.residual q := by
            rfl
  exact_hamiltonian := by
    intro p
    calc
      (regularSystem data).hamiltonianResidual p = scalarResidual data p := by
        rfl
      _ = data.selectedAutonomousScalarLaw.residual p := by
            exact (selectedAutonomousResidual_eq_scalarResidual data p).symm
      _ = data.selectedFlagshipRealization.residual p := by
            rfl
  exact_characteristic := by
    intro q
    calc
      (regularSystem data).characteristicResidual q = scalarResidual data q := by
        rfl
      _ = data.selectedAutonomousScalarLaw.residual q := by
            exact (selectedAutonomousResidual_eq_scalarResidual data q).symm
      _ = data.selectedFlagshipRealization.residual q := by
            rfl
  exact_eulerian := by
    intro x
    calc
      (observerTransport data).eulerianResidual x = scalarResidual data x := by
        rfl
      _ = data.selectedAutonomousScalarLaw.residual x := by
            exact (selectedAutonomousResidual_eq_scalarResidual data x).symm
      _ = data.selectedFlagshipRealization.residual x := by
            rfl
  exact_observerLagrangian := by
    intro a
    calc
      (observerTransport data).lagrangianResidual a = scalarResidual data a := by
        rfl
      _ = data.selectedAutonomousScalarLaw.residual a := by
            exact (selectedAutonomousResidual_eq_scalarResidual data a).symm
      _ = data.selectedFlagshipRealization.residual a := by
            rfl
  exact_observerCharacteristic := by
    intro a
    calc
      (observerTransport data).characteristicResidual a = scalarResidual data a := by
        rfl
      _ = data.selectedAutonomousScalarLaw.residual a := by
            exact (selectedAutonomousResidual_eq_scalarResidual data a).symm
      _ = data.selectedFlagshipRealization.residual a := by
            rfl
  projection_uses_dynamics := rfl
  projection_uses_observer := rfl

/-- Variational flagship realizations already use the same solution set as the
autonomous scalar law. -/
theorem VariationalFlagshipRealization.solution_iff_selectedAutonomousScalarLaw
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : VariationalFlagshipRealization data) :
    ∀ x : State,
      realization.flagship.solution x ↔ data.selectedAutonomousScalarLaw.solution x :=
  realization.flagship.solution_iff_selectedAutonomousScalarLaw

/-- Variational flagship realizations already use the same Lagrangian residual
as the selected variational system. -/
theorem VariationalFlagshipRealization.lagrangian_iff_selectedResidual
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : VariationalFlagshipRealization data) :
    ∀ q : State,
      realization.dynamics.lagrangianResidual q =
        (regularSystem data).lagrangianResidual q := by
  intro q
  calc
    realization.dynamics.lagrangianResidual q = realization.flagship.residual q := by
      exact realization.exact_lagrangian q
    _ = data.selectedAutonomousScalarLaw.residual q := by
      exact realization.flagship.residual_iff_selectedResidual q
    _ = scalarResidual data q := by
      exact selectedAutonomousResidual_eq_scalarResidual data q
    _ = (regularSystem data).lagrangianResidual q := by
      rfl

/-- Variational flagship realizations already use the same Hamiltonian
residual as the selected variational system. -/
theorem VariationalFlagshipRealization.hamiltonian_iff_selectedResidual
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : VariationalFlagshipRealization data) :
    ∀ p : State,
      realization.dynamics.hamiltonianResidual p =
        (regularSystem data).hamiltonianResidual p := by
  intro p
  calc
    realization.dynamics.hamiltonianResidual p = realization.flagship.residual p := by
      exact realization.exact_hamiltonian p
    _ = data.selectedAutonomousScalarLaw.residual p := by
      exact realization.flagship.residual_iff_selectedResidual p
    _ = scalarResidual data p := by
      exact selectedAutonomousResidual_eq_scalarResidual data p
    _ = (regularSystem data).hamiltonianResidual p := by
      rfl

/-- Variational flagship realizations already use the same characteristic
residual as the selected variational system. -/
theorem VariationalFlagshipRealization.characteristic_iff_selectedResidual
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : VariationalFlagshipRealization data) :
    ∀ q : State,
      realization.dynamics.characteristicResidual q =
        (regularSystem data).characteristicResidual q := by
  intro q
  calc
    realization.dynamics.characteristicResidual q = realization.flagship.residual q := by
      exact realization.exact_characteristic q
    _ = data.selectedAutonomousScalarLaw.residual q := by
      exact realization.flagship.residual_iff_selectedResidual q
    _ = scalarResidual data q := by
      exact selectedAutonomousResidual_eq_scalarResidual data q
    _ = (regularSystem data).characteristicResidual q := by
      rfl

/-- Variational flagship realizations already use the same Eulerian residual
as the selected observer-side transport datum. -/
theorem VariationalFlagshipRealization.eulerian_iff_selectedResidual
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : VariationalFlagshipRealization data) :
    ∀ x : State,
      realization.observer.eulerianResidual x =
        (observerTransport data).eulerianResidual x := by
  intro x
  calc
    realization.observer.eulerianResidual x = realization.flagship.residual x := by
      exact realization.exact_eulerian x
    _ = data.selectedAutonomousScalarLaw.residual x := by
      exact realization.flagship.residual_iff_selectedResidual x
    _ = scalarResidual data x := by
      exact selectedAutonomousResidual_eq_scalarResidual data x
    _ = (observerTransport data).eulerianResidual x := by
      rfl

/-- Variational flagship realizations already use the same observer-side
Lagrangian residual as the selected observer transport datum. -/
theorem VariationalFlagshipRealization.observerLagrangian_iff_selectedResidual
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : VariationalFlagshipRealization data) :
    ∀ a : State,
      realization.observer.lagrangianResidual a =
        (observerTransport data).lagrangianResidual a := by
  intro a
  calc
    realization.observer.lagrangianResidual a = realization.flagship.residual a := by
      exact realization.exact_observerLagrangian a
    _ = data.selectedAutonomousScalarLaw.residual a := by
      exact realization.flagship.residual_iff_selectedResidual a
    _ = scalarResidual data a := by
      exact selectedAutonomousResidual_eq_scalarResidual data a
    _ = (observerTransport data).lagrangianResidual a := by
      rfl

/-- Variational flagship realizations already use the same observer-side
characteristic residual as the selected observer transport datum. -/
theorem VariationalFlagshipRealization.observerCharacteristic_iff_selectedResidual
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : VariationalFlagshipRealization data) :
    ∀ a : State,
      realization.observer.characteristicResidual a =
        (observerTransport data).characteristicResidual a := by
  intro a
  calc
    realization.observer.characteristicResidual a = realization.flagship.residual a := by
      exact realization.exact_observerCharacteristic a
    _ = data.selectedAutonomousScalarLaw.residual a := by
      exact realization.flagship.residual_iff_selectedResidual a
    _ = scalarResidual data a := by
      exact selectedAutonomousResidual_eq_scalarResidual data a
    _ = (observerTransport data).characteristicResidual a := by
      rfl

/-- Variational flagship realizations already use the same observer-side
Hamilton-Jacobi characteristic residual as the selected projection bridge. -/
theorem VariationalFlagshipRealization.projectionCharacteristic_iff_selectedResidual
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : VariationalFlagshipRealization data) :
    ∀ q : State,
      realization.projection.observer.characteristicResidual q =
        (projectionDatum data).observer.characteristicResidual q := by
  intro q
  calc
    realization.projection.observer.characteristicResidual q =
        realization.observer.characteristicResidual q := by
          rw [realization.projection_uses_observer]
    _ = (observerTransport data).characteristicResidual q := by
          exact realization.observerCharacteristic_iff_selectedResidual q
    _ = (projectionDatum data).observer.characteristicResidual q := by
          rfl

/-- Manuscript-facing variational contract surface for any later stronger
flagship realization. -/
def SelectedVariationalFlagshipRealizationSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  Nonempty (VariationalFlagshipRealization data) ∧
    (∀ realization : VariationalFlagshipRealization data,
      ∀ q : State,
        realization.dynamics.lagrangianResidual q =
          (regularSystem data).lagrangianResidual q) ∧
    (∀ realization : VariationalFlagshipRealization data,
      ∀ p : State,
        realization.dynamics.hamiltonianResidual p =
          (regularSystem data).hamiltonianResidual p) ∧
    (∀ realization : VariationalFlagshipRealization data,
      ∀ q : State,
        realization.dynamics.characteristicResidual q =
          (regularSystem data).characteristicResidual q) ∧
    (∀ realization : VariationalFlagshipRealization data,
      ∀ x : State,
        realization.observer.eulerianResidual x =
          (observerTransport data).eulerianResidual x) ∧
    (∀ realization : VariationalFlagshipRealization data,
      ∀ a : State,
        realization.observer.lagrangianResidual a =
          (observerTransport data).lagrangianResidual a) ∧
    (∀ realization : VariationalFlagshipRealization data,
      ∀ a : State,
        realization.observer.characteristicResidual a =
          (observerTransport data).characteristicResidual a) ∧
    (∀ realization : VariationalFlagshipRealization data,
      ∀ q : State,
        realization.projection.observer.characteristicResidual q =
          (projectionDatum data).observer.characteristicResidual q) ∧
    (∀ realization : VariationalFlagshipRealization data,
      ∀ x : State,
        realization.flagship.solution x ↔ data.selectedAutonomousScalarLaw.solution x) ∧
    (∀ realization : VariationalFlagshipRealization data,
      ∀ x : State,
        realization.flagship.solution x ↔ data.scalarPDERealization.solution x) ∧
    (∀ realization : VariationalFlagshipRealization data,
      ∀ x : State,
        realization.flagship.solution x ↔ data.scalarActionRealization.stationary x) ∧
    (∀ realization : VariationalFlagshipRealization data,
      ∀ x : State,
        realization.flagship.solution x ↔ data.selectedEvolutionLaw.solution x)

/-- Any later stronger flagship realization that claims a Chapter 7-style
variational / observer / Hamilton-Jacobi presentation is already forced to
agree with the selected cut on those residual fields and on the common zero
set. -/
theorem LocalEventFourStateLaw.selectedVariationalFlagshipRealizationSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedVariationalFlagshipRealizationSurface data := by
  refine
    ⟨⟨data.selectedVariationalFlagshipRealization⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
  · intro realization q
    exact realization.lagrangian_iff_selectedResidual q
  · intro realization p
    exact realization.hamiltonian_iff_selectedResidual p
  · intro realization q
    exact realization.characteristic_iff_selectedResidual q
  · intro realization x
    exact realization.eulerian_iff_selectedResidual x
  · intro realization a
    exact realization.observerLagrangian_iff_selectedResidual a
  · intro realization a
    exact realization.observerCharacteristic_iff_selectedResidual a
  · intro realization q
    exact realization.projectionCharacteristic_iff_selectedResidual q
  · intro realization x
    exact realization.solution_iff_selectedAutonomousScalarLaw x
  · intro realization x
    exact realization.flagship.solution_iff_pdeSolution x
  · intro realization x
    exact realization.flagship.solution_iff_actionStationary x
  · intro realization x
    exact realization.flagship.solution_iff_evolutionSolution x

end ClosureCurrent

end CoherenceCalculus
