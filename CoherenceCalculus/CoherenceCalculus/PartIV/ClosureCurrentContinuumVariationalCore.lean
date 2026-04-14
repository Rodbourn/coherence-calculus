import CoherenceCalculus.PartIV.ClosureCurrentContinuumQuadraticCore
import CoherenceCalculus.Foundation.VariationalSelectionCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumVariationalCore

Scalarized variational strengthening of the detached continuum representative.

`ClosureCurrentContinuumQuadraticCore` shows that the no-stage four-state law
already determines an admissible selected quadratic form whose operator is the
forced continuum generator.

The next honest question is whether the current formal surface already reaches
any genuinely variational presentation. The answer is yes, but only in the
explicit scalarized sense already supported by the foundation:

* the selected quadratic operator determines one signed-count residual
  scalarization on `State`;
* that same scalar residual supplies a regular variational triad;
* that same scalar residual also supplies the observer-side conservative
  transport triad and the Hamilton-Jacobi projection bridge.

This is still not a full analytic action principle. The point is only to
record the strongest variational/transport presentation already forced by the
detached lane itself.
-/

namespace ClosureCurrent

/-- Signed-count scalar residual induced by the selected quadratic operator.
This is the current variational scalarization of the detached four-state
continuum representative. -/
def scalarResidual
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    State → SignedCount :=
  fun x =>
    SignedCount.ofNat
      (State.pair x (data.toQuadraticRepresentative.stateForm.op x))

/-- The no-stage four-state law already induces a regular variational system on
the explicit four-state carrier: the Lagrangian, Hamiltonian, and
characteristic residuals are all the same scalar residual read from the forced
quadratic operator. -/
def regularSystem
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    RegularVariationalSystem State State where
  lagrangianResidual := scalarResidual data
  hamiltonianResidual := scalarResidual data
  characteristicResidual := scalarResidual data
  lagrangian_hamiltonian := by
    constructor
    · intro h p
      exact h p
    · intro h q
      exact h q
  hamiltonian_characteristic := by
    constructor
    · intro h q
      exact h q
    · intro h p
      exact h p

/-- The same scalar residual also supplies the observer-side conservative
transport datum. -/
def observerTransport
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ConservativeTransportDatum State State where
  eulerianResidual := scalarResidual data
  lagrangianResidual := scalarResidual data
  characteristicResidual := scalarResidual data
  eulerian_lagrangian := by
    constructor
    · intro h a
      exact h a
    · intro h x
      exact h x
  eulerian_characteristic := by
    constructor
    · intro h a
      exact h a
    · intro h x
      exact h x

/-- The observer-side characteristic residual is exactly the projected
dynamics-side characteristic residual because both are the same scalar
residual carried by the selected quadratic operator. -/
def projectionDatum
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    HamiltonJacobiProjectionDatum State State where
  dynamics := regularSystem data
  observer := observerTransport data
  observer_characteristic_eq := by
    intro q
    rfl

/-- The forced quadratic representative therefore already carries an exact
scalarized variational/transport triad. Nothing analytic is added here: the
same signed-count scalar residual drives the regular variational system, the
observer-side transport datum, and the Hamilton-Jacobi projection bridge. -/
theorem LocalEventFourStateLaw.variationalRepresentativeSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    Compiler.Admissible data.toQuadraticRepresentative.stateForm ∧
      (∀ x : State,
        scalarResidual data x =
          SignedCount.ofNat
            (State.pair x (data.toQuadraticRepresentative.stateForm.op x))) ∧
      (∀ x : State,
        scalarResidual data x =
          SignedCount.ofNat
            (State.pair x (data.framed.object.bridge.generator.toFun x))) ∧
      ((∀ q : State, (regularSystem data).lagrangianResidual q = SignedCount.zero) ↔
        (∀ p : State, (regularSystem data).hamiltonianResidual p = SignedCount.zero) ∧
          (∀ q : State, (regularSystem data).characteristicResidual q = SignedCount.zero)) ∧
      (EulerianPresentation (observerTransport data) ↔
        LagrangianPresentation (observerTransport data) ∧
          CharacteristicPresentation (observerTransport data)) ∧
      (CharacteristicPresentation (projectionDatum data).observer ↔
        ∀ q : State,
          (projectionDatum data).dynamics.characteristicResidual q = SignedCount.zero) ∧
      (∀ q : State,
        (projectionDatum data).observer.characteristicResidual q =
          (projectionDatum data).dynamics.characteristicResidual q) ∧
      (projectionDatum data).dynamics = regularSystem data ∧
      (projectionDatum data).observer = observerTransport data ∧
      data.toQuadraticRepresentative.stateForm =
        selected_observed_law
          data.framed.object.bridge.selectedBridge.observer.selection := by
  refine ⟨data.toQuadraticRepresentative.stateForm_admissible, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    unfold scalarResidual
    have hgen :
        data.toQuadraticRepresentative.stateForm.op x =
          data.framed.object.bridge.generator.toFun x := by
      simpa [LocalEventFourStateLaw.toQuadraticRepresentative] using
        data.toQuadraticRepresentative.stateOperator_isGenerator x
    rw [hgen]
  · exact dynamics_triad (regularSystem data)
  · exact observer_triad (observerTransport data)
  · exact hj_projection (projectionDatum data)
  · intro q
    rfl
  · rfl
  · rfl
  · exact data.toQuadraticRepresentative.stateForm_isSelectedLaw

end ClosureCurrent

end CoherenceCalculus
