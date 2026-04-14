import CoherenceCalculus.PartIV.ClosureCurrentContinuumEffectiveCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumVariationalCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumEffectiveVariationalCore

Scalarized variational readout of the exact effective law on the stationary cut.

`ClosureCurrentContinuumEffectiveCore` proves that on the least-motion
stationary cut the selected quadratic representative is already its own exact
effective observable law. `ClosureCurrentContinuumVariationalCore` proves that
the same representative already carries the current scalarized
variational/transport triad.

This file closes the gap between those two surfaces. The point is not to add a
new action principle. The point is to show that the already-forced scalarized
variational residual is literally the residual of that exact effective law on
the same stationary cut, and therefore the same regular/observer/Hamilton--
Jacobi triad is already carried by the effective selected law itself.
-/

namespace ClosureCurrent

/-- Signed-count scalar residual read directly from the exact effective law on
the least-motion stationary cut. -/
def effectiveScalarResidual
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    State → SignedCount :=
  let rep := data.toMinimalQuadraticRepresentative
  let bridge := data.framed.object.bridge.selectedBridge
  let P := bridge.observer.selection.selectedProjection
  let Rqq := canonicalSelectedShadowPropagator bridge
  fun x =>
    SignedCount.ofNat
      (State.pair x (effectiveOp P rep.stateForm.op Rqq x))

/-- The scalarized variational residual is already the residual of the exact
effective law on the least-motion stationary cut. Hence the same regular
variational/transport/Hamilton--Jacobi triad already belongs to that exact
effective law, not to a separate postulated variational layer. -/
  theorem LocalEventFourStateLaw.effectiveVariationalRepresentativeSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    (∀ x : State,
      effectiveScalarResidual data x = scalarResidual data x) ∧
      (∀ x : State,
        effectiveScalarResidual data x =
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
          (projectionDatum data).dynamics.characteristicResidual q) := by
  obtain ⟨_heffVisible, heff, _hschur, _hreturn⟩ :=
    data.effectiveQuadraticRepresentativeSurface
  obtain ⟨_hadm, _hscalarQuad, hscalarGen, hdyn, hobs, hproj, hprojEq, _hd, _ho, _hstateForm⟩ :=
    data.variationalRepresentativeSurface
  have hstateForm :
      data.toQuadraticRepresentative.stateForm =
        data.toMinimalQuadraticRepresentative.stateForm := by
    calc
      data.toQuadraticRepresentative.stateForm =
          selected_observed_law data.framed.object.bridge.selectedBridge.observer.selection := by
            exact data.toQuadraticRepresentative.stateForm_isSelectedLaw
      _ = data.toMinimalQuadraticRepresentative.stateForm := by
            exact data.toMinimalQuadraticRepresentative.stateForm_isSelectedLaw.symm
  refine ⟨?_, ?_, hdyn, hobs, hproj, hprojEq⟩
  · intro x
    unfold effectiveScalarResidual scalarResidual
    have hsame :
        data.toQuadraticRepresentative.stateForm.op x =
          data.toMinimalQuadraticRepresentative.stateForm.op x := by
      rw [hstateForm]
    rw [hsame, heff x]
  · intro x
    calc
      effectiveScalarResidual data x = scalarResidual data x := by
        have hsame : effectiveScalarResidual data x = scalarResidual data x := by
          unfold effectiveScalarResidual scalarResidual
          have hstate :
              data.toQuadraticRepresentative.stateForm.op x =
                data.toMinimalQuadraticRepresentative.stateForm.op x := by
            rw [hstateForm]
          rw [hstate, heff x]
        exact hsame
      _ = SignedCount.ofNat
            (State.pair x (data.framed.object.bridge.generator.toFun x)) := by
          exact hscalarGen x

end ClosureCurrent

end CoherenceCalculus
