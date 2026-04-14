import CoherenceCalculus.PartIV.ClosureCurrentContinuumStationaryCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumEffectiveCore

Exact effective-law recovery on the least-motion stationary cut.

Once the selected quadratic representative is known to be exact-visible on the
least-motion stationary cut, the active Schur/Feshbach calculus forces more:

* the selected quadratic law is already its own exact effective observable law
  on that cut for the canonical selected shadow propagator;
* the corresponding Schur correction vanishes identically;
* the associated returned residual field therefore vanishes identically there.

This is still not a PDE or action principle. It is the exact effective-law
surface already forced by the current selected-cut calculus.
-/

namespace ClosureCurrent

/-- Exact effective-law surface of the selected quadratic representative on
the least-motion stationary cut. -/
def EffectiveQuadraticRepresentativeSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  let rep := data.toMinimalQuadraticRepresentative
  let bridge := data.framed.object.bridge.selectedBridge
  let selection := bridge.observer.selection
  let P := selection.selectedProjection
  let Rqq := canonicalSelectedShadowPropagator bridge
  exactVisibleOnCut P rep.stateForm.op ∧
    (∀ x : State,
      rep.stateForm.op x = effectiveOp P rep.stateForm.op Rqq x) ∧
    (∀ x : State,
      schurComplement P rep.stateForm.op Rqq x = State.zero) ∧
    (∀ x : State,
      returnedResidual (residualReturnFieldOf P rep.stateForm.op Rqq) x =
        State.zero)

/-- The canonical selected quadratic representative is already the exact
effective observable law on the least-motion stationary cut for the canonical
selected shadow propagator. The induced Schur correction and returned residual
both vanish there. -/
theorem LocalEventFourStateLaw.effectiveQuadraticRepresentativeSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    EffectiveQuadraticRepresentativeSurface data := by
  let rep := data.toMinimalQuadraticRepresentative
  let bridge := data.framed.object.bridge.selectedBridge
  let selection := bridge.observer.selection
  let P := selection.selectedProjection
  let Rqq := canonicalSelectedShadowPropagator bridge
  obtain
    ⟨_hadm, _hpsd, _hstateForm, _hcandidate, _hcut, _hmotion, _hstationary,
      _hgradComm, _hgradPQ, _hgradQP, hvis, _hcomm, hzeroPQ, _hzeroQP⟩ :=
    data.stationaryQuadraticRepresentativeSurface
  have heff :
      ∀ x : State,
        rep.stateForm.op x = effectiveOp P rep.stateForm.op Rqq x :=
    exact_visible_implies_effective P rep.stateForm.op Rqq hvis
  have hperfect :
      hasPerfectCoherence P rep.stateForm.op :=
    zeroPQ_implies_perfect P rep.stateForm.op hzeroPQ
  have hschur :
      ∀ x : State,
        schurComplement P rep.stateForm.op Rqq x = State.zero := by
    intro x
    exact hperfect Rqq x
  have hreturn :
      ∀ x : State,
        returnedResidual (residualReturnFieldOf P rep.stateForm.op Rqq) x =
          State.zero := by
    intro x
    rw [returnedResidual_eq_schur]
    exact hschur x
  exact ⟨hvis, heff, hschur, hreturn⟩

end ClosureCurrent

end CoherenceCalculus
