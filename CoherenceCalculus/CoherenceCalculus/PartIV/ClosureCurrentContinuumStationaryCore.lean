import CoherenceCalculus.PartIV.ClosureCurrentContinuumMinimalCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumStationaryCore

Stationary selected-cut surface of the detached quadratic representative.

After the minimal quadratic representative is identified, the next honest
question is whether the same selected datum already carries the least-motion
and stationarity facts needed to read that quadratic law on its actual cut.

The answer is yes. The selected projection is already:

* the finite least-motion minimizer,
* the realized horizon cut,
* stationary for the selected objective gradient,
* and therefore free of off-diagonal gradient blocks.

At the same time, exact visibility of the selected quadratic law on that cut
forces it to commute with the cut and annihilates its own off-diagonal blocks.

This file records that common stationary selected-cut surface without adding
any new analytic datum.
-/

namespace ClosureCurrent

/-- Manuscript-facing stationary selected-cut surface of the canonical
quadratic representative. The same selected projection is simultaneously the
least-motion minimizer, the realized horizon cut, the stationary projector for
the selected gradient, and the exact-visible cut for the selected quadratic
law. -/
def StationaryQuadraticRepresentativeSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  let rep := data.toMinimalQuadraticRepresentative
  let selection := data.framed.object.bridge.selectedBridge.observer.selection
  let P := selection.selectedProjection
  Compiler.Admissible rep.stateForm ∧
    Compiler.QuadForm.IsPSD rep.stateForm ∧
    rep.stateForm = selected_observed_law selection ∧
    P = selectedCandidateProjection selection ∧
    P = selection.realization.tower.π selection.horizon ∧
    (∀ i : Fin (Nat.succ selection.candidates.size),
      observerMotionValue selection ≤
        selection.objective.eval (selection.candidates.elem i)) ∧
    isStationaryFor selection.gradient P ∧
    (∀ x : State,
      projectionCommutator (selection.gradient.gradient P) P x = State.zero) ∧
    hasZeroPQ P (selection.gradient.gradient P) ∧
    hasZeroQP P (selection.gradient.gradient P) ∧
    exactVisibleOnCut P rep.stateForm.op ∧
    commutesWithProjection P rep.stateForm.op ∧
    hasZeroPQ P rep.stateForm.op ∧
    hasZeroQP P rep.stateForm.op

/-- The selected quadratic representative already sits on the exact
least-motion stationary cut: the selected projection is the minimizer and the
realized horizon cut, the selected gradient is stationary there, and the
selected quadratic law is exact-visible and commutes with that same cut. -/
theorem LocalEventFourStateLaw.stationaryQuadraticRepresentativeSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    StationaryQuadraticRepresentativeSurface data := by
  let rep := data.toMinimalQuadraticRepresentative
  let selection := data.framed.object.bridge.selectedBridge.observer.selection
  let P := selection.selectedProjection
  obtain
    ⟨hadm, hpsd, _heq, _hmin, _hmineq, hstateForm, _hgen⟩ :=
      data.minimalQuadraticRepresentativeSurface
  have hcandidate :
      P = selectedCandidateProjection selection :=
    data.framed.object.bridge.selectedBridge.selectedProjection_eq_candidate
  have hcut :
      P = selection.realization.tower.π selection.horizon :=
    data.framed.object.bridge.selectedBridge.selectedProjection_eq_horizonCut
  have hmotion :
      ∀ i : Fin (Nat.succ selection.candidates.size),
        observerMotionValue selection ≤
          selection.objective.eval (selection.candidates.elem i) := by
    intro i
    exact observerMotionValue_minimal selection i
  have hstationary :
      isStationaryFor selection.gradient P := selection.stationary
  have hgradComm :
      ∀ x : State,
        projectionCommutator (selection.gradient.gradient P) P x = State.zero :=
    (stationarity_condition selection.gradient P).mp hstationary
  have hgradOff :
      hasZeroPQ P (selection.gradient.gradient P) ∧
        hasZeroQP P (selection.gradient.gradient P) :=
    stationary_implies_offdiag_zero selection.gradient P hstationary
  have hvis0 :
      exactVisibleOnCut
        (selection.realization.tower.π selection.horizon)
        (selected_observed_law selection).op :=
    data.framed.object.bridge.selectedBridge.exactVisibleSelectedLaw
  have hvis :
      exactVisibleOnCut P rep.stateForm.op := by
    rw [hcut]
    simpa [hstateForm] using hvis0
  have hcomm :
      commutesWithProjection P rep.stateForm.op :=
    exact_visible_implies_commutes P rep.stateForm.op hvis
  have hzeroPQ :
      hasZeroPQ P rep.stateForm.op :=
    commutes_implies_zeroPQ P rep.stateForm.op hcomm
  have hzeroQP :
      hasZeroQP P rep.stateForm.op :=
    commutes_implies_zeroQP P rep.stateForm.op hcomm
  exact
    ⟨hadm,
      hpsd,
      hstateForm,
      hcandidate,
      hcut,
      hmotion,
      hstationary,
      hgradComm,
      hgradOff.1,
      hgradOff.2,
      hvis,
      hcomm,
      hzeroPQ,
      hzeroQP⟩

end ClosureCurrent

end CoherenceCalculus
