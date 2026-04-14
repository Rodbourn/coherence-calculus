import CoherenceCalculus.PartIV.ClosureCurrentContinuumFieldForceCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumEquationCore

One common selected equation on the detached analytic lane.

`ClosureCurrentContinuumFieldForceCore` identifies a unique selected
operator-residual law on the least-motion cut. The next honest sharpening is
to expose the single equation surface already forced by that law.

At the current formal surface, this is not yet a PDE. It is the common
selected equation

`r_sel(x) = 0`

where `r_sel` is the governing scalar residual of the unique selected
operator-residual law. This file shows that all current analytic
presentations on the selected cut are already presentations of that same
equation:

* the four-state continuum operator law,
* the selected quadratic law,
* the exact effective selected law,
* the promoted observed law,
* the variational residuals,
* the observer-side transport residuals,
* the Hamilton--Jacobi characteristic residuals.
-/

namespace ClosureCurrent

/-- The common selected equation forced by the detached selected law: vanishing
of the governing scalar residual on the least-motion cut. -/
def LocalEventFourStateLaw.selectedFieldEquation
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    State → Prop :=
  fun x => data.selectedFieldLaw.residual x = SignedCount.zero

/-- Manuscript-facing equation surface of the detached selected law. -/
def SelectedFieldEquationSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  let law := data.selectedFieldLaw
  let rep := data.toMinimalQuadraticRepresentative
  let bridge := data.framed.object.bridge.selectedBridge
  let P := bridge.observer.selection.selectedProjection
  let Rqq := canonicalSelectedShadowPropagator bridge
  (∀ x : State,
      data.stateDynamics.continuumLaw x = law.operator x) ∧
    (∀ x : State,
      rep.stateForm.op x = law.operator x) ∧
    (∀ x : State,
      effectiveOp P rep.stateForm.op Rqq x = law.operator x) ∧
    (∀ x : State,
      promotedObservedLaw law.promotionContext x = law.operator x) ∧
    (∀ x : State,
      scalarResidual data x = law.residual x) ∧
    (∀ x : State,
      effectiveScalarResidual data x = law.residual x) ∧
    (∀ x : State,
      data.selectedFieldEquation x ↔
        scalarResidual data x = SignedCount.zero ∧
        effectiveScalarResidual data x = SignedCount.zero ∧
        law.regularSystem.lagrangianResidual x = SignedCount.zero ∧
        law.regularSystem.hamiltonianResidual x = SignedCount.zero ∧
        law.regularSystem.characteristicResidual x = SignedCount.zero ∧
        law.observerTransport.eulerianResidual x = SignedCount.zero ∧
        law.observerTransport.lagrangianResidual x = SignedCount.zero ∧
        law.observerTransport.characteristicResidual x = SignedCount.zero ∧
        law.projectionDatum.observer.characteristicResidual x = SignedCount.zero ∧
        law.projectionDatum.dynamics.characteristicResidual x = SignedCount.zero)

/-- All current selected-cut analytic presentations already collapse to one
common selected equation: the vanishing of the governing scalar residual of
the unique selected operator-residual law. -/
theorem LocalEventFourStateLaw.selectedFieldEquationSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedFieldEquationSurface data := by
  let law := data.selectedFieldLaw
  let rep := data.toMinimalQuadraticRepresentative
  let bridge := data.framed.object.bridge.selectedBridge
  let P := bridge.observer.selection.selectedProjection
  let Rqq := canonicalSelectedShadowPropagator bridge
  obtain
    ⟨hstate, hscalar, heffectiveScalar, _hregular, _hobserver, _hprojection,
      _hprojectionEq, hpromoted⟩ :=
    data.selectedFieldLawSurface
  obtain
    ⟨_hselectedEff, hgoverning, _hscalarGov, _heffectiveScalarGov⟩ :=
    data.selectedGoverningSurface
  obtain
    ⟨_hadm, _hpsd, _heq, _hmin, _hmineq, _hstateForm, hquadratic⟩ :=
    data.minimalQuadraticRepresentativeSurface
  refine ⟨hstate, hquadratic, hgoverning, hpromoted, hscalar, heffectiveScalar, ?_⟩
  intro x
  constructor
  · intro hx
    have hx' : law.residual x = SignedCount.zero := by
      simpa [LocalEventFourStateLaw.selectedFieldEquation] using hx
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [hscalar x] using hx'
    · simpa [heffectiveScalar x] using hx'
    · simpa [SelectedFieldLaw.regularSystem] using hx'
    · simpa [SelectedFieldLaw.regularSystem] using hx'
    · simpa [SelectedFieldLaw.regularSystem] using hx'
    · simpa [SelectedFieldLaw.observerTransport] using hx'
    · simpa [SelectedFieldLaw.observerTransport] using hx'
    · simpa [SelectedFieldLaw.observerTransport] using hx'
    · simpa [SelectedFieldLaw.projectionDatum, SelectedFieldLaw.observerTransport] using hx'
    · simpa [SelectedFieldLaw.projectionDatum, SelectedFieldLaw.regularSystem] using hx'
  · intro h
    simpa [LocalEventFourStateLaw.selectedFieldEquation, hscalar x] using h.1

end ClosureCurrent

end CoherenceCalculus
