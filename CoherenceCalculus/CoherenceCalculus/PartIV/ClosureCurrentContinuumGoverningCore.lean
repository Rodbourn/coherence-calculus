import CoherenceCalculus.PartIV.ClosureCurrentContinuumEffectiveVariationalCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumGoverningCore

One governing selected operator on the least-motion cut.

The current detached analytic lane already proves three operator identities
separately:

* the selected quadratic law is the exact effective observable law on the
  least-motion stationary cut;
* the selected quadratic law is the matched selected generator;
* the scalar residual may be read from that same generator.

This file packages those equalities into one public surface. It still stops
short of a PDE or action principle. The point is simply that the strongest
current analytic lane already has one governing selected operator.
-/

namespace ClosureCurrent

/-- Signed-count scalar residual read directly from the matched selected
generator. -/
def governingScalarResidual
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    State → SignedCount :=
  fun x =>
    SignedCount.ofNat
      (State.pair x (data.framed.object.bridge.generator.toFun x))

/-- Governing selected-operator surface of the detached continuum law.

On the least-motion stationary cut, the selected quadratic law, the exact
effective selected law, and the matched selected generator already agree
pointwise, and the scalar residual may be read from that one common operator.
-/
def SelectedGoverningSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  let rep := data.toMinimalQuadraticRepresentative
  let bridge := data.framed.object.bridge.selectedBridge
  let P := bridge.observer.selection.selectedProjection
  let Rqq := canonicalSelectedShadowPropagator bridge
  (∀ x : State,
      rep.stateForm.op x = effectiveOp P rep.stateForm.op Rqq x) ∧
    (∀ x : State,
      effectiveOp P rep.stateForm.op Rqq x =
        data.framed.object.bridge.generator.toFun x) ∧
    (∀ x : State,
      scalarResidual data x = governingScalarResidual data x) ∧
    (∀ x : State,
      effectiveScalarResidual data x = governingScalarResidual data x)

/-- The detached least-motion selected surface already has one governing
operator: the selected quadratic law, its exact effective selected law, and
the matched selected generator coincide pointwise, and the scalar residual can
be read from that same operator. -/
theorem LocalEventFourStateLaw.selectedGoverningSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedGoverningSurface data := by
  let rep := data.toMinimalQuadraticRepresentative
  let bridge := data.framed.object.bridge.selectedBridge
  let P := bridge.observer.selection.selectedProjection
  let Rqq := canonicalSelectedShadowPropagator bridge
  obtain
    ⟨_hadm, _hpsd, _heq, _hmin, _hmineq, _hstateForm, hgenerator⟩ :=
    data.minimalQuadraticRepresentativeSurface
  obtain ⟨_hvis, heffective, _hschur, _hreturn⟩ :=
    data.effectiveQuadraticRepresentativeSurface
  obtain
    ⟨heffectiveScalar, _heffectiveGenerator, _hdynEff, _hobsEff, _hprojEff,
      _hprojEqEff⟩ :=
    data.effectiveVariationalRepresentativeSurface
  obtain
    ⟨_hquad, _hquadraticScalar, hgeneratorScalar, _hdynamics, _hobserver, _hprojection,
      _hcharacteristic, _hdyn, _hobs, _hstateForm⟩ :=
    data.variationalRepresentativeSurface
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    exact heffective x
  · intro x
    calc
      effectiveOp P rep.stateForm.op Rqq x = rep.stateForm.op x := by
        symm
        exact heffective x
      _ = data.framed.object.bridge.generator.toFun x := by
        exact hgenerator x
  · intro x
    simpa [governingScalarResidual] using hgeneratorScalar x
  · intro x
    calc
      effectiveScalarResidual data x = scalarResidual data x := by
        exact heffectiveScalar x
      _ = governingScalarResidual data x := by
        simpa [governingScalarResidual] using hgeneratorScalar x

end ClosureCurrent

end CoherenceCalculus
