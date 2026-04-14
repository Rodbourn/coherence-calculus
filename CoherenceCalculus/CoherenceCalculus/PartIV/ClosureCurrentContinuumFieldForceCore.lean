import CoherenceCalculus.PartIV.ClosureCurrentContinuumFieldCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumFieldForceCore

Forcing surface of the selected operator-residual law.

`ClosureCurrentContinuumFieldCore` identifies one selected operator-residual
law on the least-motion cut and shows that the detached variational, observer,
projection, and promotion layers are all presentations of it.

The next honest sharpening is uniqueness. This file records that the current
selected field law is not merely one useful package. It is already the unique
selected operator-residual law compatible with:

* the fixed selected projector;
* the forced continuum limit class on the four-state carrier;
* the governing scalar residual.

This is still not a PDE or action principle. It is the strongest current
forcing statement for the law-shaped analytic object itself.
-/

namespace ClosureCurrent

/-- Two selected field laws are equal once their projector, operator, and
residual agree. The remaining fields are proof data only. -/
theorem SelectedFieldLaw.ext
    {law law' : SelectedFieldLaw}
    (hproject : law.project = law'.project)
    (hoperator : law.operator = law'.operator)
    (hresidual : law.residual = law'.residual) :
    law = law' := by
  cases law
  cases law'
  cases hproject
  cases hoperator
  cases hresidual
  simp

/-- Admissible selected field laws for the detached selected cut: the
projector is the selected one, the operator lies in the forced continuum class
on the four-state carrier, and the residual is the governing scalar residual.
-/
def LocalEventFourStateLaw.selectedFieldLawClass
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ContinuumLimitClass SelectedFieldLaw where
  admissible := fun law =>
    law.project = data.selectedFieldLaw.project ∧
      data.stateDynamics.limitClass.admissible law.operator ∧
      law.residual = data.selectedFieldLaw.residual

/-- The detached selected field law itself is admissible for its law class. -/
theorem LocalEventFourStateLaw.selectedFieldLaw_admissible
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    data.selectedFieldLawClass.admissible data.selectedFieldLaw := by
  obtain
    ⟨hstate, _hscalar, _heffectiveScalar, _hreg, _hobs, _hproj, _hprojEq,
      _hpromo⟩ := data.selectedFieldLawSurface
  have hstateEq :
      data.stateDynamics.continuumLaw = data.selectedFieldLaw.operator :=
    funext hstate
  refine ⟨rfl, ?_, rfl⟩
  rw [← hstateEq]
  exact data.stateDynamics.continuumLaw_admissible

/-- Any admissible selected field law is already forced to equal the detached
selected field law. -/
theorem LocalEventFourStateLaw.selectedFieldLaw_pointwise_forcing
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law)
    {law : SelectedFieldLaw}
    (hlaw : data.selectedFieldLawClass.admissible law) :
    law = data.selectedFieldLaw := by
  rcases hlaw with ⟨hproject, hoperator, hresidual⟩
  obtain
    ⟨hstate, _hscalar, _heffectiveScalar, _hreg, _hobs, _hproj, _hprojEq,
      _hpromo⟩ := data.selectedFieldLawSurface
  have hop :
      law.operator = data.selectedFieldLaw.operator := by
    funext x
    calc
      law.operator x = data.stateDynamics.continuumLaw x := by
        exact data.stateDynamics.limitClass_pointwise_forcing hoperator x
      _ = data.selectedFieldLaw.operator x := by
        exact hstate x
  exact SelectedFieldLaw.ext hproject hop hresidual

/-- Manuscript-facing forcing surface of the selected operator-residual law. -/
def SelectedFieldLawForcingSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  ForcedContinuumLaw data.selectedFieldLawClass data.selectedFieldLaw

/-- The detached analytic lane already forces one unique selected
operator-residual law on the least-motion cut. -/
theorem LocalEventFourStateLaw.selectedFieldLawForcingSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedFieldLawForcingSurface data := by
  exact
    discrete_to_continuum_forcing_principle
      data.selectedFieldLawClass
      data.selectedFieldLaw
      data.selectedFieldLaw_admissible
      (fun law hlaw => data.selectedFieldLaw_pointwise_forcing hlaw)

end ClosureCurrent

end CoherenceCalculus
