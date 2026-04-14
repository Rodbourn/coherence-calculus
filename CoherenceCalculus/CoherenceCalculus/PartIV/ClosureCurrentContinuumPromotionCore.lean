import CoherenceCalculus.PartIV.ClosureCurrentContinuumFlowCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumPromotionCore

Law-native constitutive collapse of the selected governing flow.

The selected field/flow package is already strong enough to support the generic
Part III promotion interfaces. The crucial point is that the apparent
constitutive term may be taken to be the returned residual of the exact
effective selected law, and that returned residual already vanishes on the
least-motion cut.

So the selected cut admits no exogenous constitutive completion: the promoted
observed law collapses back to the same forced selected continuum law, and the
finite promotion chain carries only that one branch.
-/

namespace ClosureCurrent

/-- Law-native promoted constitutive context of the selected governing flow. -/
def LocalEventFourStateLaw.selectedPromotionContext
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    PromotedConstitutiveContext State State :=
  let rep := data.toMinimalQuadraticRepresentative
  let bridge := data.framed.object.bridge.selectedBridge
  let selection := bridge.observer.selection
  let P := selection.selectedProjection
  let Rqq := canonicalSelectedShadowPropagator bridge
  {
    project := P
    transport := effectiveOp P rep.stateForm.op Rqq
    nonlinear := returnedResidual (residualReturnFieldOf P rep.stateForm.op Rqq)
    reconstruct := fun x => x
    combine := State.add
  }

/-- The apparent constitutive term on the selected cut vanishes identically:
it is already just the returned residual of the exact effective selected law,
and that residual is zero. -/
theorem LocalEventFourStateLaw.selectedPromotionConstitutiveZero
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ∀ x : State,
      PromotedConstitutiveTerm data.selectedPromotionContext x = State.zero := by
  let rep := data.toMinimalQuadraticRepresentative
  let bridge := data.framed.object.bridge.selectedBridge
  let selection := bridge.observer.selection
  let P := selection.selectedProjection
  let Rqq := canonicalSelectedShadowPropagator bridge
  obtain ⟨_hvis, _heff, _hschur, hreturn⟩ :=
    data.effectiveQuadraticRepresentativeSurface
  intro x
  unfold PromotedConstitutiveTerm LocalEventFourStateLaw.selectedPromotionContext
  change P
      (returnedResidual (residualReturnFieldOf P rep.stateForm.op Rqq) x) =
    State.zero
  rw [hreturn x, P.map_zero]

/-- The carried transport part of the selected promotion context is already
the forced selected continuum law. -/
theorem LocalEventFourStateLaw.selectedPromotionBoundaryIdentity
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ∀ x : State,
      data.selectedPromotionContext.project
          (data.selectedPromotionContext.transport
            (data.selectedPromotionContext.reconstruct x)) =
        data.stateDynamics.continuumLaw x := by
  let rep := data.toMinimalQuadraticRepresentative
  let bridge := data.framed.object.bridge.selectedBridge
  let selection := bridge.observer.selection
  let P := selection.selectedProjection
  let Rqq := canonicalSelectedShadowPropagator bridge
  obtain ⟨_hquadEff, hgoverning, _hscalarGov, _heffectiveScalarGov⟩ :=
    data.selectedGoverningSurface
  obtain ⟨_hinterp, hPP, _hPQ, _hQP, _hQQ, _hflowC1, hflowFormula⟩ :=
    data.selectedGoverningFlowSurface
  intro x
  unfold LocalEventFourStateLaw.selectedPromotionContext
  change P (effectiveOp P rep.stateForm.op Rqq x) = data.stateDynamics.continuumLaw x
  calc
    P (effectiveOp P rep.stateForm.op Rqq x) =
        P (blockPP P rep.stateForm.op x) := by
          rw [hflowFormula 0 x]
    _ = blockPP P rep.stateForm.op x := by
          rw [operatorCompression_eq_blockPP, P.idem]
    _ = data.framed.object.bridge.generator.toFun x := by
          exact hPP 0 x
    _ = data.stateDynamics.continuumLaw x := by
          exact rfl

/-- The promoted observed law on the selected cut is exactly the same forced
selected continuum law: no extra constitutive completion remains. -/
theorem LocalEventFourStateLaw.selectedPromotedLawExact
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ∀ x : State,
      promotedObservedLaw data.selectedPromotionContext x =
        data.stateDynamics.continuumLaw x := by
  intro x
  unfold promotedObservedLaw
  calc
    data.selectedPromotionContext.combine
        (data.selectedPromotionContext.project
          (data.selectedPromotionContext.transport
            (data.selectedPromotionContext.reconstruct x)))
        (PromotedConstitutiveTerm data.selectedPromotionContext x)
        =
      State.add
        (data.selectedPromotionContext.project
          (data.selectedPromotionContext.transport
            (data.selectedPromotionContext.reconstruct x)))
        (PromotedConstitutiveTerm data.selectedPromotionContext x) := by
          rfl
    _ =
      State.add
        (data.stateDynamics.continuumLaw x)
        (PromotedConstitutiveTerm data.selectedPromotionContext x) := by
          rw [data.selectedPromotionBoundaryIdentity x]
    _ = State.add (data.stateDynamics.continuumLaw x) State.zero := by
          rw [data.selectedPromotionConstitutiveZero x]
    _ = data.stateDynamics.continuumLaw x := by
          exact State.add_zero (data.stateDynamics.continuumLaw x)

/-- The selected promoted observed law as its own named map. -/
def LocalEventFourStateLaw.selectedPromotedLaw
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    State → State :=
  promotedObservedLaw data.selectedPromotionContext

/-- Characteristic-scale promotion data carried by the selected constitutive
context. -/
def LocalEventFourStateLaw.selectedPromotionData
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    CharacteristicScalePromotionData data.selectedPromotionContext where
  solution_bijection :=
    ∀ x : State,
      data.selectedPromotedLaw x = data.stateDynamics.continuumLaw x
  boundary_identity :=
    ∀ x : State,
      data.selectedPromotionContext.project
          (data.selectedPromotionContext.transport
            (data.selectedPromotionContext.reconstruct x)) =
        data.stateDynamics.continuumLaw x
  transported_test_identity :=
    ∀ x : State,
      PromotedConstitutiveTerm data.selectedPromotionContext x = State.zero

/-- The solution-bijection field is just the exact equality with the forced
selected continuum law. -/
theorem LocalEventFourStateLaw.selectedPromotionSolution
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    data.selectedPromotionData.solution_bijection := by
  exact data.selectedPromotedLawExact

/-- The boundary-identity field is the exact carried transport identity on the
selected cut. -/
theorem LocalEventFourStateLaw.selectedPromotionBoundary
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    data.selectedPromotionData.boundary_identity := by
  exact data.selectedPromotionBoundaryIdentity

/-- The transported-test field is exact vanishing of the apparent constitutive
term. -/
theorem LocalEventFourStateLaw.selectedPromotionTests
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    data.selectedPromotionData.transported_test_identity := by
  exact data.selectedPromotionConstitutiveZero

/-- The selected promotion data carries exactly the solution, boundary, and
transported-test surfaces. -/
theorem LocalEventFourStateLaw.selectedPromotionDataSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    data.selectedPromotionData.solution_bijection ∧
      data.selectedPromotionData.boundary_identity ∧
      data.selectedPromotionData.transported_test_identity := by
  exact
    ⟨data.selectedPromotionSolution,
      data.selectedPromotionBoundary,
      data.selectedPromotionTests⟩

/-- Generic Part III characteristic-scale promotion wrapper instantiated on
the selected constitutive package. -/
def LocalEventFourStateLaw.selectedScalePromotion
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    CharacteristicScalePromotionData data.selectedPromotionContext :=
  characteristic_scale_promotion data.selectedPromotionContext
    data.selectedPromotionData

/-- Finite admissible-promotion chain on the selected promoted law: every
stage selects the same forced selected law. -/
def LocalEventFourStateLaw.selectedAdmissiblePromotionData
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law)
    (length : Nat) :
    AdmissiblePromotionData (State → State) where
  length := length
  selectedLaw := fun _ => data.selectedPromotedLaw
  unique_step := fun _ _ =>
    ∀ other : State → State,
      data.stateDynamics.limitClass.admissible other →
      ∀ x : State,
        other x = data.selectedPromotedLaw x

/-- Every stage in the selected finite promotion chain is uniquely forced to
the same promoted observed law. -/
theorem LocalEventFourStateLaw.selectedPromotionUniqueStep
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law)
    (length n : Nat) (hn : n ≤ length) :
    (data.selectedAdmissiblePromotionData length).unique_step n hn := by
  intro other hother x
  calc
    other x = data.stateDynamics.continuumLaw x := by
      exact data.stateDynamics.limitClass_pointwise_forcing hother x
    _ = data.selectedPromotedLaw x := by
      exact (data.selectedPromotedLawExact x).symm

/-- The generic admissible-promotion wrapper instantiated on the selected
promoted law. -/
def LocalEventFourStateLaw.selectedAdmissiblePromotion
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law)
    (length : Nat) :
    AdmissiblePromotionData (State → State) :=
  admissible_promotion (data.selectedAdmissiblePromotionData length)

/-- Minimum-energy interpretation package for the selected promotion chain:
admissibility leaves only the same forced selected law at every finite stage.
-/
def LocalEventFourStateLaw.selectedMinimumEnergyPromotion
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law)
    (length : Nat) :
    MinimumEnergyPromotion where
  minimum_energy_branch :=
    ∀ n : Nat, n ≤ length →
      ∀ other : State → State,
        data.stateDynamics.limitClass.admissible other →
        ∀ x : State,
          other x = (data.selectedAdmissiblePromotionData length).selectedLaw n x
  admissibility_interpretation :=
    ∀ n : Nat, ∀ hn : n ≤ length,
      (data.selectedAdmissiblePromotionData length).unique_step n hn

/-- The minimum-energy branch is exactly the unique forced selected promoted
law. -/
theorem LocalEventFourStateLaw.selectedMinimumEnergyBranch
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law)
    (length : Nat) :
    (data.selectedMinimumEnergyPromotion length).minimum_energy_branch := by
  intro n hn other hother x
  exact data.selectedPromotionUniqueStep length n hn other hother x

/-- The admissibility interpretation is exactly the unique-step theorem for
the selected finite promotion chain. -/
theorem LocalEventFourStateLaw.selectedMinimumEnergyAdmissibility
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law)
    (length : Nat) :
    (data.selectedMinimumEnergyPromotion length).admissibility_interpretation := by
  intro n hn
  exact data.selectedPromotionUniqueStep length n hn

/-- Manuscript-facing promotion surface of the selected governing flow. -/
def SelectedPromotionSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  data.selectedPromotionData.solution_bijection ∧
    data.selectedPromotionData.boundary_identity ∧
    data.selectedPromotionData.transported_test_identity ∧
    ∀ length : Nat,
      (data.selectedMinimumEnergyPromotion length).minimum_energy_branch ∧
        (data.selectedMinimumEnergyPromotion length).admissibility_interpretation

/-- The selected governing field/flow package already collapses its own
constitutive appearance and promotion chain. -/
theorem LocalEventFourStateLaw.selectedPromotionSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedPromotionSurface data := by
  refine ⟨data.selectedPromotionSolution, data.selectedPromotionBoundary,
    data.selectedPromotionTests, ?_⟩
  intro length
  exact
    ⟨data.selectedMinimumEnergyBranch length,
      data.selectedMinimumEnergyAdmissibility length⟩

end ClosureCurrent

end CoherenceCalculus
