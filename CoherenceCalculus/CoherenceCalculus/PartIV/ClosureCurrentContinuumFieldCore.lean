import CoherenceCalculus.PartIV.ClosureCurrentContinuumRepresentativeCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumEffectiveVariationalCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumPromotionCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumFieldCore

One selected operator-residual law on the least-motion cut.

The detached analytic lane already identifies:

* one common selected governing operator;
* one scalar residual read from that operator;
* one exact field/flow package;
* one collapsed constitutive/promotion package;
* one scalarized variational/observer/projection triad.

This file records the next honest simplification. Those layers are not
independent pieces of analytic structure. They are already generic wrappers of
one selected operator-residual law on the least-motion cut.

This is still not a PDE or an action principle. The point is only to expose
the strongest current law-shaped analytic surface without claiming more than
the detached lane presently proves.
-/

namespace ClosureCurrent

/-- One selected operator-residual law on the explicit four-state carrier. -/
structure SelectedFieldLaw where
  project : State → State
  operator : State → State
  residual : State → SignedCount
  project_zero : project State.zero = State.zero
  operator_visible : ∀ x : State, project (operator x) = operator x

/-- The regular variational system canonically induced by one selected
operator-residual law. -/
def SelectedFieldLaw.regularSystem
    (law : SelectedFieldLaw) :
    RegularVariationalSystem State State where
  lagrangianResidual := law.residual
  hamiltonianResidual := law.residual
  characteristicResidual := law.residual
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

/-- The observer-side conservative transport datum canonically induced by one
selected operator-residual law. -/
def SelectedFieldLaw.observerTransport
    (law : SelectedFieldLaw) :
    ConservativeTransportDatum State State where
  eulerianResidual := law.residual
  lagrangianResidual := law.residual
  characteristicResidual := law.residual
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

/-- The Hamilton--Jacobi projection datum canonically induced by one selected
operator-residual law. -/
def SelectedFieldLaw.projectionDatum
    (law : SelectedFieldLaw) :
    HamiltonJacobiProjectionDatum State State where
  dynamics := law.regularSystem
  observer := law.observerTransport
  observer_characteristic_eq := by
    intro q
    rfl

/-- The zero-constitutive promotion context canonically induced by one
selected operator-residual law. -/
def SelectedFieldLaw.promotionContext
    (law : SelectedFieldLaw) :
    PromotedConstitutiveContext State State where
  project := law.project
  transport := law.operator
  nonlinear := fun _ => State.zero
  reconstruct := fun x => x
  combine := State.add

/-- The regular variational triad already belongs to the canonical selected
operator-residual law. -/
theorem SelectedFieldLaw.regularSurface
    (law : SelectedFieldLaw) :
    ((∀ q : State, law.regularSystem.lagrangianResidual q = SignedCount.zero) ↔
      (∀ p : State, law.regularSystem.hamiltonianResidual p = SignedCount.zero) ∧
        (∀ q : State, law.regularSystem.characteristicResidual q = SignedCount.zero)) := by
  exact dynamics_triad law.regularSystem

/-- The observer-side transport triad already belongs to the canonical
selected operator-residual law. -/
theorem SelectedFieldLaw.observerSurface
    (law : SelectedFieldLaw) :
    (EulerianPresentation law.observerTransport ↔
      LagrangianPresentation law.observerTransport ∧
        CharacteristicPresentation law.observerTransport) := by
  exact observer_triad law.observerTransport

/-- The Hamilton--Jacobi bridge already belongs to the canonical selected
operator-residual law. -/
theorem SelectedFieldLaw.projectionSurface
    (law : SelectedFieldLaw) :
    (CharacteristicPresentation law.projectionDatum.observer ↔
      ∀ q : State,
        law.projectionDatum.dynamics.characteristicResidual q = SignedCount.zero) ∧
      (∀ q : State,
        law.projectionDatum.observer.characteristicResidual q =
          law.projectionDatum.dynamics.characteristicResidual q) := by
  exact ⟨hj_projection law.projectionDatum, fun q => rfl⟩

/-- The promoted constitutive term of the canonical selected operator-residual
law vanishes identically. -/
theorem SelectedFieldLaw.promotedConstitutiveZero
    (law : SelectedFieldLaw) :
    ∀ x : State,
      PromotedConstitutiveTerm law.promotionContext x = State.zero := by
  intro x
  unfold PromotedConstitutiveTerm SelectedFieldLaw.promotionContext
  simpa using law.project_zero

/-- The promoted observed law of the canonical selected operator-residual law
is exactly the same operator again. -/
theorem SelectedFieldLaw.promotedLawExact
    (law : SelectedFieldLaw) :
    ∀ x : State,
      promotedObservedLaw law.promotionContext x = law.operator x := by
  intro x
  unfold promotedObservedLaw SelectedFieldLaw.promotionContext
  calc
    State.add (law.project (law.operator x))
        (PromotedConstitutiveTerm law.promotionContext x)
        =
      State.add (law.project (law.operator x)) State.zero := by
        rw [law.promotedConstitutiveZero x]
    _ = law.project (law.operator x) := by
        exact State.add_zero _
    _ = law.operator x := by
        exact law.operator_visible x

/-- The selected operator-residual law canonically read from the detached
least-motion cut. -/
def LocalEventFourStateLaw.selectedFieldLaw
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedFieldLaw where
  project := data.framed.object.bridge.selectedBridge.observer.selection.selectedProjection
  operator := data.framed.object.bridge.generator.toFun
  residual := governingScalarResidual data
  project_zero := by
    let P := data.framed.object.bridge.selectedBridge.observer.selection.selectedProjection
    simpa using P.map_zero
  operator_visible := by
    intro x
    let P := data.framed.object.bridge.selectedBridge.observer.selection.selectedProjection
    let rep := data.toMinimalQuadraticRepresentative
    obtain
      ⟨_hadm, _hpsd, _hstateForm, _hcandidate, _hcut, _hmotion, _hstationary,
        _hgradComm, _hgradPQ, _hgradQP, hvis, _hcomm, _hzeroPQ, _hzeroQP⟩ :=
      data.stationaryQuadraticRepresentativeSurface
    obtain
      ⟨_hadm, _hpsd, _heq, _hmin, _hmineq, _hstateForm, hgenerator⟩ :=
      data.minimalQuadraticRepresentativeSurface
    have hvisComm : commutesWithProjection P rep.stateForm.op :=
      exact_visible_implies_commutes P rep.stateForm.op hvis
    have hvisSelf : rep.stateForm.op x = P (rep.stateForm.op x) := by
      have hx : rep.stateForm.op x = blockPP P rep.stateForm.op x := hvis x
      rw [operatorCompression_eq_blockPP] at hx
      rw [hvisComm x] at hx
      rw [P.idem] at hx
      exact hx
    calc
      P (data.framed.object.bridge.generator.toFun x) =
          P (rep.stateForm.op x) := by
            rw [(hgenerator x).symm]
      _ = rep.stateForm.op x := by
            exact hvisSelf.symm
      _ = data.framed.object.bridge.generator.toFun x := by
            exact hgenerator x

/-- One selected operator-residual law already carries the strongest current
common analytic data on the detached selected cut: the forced continuum law,
the two scalar residual readouts, the scalarized variational/observer/HJ
triad, and the zero-constitutive promoted law. -/
def SelectedFieldLawSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  (∀ x : State,
      data.stateDynamics.continuumLaw x = data.selectedFieldLaw.operator x) ∧
    (∀ x : State,
      scalarResidual data x = data.selectedFieldLaw.residual x) ∧
    (∀ x : State,
      effectiveScalarResidual data x = data.selectedFieldLaw.residual x) ∧
    ((∀ q : State,
        data.selectedFieldLaw.regularSystem.lagrangianResidual q = SignedCount.zero) ↔
      (∀ p : State,
          data.selectedFieldLaw.regularSystem.hamiltonianResidual p = SignedCount.zero) ∧
        (∀ q : State,
          data.selectedFieldLaw.regularSystem.characteristicResidual q = SignedCount.zero)) ∧
    (EulerianPresentation data.selectedFieldLaw.observerTransport ↔
      LagrangianPresentation data.selectedFieldLaw.observerTransport ∧
        CharacteristicPresentation data.selectedFieldLaw.observerTransport) ∧
    (CharacteristicPresentation data.selectedFieldLaw.projectionDatum.observer ↔
      ∀ q : State,
        data.selectedFieldLaw.projectionDatum.dynamics.characteristicResidual q =
          SignedCount.zero) ∧
    (∀ q : State,
      data.selectedFieldLaw.projectionDatum.observer.characteristicResidual q =
        data.selectedFieldLaw.projectionDatum.dynamics.characteristicResidual q) ∧
    (∀ x : State,
      promotedObservedLaw data.selectedFieldLaw.promotionContext x =
        data.selectedFieldLaw.operator x)

/-- The detached selected analytic lane already collapses to one selected
operator-residual law. The forced continuum law, the scalarized
variational/observer/Hamilton--Jacobi surfaces, and the zero-constitutive
promotion law are all generic wrappers of that same selected law. -/
theorem LocalEventFourStateLaw.selectedFieldLawSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedFieldLawSurface data := by
  have hstateAdmissible :
      data.stateDynamics.limitClass.admissible data.selectedFieldLaw.operator := by
    simpa [LocalEventFourStateLaw.selectedFieldLaw,
      LocalEventFourStateLaw.toContinuumRepresentative]
      using data.toContinuumRepresentative.stateLaw_forced.1
  obtain ⟨_hquadEff, _hgoverning, hscalar, heffectiveScalar⟩ :=
    data.selectedGoverningSurface
  obtain ⟨hproj, hprojEq⟩ := data.selectedFieldLaw.projectionSurface
  refine ⟨?_, ?_, ?_, data.selectedFieldLaw.regularSurface,
    data.selectedFieldLaw.observerSurface, hproj, hprojEq, ?_⟩
  · intro x
    exact (data.stateDynamics.limitClass_pointwise_forcing hstateAdmissible x).symm
  · intro x
    exact hscalar x
  · intro x
    exact heffectiveScalar x
  · intro x
    exact data.selectedFieldLaw.promotedLawExact x

end ClosureCurrent

end CoherenceCalculus
