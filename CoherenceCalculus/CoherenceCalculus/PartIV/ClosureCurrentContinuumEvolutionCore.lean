import CoherenceCalculus.PartIV.ClosureCurrentContinuumFirstOrderCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumEvolutionCore

Canonical autonomous evolution law of the detached selected cut.

`ClosureCurrentContinuumFirstOrderCore` shows that the detached selected cut
already carries one canonical first-order law object: one exact selected flow,
one selected operator, and one scalar equation read from that same operator.

This file upgrades that surface from a theorem package to an actual law object.
It packages the exact selected flow, the common selected generator, and the
governing scalar residual as one autonomous evolution law, then proves that
this law is uniquely forced among all autonomous first-order laws compatible
with the same forced continuum class and the same selected scalar residual.

This is still not a spatial differential PDE. It is the strongest current
autonomous evolution form honestly forced by the detached selected law itself.
-/

namespace ClosureCurrent

/-- An autonomous first-order evolution law on the selected carrier. The flow is
allowed to be stage-parameterized, but every stage must already agree with one
common generator. -/
structure EvolutionLaw where
  flow : Nat → State → State
  generator : State → State
  residual : State → SignedCount
  stage_constant : ∀ n : Nat, ∀ x : State, flow n x = generator x

/-- Two evolution laws are equal once their flow, generator, and residual
agree. The remaining field is proof data only. -/
theorem EvolutionLaw.ext
    {law law' : EvolutionLaw}
    (hflow : law.flow = law'.flow)
    (hgenerator : law.generator = law'.generator)
    (hresidual : law.residual = law'.residual) :
    law = law' := by
  cases law
  cases law'
  cases hflow
  cases hgenerator
  cases hresidual
  simp

/-- The zero set of an evolution law residual. -/
def EvolutionLaw.solution
    (law : EvolutionLaw) :
    State → Prop :=
  fun x => law.residual x = SignedCount.zero

/-- The canonical autonomous evolution law carried by the detached selected
cut. -/
def LocalEventFourStateLaw.selectedEvolutionLaw
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    EvolutionLaw where
  flow := data.selectedContinuousEffectiveFlowData.effectiveOp
  generator := data.selectedFieldLaw.operator
  residual := data.selectedFieldLaw.residual
  stage_constant := by
    intro n x
    exact (data.selectedFirstOrderLawSurface.2.2.2.1 n x)

/-- Admissible autonomous evolution laws for the detached selected cut: the
generator lies in the forced continuum class, the residual is the governing
selected residual, and the stagewise flow is exactly that same generator. -/
def LocalEventFourStateLaw.selectedEvolutionLawClass
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ContinuumLimitClass EvolutionLaw where
  admissible := fun law =>
    data.stateDynamics.limitClass.admissible law.generator ∧
      law.residual = data.selectedFieldLaw.residual ∧
      (∀ n : Nat, ∀ x : State, law.flow n x = law.generator x)

/-- The canonical selected evolution law is admissible for its law class. -/
theorem LocalEventFourStateLaw.selectedEvolutionLaw_admissible
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    data.selectedEvolutionLawClass.admissible data.selectedEvolutionLaw := by
  obtain
    ⟨hstate, _hscalar, _heffectiveScalar, _hreg, _hobs, _hproj, _hprojEq,
      _hpromo⟩ := data.selectedFieldLawSurface
  have hstateEq :
      data.stateDynamics.continuumLaw = data.selectedFieldLaw.operator :=
    funext hstate
  refine ⟨?_, rfl, data.selectedEvolutionLaw.stage_constant⟩
  simpa [LocalEventFourStateLaw.selectedEvolutionLaw] using
    (show data.stateDynamics.limitClass.admissible data.selectedFieldLaw.operator by
      rw [← hstateEq]
      exact data.stateDynamics.continuumLaw_admissible)

/-- Any admissible autonomous evolution law is already forced to equal the
canonical selected evolution law. -/
theorem LocalEventFourStateLaw.selectedEvolutionLaw_pointwise_forcing
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law)
    {law : EvolutionLaw}
    (hlaw : data.selectedEvolutionLawClass.admissible law) :
    law = data.selectedEvolutionLaw := by
  rcases hlaw with ⟨hgenerator, hresidual, hstage⟩
  have hop :
      law.generator = data.selectedFieldLaw.operator := by
    funext x
    exact data.stateDynamics.limitClass_pointwise_forcing hgenerator x
  have hflow :
      law.flow = data.selectedEvolutionLaw.flow := by
    funext n
    funext x
    calc
      law.flow n x = law.generator x := by
        exact hstage n x
      _ = data.selectedFieldLaw.operator x := by
        rw [hop]
      _ = data.selectedEvolutionLaw.flow n x := by
        symm
        exact data.selectedEvolutionLaw.stage_constant n x
  have hgenerator' :
      law.generator = data.selectedEvolutionLaw.generator := by
    exact hop
  have hresidual' :
      law.residual = data.selectedEvolutionLaw.residual := by
    exact hresidual
  exact EvolutionLaw.ext hflow hgenerator' hresidual'

/-- Manuscript-facing forcing surface of the canonical autonomous evolution law
on the detached selected cut. -/
def SelectedEvolutionLawForcingSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  ForcedContinuumLaw data.selectedEvolutionLawClass data.selectedEvolutionLaw

/-- The detached selected cut already forces one unique autonomous evolution
law. -/
theorem LocalEventFourStateLaw.selectedEvolutionLawForcingSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedEvolutionLawForcingSurface data := by
  exact
    discrete_to_continuum_forcing_principle
      data.selectedEvolutionLawClass
      data.selectedEvolutionLaw
      data.selectedEvolutionLaw_admissible
      (fun law hlaw => data.selectedEvolutionLaw_pointwise_forcing hlaw)

/-- Manuscript-facing autonomous evolution surface of the detached selected cut.
The exact selected flow, the forced selected operator, and the current scalar
PDE/action realizations are all read from one unique autonomous evolution law. -/
def SelectedEvolutionLawSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  SelectedEvolutionLawForcingSurface data ∧
    (∀ n : Nat, ∀ x : State,
      data.selectedEvolutionLaw.flow n x = data.selectedFieldLaw.operator x) ∧
    (∀ x : State,
      data.selectedEvolutionLaw.generator x = data.selectedFieldLaw.operator x) ∧
    (∀ x : State,
      data.selectedEvolutionLaw.residual x = data.selectedFieldLaw.residual x) ∧
    (∀ x : State,
      data.selectedEvolutionLaw.residual x =
        SignedCount.ofNat
          (State.pair x (data.selectedEvolutionLaw.generator x))) ∧
    (∀ x : State,
      data.selectedEvolutionLaw.solution x ↔ data.selectedFieldEquation x) ∧
    (∀ x : State,
      data.selectedEvolutionLaw.solution x ↔ data.scalarPDERealization.solution x) ∧
    (∀ x : State,
      data.selectedEvolutionLaw.solution x ↔
        data.scalarActionRealization.stationary x)

/-- The detached selected cut already carries one uniquely forced autonomous
evolution law. Its generator is the common selected operator, its residual is
the governing selected residual, and its zero set is exactly the current scalar
PDE/action zero set. -/
theorem LocalEventFourStateLaw.selectedEvolutionLawSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedEvolutionLawSurface data := by
  have hforced :
      SelectedEvolutionLawForcingSurface data := by
    exact data.selectedEvolutionLawForcingSurface
  have hfirst :
      SelectedFirstOrderLawSurface data := by
    exact data.selectedFirstOrderLawSurface
  obtain
    ⟨_hfieldForced, _hscalarLaw, _hflow, hflowOp, hflowScalar, hequation,
      hpde, haction⟩ := hfirst
  have hsolutionFlow :
      ∀ x : State,
        data.selectedEvolutionLaw.solution x ↔
          SignedCount.ofNat
              (State.pair x (data.selectedContinuousEffectiveFlowData.effectiveOp 0 x)) =
            SignedCount.zero := by
    intro x
    constructor
    · intro hx
      calc
        SignedCount.ofNat
            (State.pair x (data.selectedContinuousEffectiveFlowData.effectiveOp 0 x)) =
            data.selectedFieldLaw.residual x := by
              symm
              exact hflowScalar 0 x
        _ = SignedCount.zero := by
              simpa [EvolutionLaw.solution, LocalEventFourStateLaw.selectedEvolutionLaw] using hx
    · intro hx
      calc
        data.selectedEvolutionLaw.residual x = data.selectedFieldLaw.residual x := by
          rfl
        _ =
            SignedCount.ofNat
              (State.pair x (data.selectedContinuousEffectiveFlowData.effectiveOp 0 x)) := by
                exact hflowScalar 0 x
        _ = SignedCount.zero := hx
  have hsolutionEq :
      ∀ x : State,
        data.selectedEvolutionLaw.solution x ↔ data.selectedFieldEquation x := by
    intro x
    constructor
    · intro hx
      exact (hequation 0 x).2 ((hsolutionFlow x).1 hx)
    · intro hx
      exact (hsolutionFlow x).2 ((hequation 0 x).1 hx)
  refine ⟨hforced, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n x
    exact hflowOp n x
  · intro x
    rfl
  · intro x
    rfl
  · intro x
    calc
      data.selectedEvolutionLaw.residual x = data.selectedFieldLaw.residual x := by
        rfl
      _ =
          SignedCount.ofNat
            (State.pair x (data.selectedContinuousEffectiveFlowData.effectiveOp 0 x)) := by
              exact hflowScalar 0 x
      _ =
          SignedCount.ofNat
            (State.pair x (data.selectedEvolutionLaw.generator x)) := by
              rw [hflowOp 0 x]
              rfl
  · intro x
    exact hsolutionEq x
  · intro x
    constructor
    · intro hx
      exact (data.scalarPDERealization.solution_iff_selectedEquation x).2
        ((hsolutionEq x).1 hx)
    · intro hx
      exact (hsolutionEq x).2
        ((data.scalarPDERealization.solution_iff_selectedEquation x).1 hx)
  · intro x
    constructor
    · intro hx
      exact (data.scalarActionRealization.stationary_iff_selectedEquation x).2
        ((hsolutionEq x).1 hx)
    · intro hx
      exact (hsolutionEq x).2
        ((data.scalarActionRealization.stationary_iff_selectedEquation x).1 hx)

end ClosureCurrent

end CoherenceCalculus
