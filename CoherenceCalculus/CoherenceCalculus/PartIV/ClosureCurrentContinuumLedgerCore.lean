import CoherenceCalculus.PartIV.ClosureCurrentContinuumRealizationCore
import CoherenceCalculus.Foundation.RealizationCalculusCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumLedgerCore

Exact realization-ledger surface of the detached selected operator law.

`ClosureCurrentContinuumRealizationCore` gives the current honest scalar
realization boundary: the selected equation already has canonical scalar
PDE-form and action-form realizations, and both come from one concrete
selected quadratic density.

The next honest strengthening is not yet a spatial differential PDE. It is the
host-side exactness statement already supported by the rebuilt realization
calculus: the same selected operator law admits a canonical realization chain
with no hidden crimes, and the scalar density/residual are read directly from
that exact realized residual.
-/

namespace ClosureCurrent

/-- Minimal realization law whose continuum residual is exactly the selected
operator on the detached selected cut. -/
def LocalEventFourStateLaw.selectedRealizationLaw
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    VariationalLaw where
  trialSpace := Unit
  testSpace := State
  bilinear := fun _ x => x
  load := fun x => State.add x (data.selectedFieldLaw.operator x)
  observables := Unit
  invariants := Unit

/-- Canonical realization chain with every realized residual representative
already equal to the selected operator. -/
def LocalEventFourStateLaw.selectedRealizationChain
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    RealizationChain data.selectedRealizationLaw where
  trialRealization := Unit
  testRealization := State
  trialLift := fun _ => ()
  testLift := fun x => x
  geometryData := Unit
  quadratureData := Unit
  stageData := Unit
  solverData := Unit
  interfaceData := Unit
  residualProj := fun _ x => data.selectedFieldLaw.operator x
  residualGeom := fun _ x => data.selectedFieldLaw.operator x
  residualQuad := fun _ x => data.selectedFieldLaw.operator x
  residualAlias := fun _ x => data.selectedFieldLaw.operator x
  residualSplit := fun _ x => data.selectedFieldLaw.operator x
  residualLin := fun _ x => data.selectedFieldLaw.operator x
  residualAlg := fun _ x => data.selectedFieldLaw.operator x
  residualBc := fun _ x => data.selectedFieldLaw.operator x
  residualIface := fun _ x => data.selectedFieldLaw.operator x

/-- The continuum residual of the canonical realization law is exactly the
selected operator. -/
theorem LocalEventFourStateLaw.selectedContinuumResidual
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ∀ x : State,
      continuumResidual data.selectedRealizationChain () x =
        data.selectedFieldLaw.operator x := by
  intro x
  unfold continuumResidual LocalEventFourStateLaw.selectedRealizationChain
    LocalEventFourStateLaw.selectedRealizationLaw
  exact State.sub_eq_right_of_add_left rfl

/-- The canonical selected realization chain is exact: every realization-crime
entry vanishes pointwise. -/
theorem LocalEventFourStateLaw.selectedRealizationExact
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    realizationExact data.selectedRealizationChain := by
  intro u v
  cases u
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold typedCrimeLedger
    simpa [data.selectedContinuumResidual v] using
      State.sub_self (data.selectedFieldLaw.operator v)
  · simp [typedCrimeLedger, LocalEventFourStateLaw.selectedRealizationChain,
      State.sub_self]
  · simp [typedCrimeLedger, LocalEventFourStateLaw.selectedRealizationChain,
      State.sub_self]
  · simp [typedCrimeLedger, LocalEventFourStateLaw.selectedRealizationChain,
      State.sub_self]
  · simp [typedCrimeLedger, LocalEventFourStateLaw.selectedRealizationChain,
      State.sub_self]
  · simp [typedCrimeLedger, LocalEventFourStateLaw.selectedRealizationChain,
      State.sub_self]
  · simp [typedCrimeLedger, LocalEventFourStateLaw.selectedRealizationChain,
      State.sub_self]
  · simp [typedCrimeLedger, LocalEventFourStateLaw.selectedRealizationChain,
      State.sub_self]
  · simp [typedCrimeLedger, LocalEventFourStateLaw.selectedRealizationChain,
      State.sub_self]

/-- Manuscript-facing exact realization-ledger surface of the detached selected
operator law. -/
def SelectedLedgerSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  realizationExact data.selectedRealizationChain ∧
    (∀ x : State,
      residualReal data.selectedRealizationChain () x =
        continuumResidual data.selectedRealizationChain () x) ∧
    (∀ x : State,
      continuumResidual data.selectedRealizationChain () x =
        data.selectedFieldLaw.operator x) ∧
    (∀ x : State,
      residualReal data.selectedRealizationChain () x =
        data.selectedFieldLaw.operator x) ∧
    (∀ x : State,
      State.pair x (residualReal data.selectedRealizationChain () x) =
        data.selectedQuadraticDensity x) ∧
    (∀ x : State,
      data.selectedFieldLaw.residual x =
        SignedCount.ofNat
          (State.pair x (residualReal data.selectedRealizationChain () x)))

/-- The detached selected operator law already admits a canonical no-hidden-
crime realization chain. The realized residual is exactly the selected
operator, and the current scalar flagship quantities are read directly from
that exact realized residual. -/
theorem LocalEventFourStateLaw.selectedLedgerSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedLedgerSurface data := by
  have hreal :
      ∀ x : State,
        residualReal data.selectedRealizationChain () x =
          data.selectedFieldLaw.operator x := by
    intro x
    calc
      residualReal data.selectedRealizationChain () x =
          continuumResidual data.selectedRealizationChain () x := by
            exact no_hidden_crime data.selectedRealizationChain
              data.selectedRealizationExact () x
      _ = data.selectedFieldLaw.operator x := by
            exact data.selectedContinuumResidual x
  refine ⟨data.selectedRealizationExact, ?_, data.selectedContinuumResidual, hreal, ?_, ?_⟩
  · intro x
    exact no_hidden_crime data.selectedRealizationChain
      data.selectedRealizationExact () x
  · intro x
    calc
      State.pair x (residualReal data.selectedRealizationChain () x) =
          State.pair x (data.selectedFieldLaw.operator x) := by
            rw [hreal x]
      _ = data.selectedQuadraticDensity x := by
            rfl
  · intro x
    calc
      data.selectedFieldLaw.residual x =
          SignedCount.ofNat (data.selectedQuadraticDensity x) := by
            exact data.selectedScalarDensitySurface.2.1 x
      _ =
          SignedCount.ofNat
            (State.pair x (data.selectedFieldLaw.operator x)) := by
            rw [data.selectedScalarDensitySurface.1 x]
      _ =
          SignedCount.ofNat
            (State.pair x (residualReal data.selectedRealizationChain () x)) := by
            rw [(hreal x).symm]

end ClosureCurrent

end CoherenceCalculus
