import CoherenceCalculus.PartIII.ClassicalLimitCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumFlagshipRealizationCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumDerivativeRealizationCore

Derivative-subsampling contract for any later stronger flagship realization.

`ClosureCurrentContinuumFlagshipRealizationCore` fixes the public law data of
any later stronger flagship form: velocity, scalar density, scalar residual,
and solution set. Part III already contains an exact minimal language for a
classical derivative presentation: a stagewise projection family, one
derivative field, one observed restriction family, and one defect family.

This file adds the next honest boundary theorem. Any later stronger flagship
realization that claims a Part III-style classical derivative-subsampling
presentation is already forced to use the same selected projection, the same
selected generator as derivative, the same observed restriction, the same
vanishing defect, and the same common zero set.

This is still not the final spatial differential PDE. It is the exact
derivative-subsampling contract that any such later PDE-like realization must
satisfy.
-/

namespace ClosureCurrent

/-- Minimal Part III-style classical derivative-subsampling realization of a
later stronger flagship language. It extends the public flagship realization by
one concrete derivative-subsampling package and requires that package to be the
selected projection/readout of the same flagship velocity field. -/
structure DerivativeSubsamplingFlagshipRealization
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) where
  flagship : FlagshipRealization data
  derivativeDatum : ClassicalDerivativeSubsamplingExample State
  exact_projection :
    ∀ n : Nat, ∀ x : State,
      derivativeDatum.projection n x =
        data.framed.object.bridge.selectedBridge.observer.selection.selectedProjection x
  exact_derivative :
    ∀ x : State, derivativeDatum.derivative x = flagship.velocity x
  exact_restriction :
    ∀ n : Nat, ∀ x : State,
      derivativeDatum.restriction n x =
        data.framed.object.bridge.selectedBridge.observer.selection.selectedProjection
          (flagship.velocity x)
  exact_defect :
    ∀ n : Nat, ∀ x : State, derivativeDatum.defect n x = State.zero

/-- The canonical derivative-subsampling realization already carried by the
detached selected cut. -/
def LocalEventFourStateLaw.selectedDerivativeSubsamplingFlagshipRealization
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    DerivativeSubsamplingFlagshipRealization data := by
  let selection := data.framed.object.bridge.selectedBridge.observer.selection
  refine
    { flagship := data.selectedFlagshipRealization
      derivativeDatum :=
        { projection := fun _ => selection.selectedProjection
          derivative := data.selectedFlagshipRealization.velocity
          restriction := fun _ x => selection.selectedProjection (data.selectedFlagshipRealization.velocity x)
          observed := fun _ x => selection.selectedProjection (data.selectedFlagshipRealization.velocity x)
          observed_eq_restriction := by
            intro _ x
            rfl
          defect := fun _ _ => State.zero }
      exact_projection := ?_
      exact_derivative := ?_
      exact_restriction := ?_
      exact_defect := ?_ }
  · intro _ x
    rfl
  · intro x
    rfl
  · intro _ x
    rfl
  · intro _ x
    rfl

/-- Derivative-subsampling realizations already use the same velocity as the
selected flagship law. -/
theorem DerivativeSubsamplingFlagshipRealization.velocity_iff_selectedGenerator
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : DerivativeSubsamplingFlagshipRealization data) :
    ∀ x : State,
      realization.flagship.velocity x = data.selectedAutonomousScalarLaw.generator x :=
  realization.flagship.velocity_iff_selectedGenerator

/-- Derivative-subsampling realizations already use the selected cut
projection. -/
theorem DerivativeSubsamplingFlagshipRealization.projection_iff_selectedProjection
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : DerivativeSubsamplingFlagshipRealization data) :
    ∀ n : Nat, ∀ x : State,
      realization.derivativeDatum.projection n x =
        data.framed.object.bridge.selectedBridge.observer.selection.selectedProjection x :=
  realization.exact_projection

/-- Derivative-subsampling realizations already use the selected generator as
their derivative field. -/
theorem DerivativeSubsamplingFlagshipRealization.derivative_iff_selectedGenerator
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : DerivativeSubsamplingFlagshipRealization data) :
    ∀ x : State,
      realization.derivativeDatum.derivative x =
        data.selectedAutonomousScalarLaw.generator x := by
  intro x
  calc
    realization.derivativeDatum.derivative x = realization.flagship.velocity x := by
      exact realization.exact_derivative x
    _ = data.selectedAutonomousScalarLaw.generator x := by
      exact realization.velocity_iff_selectedGenerator x

/-- Derivative-subsampling realizations already use the selected observed
restriction of the selected generator. -/
theorem DerivativeSubsamplingFlagshipRealization.restriction_iff_selectedGenerator
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : DerivativeSubsamplingFlagshipRealization data) :
    ∀ n : Nat, ∀ x : State,
      realization.derivativeDatum.restriction n x =
        data.framed.object.bridge.selectedBridge.observer.selection.selectedProjection
          (data.selectedAutonomousScalarLaw.generator x) := by
  intro n x
  calc
    realization.derivativeDatum.restriction n x =
        data.framed.object.bridge.selectedBridge.observer.selection.selectedProjection
          (realization.flagship.velocity x) := by
            exact realization.exact_restriction n x
    _ =
        data.framed.object.bridge.selectedBridge.observer.selection.selectedProjection
          (data.selectedAutonomousScalarLaw.generator x) := by
            rw [realization.velocity_iff_selectedGenerator x]

/-- Derivative-subsampling realizations already have the same observed family
as the selected observed restriction of the selected generator. -/
theorem DerivativeSubsamplingFlagshipRealization.observed_iff_selectedGenerator
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : DerivativeSubsamplingFlagshipRealization data) :
    ∀ n : Nat, ∀ x : State,
      realization.derivativeDatum.observed n x =
        data.framed.object.bridge.selectedBridge.observer.selection.selectedProjection
          (data.selectedAutonomousScalarLaw.generator x) := by
  intro n x
  calc
    realization.derivativeDatum.observed n x =
        realization.derivativeDatum.restriction n x := by
          exact realization.derivativeDatum.observed_eq_restriction n x
    _ =
        data.framed.object.bridge.selectedBridge.observer.selection.selectedProjection
          (data.selectedAutonomousScalarLaw.generator x) := by
            exact realization.restriction_iff_selectedGenerator n x

/-- Derivative-subsampling realizations already have vanishing defect on the
selected cut. -/
theorem DerivativeSubsamplingFlagshipRealization.defect_iff_zero
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : DerivativeSubsamplingFlagshipRealization data) :
    ∀ n : Nat, ∀ x : State,
      realization.derivativeDatum.defect n x = State.zero :=
  realization.exact_defect

/-- Derivative-subsampling realizations already have the same solution set as
the autonomous scalar law. -/
theorem DerivativeSubsamplingFlagshipRealization.solution_iff_selectedAutonomousScalarLaw
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : DerivativeSubsamplingFlagshipRealization data) :
    ∀ x : State,
      realization.flagship.solution x ↔ data.selectedAutonomousScalarLaw.solution x :=
  realization.flagship.solution_iff_selectedAutonomousScalarLaw

/-- Manuscript-facing derivative-subsampling contract surface for any later
stronger flagship realization. -/
def SelectedDerivativeSubsamplingFlagshipSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  Nonempty (DerivativeSubsamplingFlagshipRealization data) ∧
    (∀ realization : DerivativeSubsamplingFlagshipRealization data,
      ∀ n : Nat, ∀ x : State,
        realization.derivativeDatum.projection n x =
          data.framed.object.bridge.selectedBridge.observer.selection.selectedProjection x) ∧
    (∀ realization : DerivativeSubsamplingFlagshipRealization data,
      ∀ x : State,
        realization.derivativeDatum.derivative x =
          data.selectedAutonomousScalarLaw.generator x) ∧
    (∀ realization : DerivativeSubsamplingFlagshipRealization data,
      ∀ n : Nat, ∀ x : State,
        realization.derivativeDatum.restriction n x =
          data.framed.object.bridge.selectedBridge.observer.selection.selectedProjection
            (data.selectedAutonomousScalarLaw.generator x)) ∧
    (∀ realization : DerivativeSubsamplingFlagshipRealization data,
      ∀ n : Nat, ∀ x : State,
        realization.derivativeDatum.observed n x =
          data.framed.object.bridge.selectedBridge.observer.selection.selectedProjection
            (data.selectedAutonomousScalarLaw.generator x)) ∧
    (∀ realization : DerivativeSubsamplingFlagshipRealization data,
      ∀ n : Nat, ∀ x : State,
        realization.derivativeDatum.defect n x = State.zero) ∧
    (∀ realization : DerivativeSubsamplingFlagshipRealization data,
      ∀ x : State,
        realization.flagship.solution x ↔ data.selectedAutonomousScalarLaw.solution x) ∧
    (∀ realization : DerivativeSubsamplingFlagshipRealization data,
      ∀ x : State,
        realization.flagship.solution x ↔ data.scalarPDERealization.solution x) ∧
    (∀ realization : DerivativeSubsamplingFlagshipRealization data,
      ∀ x : State,
        realization.flagship.solution x ↔ data.scalarActionRealization.stationary x) ∧
    (∀ realization : DerivativeSubsamplingFlagshipRealization data,
      ∀ x : State,
        realization.flagship.solution x ↔ data.selectedEvolutionLaw.solution x)

/-- Any later stronger flagship realization that claims a Part III-style
classical derivative-subsampling presentation is already forced to agree with
the selected cut on the projection, derivative, observed restriction, vanishing
defect, and the common zero set. -/
theorem LocalEventFourStateLaw.selectedDerivativeSubsamplingFlagshipSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedDerivativeSubsamplingFlagshipSurface data := by
  refine
    ⟨⟨data.selectedDerivativeSubsamplingFlagshipRealization⟩, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
  · intro realization n x
    exact realization.projection_iff_selectedProjection n x
  · intro realization x
    exact realization.derivative_iff_selectedGenerator x
  · intro realization n x
    exact realization.restriction_iff_selectedGenerator n x
  · intro realization n x
    exact realization.observed_iff_selectedGenerator n x
  · intro realization n x
    exact realization.defect_iff_zero n x
  · intro realization x
    exact realization.solution_iff_selectedAutonomousScalarLaw x
  · intro realization x
    exact realization.flagship.solution_iff_pdeSolution x
  · intro realization x
    exact realization.flagship.solution_iff_actionStationary x
  · intro realization x
    exact realization.flagship.solution_iff_evolutionSolution x

end ClosureCurrent

end CoherenceCalculus
