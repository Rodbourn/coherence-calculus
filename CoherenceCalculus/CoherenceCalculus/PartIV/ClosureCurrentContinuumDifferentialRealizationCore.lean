import CoherenceCalculus.PartIV.ClosureCurrentContinuumFlagshipRealizationCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumFlowCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumDifferentialRealizationCore

Differential-flow contract for any later stronger flagship realization.

`ClosureCurrentContinuumFlagshipRealizationCore` fixes the public law data of
any later stronger flagship form: velocity, scalar density, scalar residual,
and solution set. `ClosureCurrentContinuumFlowCore` already supplies the exact
Part III-style continuous block-derivative and effective-flow package carried
by the detached selected cut.

This file combines those two surfaces at the next honest boundary. Any later
stronger flagship realization that claims a differential-flow presentation in
that same Part III language is already forced to agree with the selected cut
on the operator, the `PP/PQ/QP/QQ` blocks, the effective flow, and the common
solution set.

This is still not the final spatial differential PDE. It is the exact
differential-flow contract that any such later PDE-like realization must
satisfy.
-/

namespace ClosureCurrent

/-- Minimal Part III-style differential-flow realization of a later stronger
flagship language. It extends the public flagship realization by one concrete
continuous block-derivative package and one concrete effective-flow package,
and requires that both are presentations of the same flagship velocity field. -/
structure DifferentialFlagshipRealization
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) where
  flagship : FlagshipRealization data
  blockDatum : ContinuousBlockDerivativeDatum Nat State
  flowDatum : ContinuousEffectiveFlowData Nat State
  flow_uses_blockDatum : flowDatum.blockData = blockDatum
  exact_operator : ∀ x : State, blockDatum.operator x = flagship.velocity x
  exact_blockPP : ∀ n : Nat, ∀ x : State, blockDatum.blockPP n x = flagship.velocity x
  exact_blockPQ : ∀ n : Nat, ∀ x : State, blockDatum.blockPQ n x = State.zero
  exact_blockQP : ∀ n : Nat, ∀ x : State, blockDatum.blockQP n x = State.zero
  exact_blockQQ : ∀ n : Nat, ∀ x : State, blockDatum.blockQQ n x = State.zero
  exact_flow : ∀ n : Nat, ∀ x : State, flowDatum.effectiveOp n x = flagship.velocity x

/-- The canonical differential-flow realization already carried by the detached
selected cut. -/
def LocalEventFourStateLaw.selectedDifferentialFlagshipRealization
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    DifferentialFlagshipRealization data where
  flagship := data.selectedFlagshipRealization
  blockDatum := data.selectedContinuousBlockDerivativeDatum
  flowDatum := data.selectedContinuousEffectiveFlowData
  flow_uses_blockDatum := rfl
  exact_operator := by
    obtain
      ⟨_hadm, _hpsd, _heq, _hmin, _hmineq, _hstateForm, hgenerator⟩ :=
      data.minimalQuadraticRepresentativeSurface
    intro x
    calc
      data.selectedContinuousBlockDerivativeDatum.operator x =
          data.framed.object.bridge.generator.toFun x := by
            exact hgenerator x
      _ = data.selectedFlagshipRealization.velocity x := by
            rfl
  exact_blockPP := data.selectedContinuousBlockDerivativeDatum_PP
  exact_blockPQ := data.selectedContinuousBlockDerivativeDatum_PQ
  exact_blockQP := data.selectedContinuousBlockDerivativeDatum_QP
  exact_blockQQ := data.selectedContinuousBlockDerivativeDatum_QQ
  exact_flow := by
    have hfirst :
        SelectedFirstOrderLawSurface data := data.selectedFirstOrderLawSurface
    obtain
      ⟨_hforced, _hscalar, _hflow, hflowOp, _hflowScalar, _hequation, _hpde,
        _haction⟩ :=
      hfirst
    intro n x
    calc
      data.selectedContinuousEffectiveFlowData.effectiveOp n x =
          data.selectedFieldLaw.operator x := by
            exact hflowOp n x
      _ = data.selectedFlagshipRealization.velocity x := by
            rfl

/-- Differential-flow realizations already have the same velocity as the
selected flagship law. -/
theorem DifferentialFlagshipRealization.velocity_iff_selectedGenerator
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : DifferentialFlagshipRealization data) :
    ∀ x : State,
      realization.flagship.velocity x = data.selectedAutonomousScalarLaw.generator x :=
  realization.flagship.velocity_iff_selectedGenerator

/-- Differential-flow realizations already have the same block operator as the
selected differential-flow package. -/
theorem DifferentialFlagshipRealization.operator_iff_selectedBlockOperator
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : DifferentialFlagshipRealization data) :
    ∀ x : State,
      realization.blockDatum.operator x =
        data.selectedContinuousBlockDerivativeDatum.operator x := by
  obtain
    ⟨_hadm, _hpsd, _heq, _hmin, _hmineq, _hstateForm, hgenerator⟩ :=
    data.minimalQuadraticRepresentativeSurface
  intro x
  calc
    realization.blockDatum.operator x = realization.flagship.velocity x := by
      exact realization.exact_operator x
    _ = data.selectedAutonomousScalarLaw.generator x := by
      exact realization.velocity_iff_selectedGenerator x
    _ = data.framed.object.bridge.generator.toFun x := by
      rfl
    _ = data.selectedContinuousBlockDerivativeDatum.operator x := by
      symm
      exact hgenerator x

/-- Differential-flow realizations already have the same `PP` block as the
selected differential-flow package. -/
theorem DifferentialFlagshipRealization.blockPP_iff_selectedBlockPP
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : DifferentialFlagshipRealization data) :
    ∀ n : Nat, ∀ x : State,
      realization.blockDatum.blockPP n x =
        data.selectedContinuousBlockDerivativeDatum.blockPP n x := by
  intro n x
  calc
    realization.blockDatum.blockPP n x = realization.flagship.velocity x := by
      exact realization.exact_blockPP n x
    _ = data.selectedAutonomousScalarLaw.generator x := by
      exact realization.velocity_iff_selectedGenerator x
    _ = data.selectedContinuousBlockDerivativeDatum.blockPP n x := by
      symm
      exact data.selectedContinuousBlockDerivativeDatum_PP n x

/-- Differential-flow realizations already have the same `PQ` block as the
selected differential-flow package. -/
theorem DifferentialFlagshipRealization.blockPQ_iff_selectedBlockPQ
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : DifferentialFlagshipRealization data) :
    ∀ n : Nat, ∀ x : State,
      realization.blockDatum.blockPQ n x =
        data.selectedContinuousBlockDerivativeDatum.blockPQ n x := by
  intro n x
  calc
    realization.blockDatum.blockPQ n x = State.zero := by
      exact realization.exact_blockPQ n x
    _ = data.selectedContinuousBlockDerivativeDatum.blockPQ n x := by
      symm
      exact data.selectedContinuousBlockDerivativeDatum_PQ n x

/-- Differential-flow realizations already have the same `QP` block as the
selected differential-flow package. -/
theorem DifferentialFlagshipRealization.blockQP_iff_selectedBlockQP
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : DifferentialFlagshipRealization data) :
    ∀ n : Nat, ∀ x : State,
      realization.blockDatum.blockQP n x =
        data.selectedContinuousBlockDerivativeDatum.blockQP n x := by
  intro n x
  calc
    realization.blockDatum.blockQP n x = State.zero := by
      exact realization.exact_blockQP n x
    _ = data.selectedContinuousBlockDerivativeDatum.blockQP n x := by
      symm
      exact data.selectedContinuousBlockDerivativeDatum_QP n x

/-- Differential-flow realizations already have the same `QQ` block as the
selected differential-flow package. -/
theorem DifferentialFlagshipRealization.blockQQ_iff_selectedBlockQQ
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : DifferentialFlagshipRealization data) :
    ∀ n : Nat, ∀ x : State,
      realization.blockDatum.blockQQ n x =
        data.selectedContinuousBlockDerivativeDatum.blockQQ n x := by
  intro n x
  calc
    realization.blockDatum.blockQQ n x = State.zero := by
      exact realization.exact_blockQQ n x
    _ = data.selectedContinuousBlockDerivativeDatum.blockQQ n x := by
      symm
      exact data.selectedContinuousBlockDerivativeDatum_QQ n x

/-- Differential-flow realizations already have the same effective flow as the
selected differential-flow package. -/
theorem DifferentialFlagshipRealization.flow_iff_selectedEffectiveFlow
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : DifferentialFlagshipRealization data) :
    ∀ n : Nat, ∀ x : State,
      realization.flowDatum.effectiveOp n x =
        data.selectedContinuousEffectiveFlowData.effectiveOp n x := by
  have hfirst :
      SelectedFirstOrderLawSurface data := data.selectedFirstOrderLawSurface
  obtain
    ⟨_hforced, _hscalar, _hflow, hflowOp, _hflowScalar, _hequation, _hpde,
      _haction⟩ :=
    hfirst
  intro n x
  calc
    realization.flowDatum.effectiveOp n x = realization.flagship.velocity x := by
      exact realization.exact_flow n x
    _ = data.selectedAutonomousScalarLaw.generator x := by
      exact realization.velocity_iff_selectedGenerator x
    _ = data.selectedFieldLaw.operator x := by
      rfl
    _ = data.selectedContinuousEffectiveFlowData.effectiveOp n x := by
      symm
      exact hflowOp n x

/-- Differential-flow realizations already have the same solution set as the
selected flagship contract. -/
theorem DifferentialFlagshipRealization.solution_iff_selectedAutonomousScalarLaw
    {Index Time Carrier Law : Type}
    {data : LocalEventFourStateLaw Index Time Carrier Law}
    (realization : DifferentialFlagshipRealization data) :
    ∀ x : State,
      realization.flagship.solution x ↔ data.selectedAutonomousScalarLaw.solution x :=
  realization.flagship.solution_iff_selectedAutonomousScalarLaw

/-- Manuscript-facing differential-flow contract surface for any later stronger
flagship realization. -/
def SelectedDifferentialFlagshipRealizationSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  Nonempty (DifferentialFlagshipRealization data) ∧
    (∀ realization : DifferentialFlagshipRealization data,
      ∀ x : State,
        realization.flagship.velocity x = data.selectedAutonomousScalarLaw.generator x) ∧
    (∀ realization : DifferentialFlagshipRealization data,
      ∀ x : State,
        realization.blockDatum.operator x =
          data.selectedContinuousBlockDerivativeDatum.operator x) ∧
    (∀ realization : DifferentialFlagshipRealization data,
      ∀ n : Nat, ∀ x : State,
        realization.blockDatum.blockPP n x =
          data.selectedContinuousBlockDerivativeDatum.blockPP n x) ∧
    (∀ realization : DifferentialFlagshipRealization data,
      ∀ n : Nat, ∀ x : State,
        realization.blockDatum.blockPQ n x =
          data.selectedContinuousBlockDerivativeDatum.blockPQ n x) ∧
    (∀ realization : DifferentialFlagshipRealization data,
      ∀ n : Nat, ∀ x : State,
        realization.blockDatum.blockQP n x =
          data.selectedContinuousBlockDerivativeDatum.blockQP n x) ∧
    (∀ realization : DifferentialFlagshipRealization data,
      ∀ n : Nat, ∀ x : State,
        realization.blockDatum.blockQQ n x =
          data.selectedContinuousBlockDerivativeDatum.blockQQ n x) ∧
    (∀ realization : DifferentialFlagshipRealization data,
      ∀ n : Nat, ∀ x : State,
        realization.flowDatum.effectiveOp n x =
          data.selectedContinuousEffectiveFlowData.effectiveOp n x) ∧
    (∀ realization : DifferentialFlagshipRealization data,
      ∀ x : State,
        realization.flagship.solution x ↔ data.selectedAutonomousScalarLaw.solution x) ∧
    (∀ realization : DifferentialFlagshipRealization data,
      ∀ x : State,
        realization.flagship.solution x ↔ data.scalarPDERealization.solution x) ∧
    (∀ realization : DifferentialFlagshipRealization data,
      ∀ x : State,
        realization.flagship.solution x ↔ data.scalarActionRealization.stationary x) ∧
    (∀ realization : DifferentialFlagshipRealization data,
      ∀ x : State,
        realization.flagship.solution x ↔ data.selectedEvolutionLaw.solution x)

/-- Any later stronger flagship realization that claims a Part III-style
differential-flow presentation is already forced to agree with the selected
cut on the operator, the `PP/PQ/QP/QQ` blocks, the effective flow, and the
common solution set. -/
theorem LocalEventFourStateLaw.selectedDifferentialFlagshipRealizationSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedDifferentialFlagshipRealizationSurface data := by
  refine
    ⟨⟨data.selectedDifferentialFlagshipRealization⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
  · intro realization x
    exact realization.velocity_iff_selectedGenerator x
  · intro realization x
    exact realization.operator_iff_selectedBlockOperator x
  · intro realization n x
    exact realization.blockPP_iff_selectedBlockPP n x
  · intro realization n x
    exact realization.blockPQ_iff_selectedBlockPQ n x
  · intro realization n x
    exact realization.blockQP_iff_selectedBlockQP n x
  · intro realization n x
    exact realization.blockQQ_iff_selectedBlockQQ n x
  · intro realization n x
    exact realization.flow_iff_selectedEffectiveFlow n x
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
