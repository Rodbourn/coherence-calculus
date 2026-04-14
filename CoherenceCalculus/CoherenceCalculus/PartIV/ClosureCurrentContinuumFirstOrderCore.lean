import CoherenceCalculus.PartIV.ClosureCurrentContinuumScalarCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumFlowCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumFirstOrderCore

One canonical first-order law object on the detached selected cut.

`ClosureCurrentContinuumScalarCore` packages the current scalar flagship side as
one canonical scalar law object. `ClosureCurrentContinuumFlowCore` packages the
same selected governing operator as an exact Part III-style continuous
effective-flow datum.

This file closes the remaining gap between those two surfaces. The point is not
to claim a spatial differential PDE. The point is to show that the detached
selected cut already carries one canonical first-order law object:

* one uniquely forced selected operator;
* one exact continuous effective flow presenting that same operator;
* one scalar equation read directly from that same first-order operator.

So the current flagship law is already first-order before any stronger
differential realization is attempted.
-/

namespace ClosureCurrent

/-- The detached selected cut already carries one canonical first-order law
object. The uniquely forced selected operator, the exact continuous effective
flow, and the scalar flagship equation are all presentations of the same
first-order law on the selected carrier. -/
def SelectedFirstOrderLawSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) : Prop :=
  SelectedFieldLawForcingSurface data ∧
    SelectedScalarLawSurface data ∧
    SelectedGoverningFlowSurface data ∧
    (∀ n : Nat, ∀ x : State,
      data.selectedContinuousEffectiveFlowData.effectiveOp n x =
        data.selectedFieldLaw.operator x) ∧
    (∀ n : Nat, ∀ x : State,
      data.selectedFieldLaw.residual x =
        SignedCount.ofNat
          (State.pair x (data.selectedContinuousEffectiveFlowData.effectiveOp n x))) ∧
    (∀ n : Nat, ∀ x : State,
      data.selectedFieldEquation x ↔
        SignedCount.ofNat
            (State.pair x (data.selectedContinuousEffectiveFlowData.effectiveOp n x)) =
          SignedCount.zero) ∧
    (∀ n : Nat, ∀ x : State,
      data.scalarPDERealization.solution x ↔
        SignedCount.ofNat
            (State.pair x (data.selectedContinuousEffectiveFlowData.effectiveOp n x)) =
          SignedCount.zero) ∧
    (∀ n : Nat, ∀ x : State,
      data.scalarActionRealization.stationary x ↔
        SignedCount.ofNat
            (State.pair x (data.selectedContinuousEffectiveFlowData.effectiveOp n x)) =
          SignedCount.zero)

/-- The detached selected cut already carries one canonical first-order law
object. The exact selected flow is stagewise constant and equal to the unique
selected operator, while the selected equation and its current scalar PDE/action
realizations are exactly the zero set of the scalar readout of that flow. -/
theorem LocalEventFourStateLaw.selectedFirstOrderLawSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    SelectedFirstOrderLawSurface data := by
  have hforced :
      SelectedFieldLawForcingSurface data := by
    exact data.selectedFieldLawForcingSurface
  have hscalarLaw :
      SelectedScalarLawSurface data := by
    exact data.selectedScalarLawSurface
  have hflow :
      SelectedGoverningFlowSurface data := by
    exact data.selectedGoverningFlowSurface
  have hscalarLawSurface := hscalarLaw
  have hflowSurface := hflow
  obtain
    ⟨_hrealization, _hexistence, _hscalar, hdensity, _hledger, _hgoal,
      _hrealDensity, _hgoalDensity, _hpointwise, _hzeros⟩ :=
    hscalarLawSurface
  obtain
    ⟨hdensityOp, hresDensity, _hpdeDensity, _hactionDensity, _hpdeActionDensity⟩ :=
    hdensity
  obtain
    ⟨_hinterp, hPP, _hPQ, _hQP, _hQQ, _hflowC1, hflowFormula⟩ :=
    hflowSurface
  have hflowOp :
      ∀ n : Nat, ∀ x : State,
        data.selectedContinuousEffectiveFlowData.effectiveOp n x =
          data.selectedFieldLaw.operator x := by
    intro n x
    calc
      data.selectedContinuousEffectiveFlowData.effectiveOp n x =
          blockPP
            data.framed.object.bridge.selectedBridge.observer.selection.selectedProjection
            data.toMinimalQuadraticRepresentative.stateForm.op x := by
              exact hflowFormula n x
      _ = data.framed.object.bridge.generator.toFun x := by
            exact hPP n x
      _ = data.selectedFieldLaw.operator x := by
            rfl
  have hflowScalar :
      ∀ n : Nat, ∀ x : State,
        data.selectedFieldLaw.residual x =
          SignedCount.ofNat
            (State.pair x (data.selectedContinuousEffectiveFlowData.effectiveOp n x)) := by
    intro n x
    calc
      data.selectedFieldLaw.residual x =
          SignedCount.ofNat (data.selectedQuadraticDensity x) := by
            exact hresDensity x
      _ = SignedCount.ofNat (State.pair x (data.selectedFieldLaw.operator x)) := by
            rw [hdensityOp x]
      _ = SignedCount.ofNat
            (State.pair x (data.selectedContinuousEffectiveFlowData.effectiveOp n x)) := by
            rw [← hflowOp n x]
  have hequation :
      ∀ n : Nat, ∀ x : State,
        data.selectedFieldEquation x ↔
          SignedCount.ofNat
              (State.pair x (data.selectedContinuousEffectiveFlowData.effectiveOp n x)) =
            SignedCount.zero := by
    intro n x
    constructor
    · intro hx
      calc
        SignedCount.ofNat
            (State.pair x (data.selectedContinuousEffectiveFlowData.effectiveOp n x)) =
            data.selectedFieldLaw.residual x := by
              symm
              exact hflowScalar n x
        _ = SignedCount.zero := by
              simpa [LocalEventFourStateLaw.selectedFieldEquation] using hx
    · intro hx
      have hres :
          data.selectedFieldLaw.residual x = SignedCount.zero := by
        calc
          data.selectedFieldLaw.residual x =
              SignedCount.ofNat
                (State.pair x (data.selectedContinuousEffectiveFlowData.effectiveOp n x)) := by
                  exact hflowScalar n x
          _ = SignedCount.zero := hx
      simpa [LocalEventFourStateLaw.selectedFieldEquation] using hres
  have hpde :
      ∀ n : Nat, ∀ x : State,
        data.scalarPDERealization.solution x ↔
          SignedCount.ofNat
              (State.pair x (data.selectedContinuousEffectiveFlowData.effectiveOp n x)) =
            SignedCount.zero := by
    intro n x
    constructor
    · intro hx
      exact (hequation n x).1
        ((data.scalarPDERealization.solution_iff_selectedEquation x).1 hx)
    · intro hx
      exact (data.scalarPDERealization.solution_iff_selectedEquation x).2
        ((hequation n x).2 hx)
  have haction :
      ∀ n : Nat, ∀ x : State,
        data.scalarActionRealization.stationary x ↔
          SignedCount.ofNat
              (State.pair x (data.selectedContinuousEffectiveFlowData.effectiveOp n x)) =
            SignedCount.zero := by
    intro n x
    constructor
    · intro hx
      exact (hequation n x).1
        ((data.scalarActionRealization.stationary_iff_selectedEquation x).1 hx)
    · intro hx
      exact (data.scalarActionRealization.stationary_iff_selectedEquation x).2
        ((hequation n x).2 hx)
  exact ⟨hforced, hscalarLaw, hflow, hflowOp, hflowScalar, hequation, hpde, haction⟩

end ClosureCurrent

end CoherenceCalculus
