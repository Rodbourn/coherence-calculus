import CoherenceCalculus.Foundation.ClosureDirectCore

/-!
# Foundation.ClosureTransportCore

Transport of the rebuilt state/operator language from the closure-forced
four-grade realization.

This module pushes the forcing story one step further. The abstract `State`
layer used by the rebuilt theorem envelope is shown to be an explicit transport
of `ClosureState`, rather than an independent modeling choice.
-/

namespace CoherenceCalculus

/-- Explicit transport between the closure-forced state and the rebuilt state
wrapper. -/
structure ClosureStateTransport where
  toState : ClosureState → State
  toClosure : State → ClosureState
  left_inv : ∀ x : ClosureState, toClosure (toState x) = x
  right_inv : ∀ x : State, toState (toClosure x) = x

/-- The rebuilt `State` layer is exactly the closure-state transport. -/
def closureStateTransport : ClosureStateTransport where
  toState := stateFromClosureCoordinates
  toClosure := closureCoordinates
  left_inv := ClosureState.coordinates_round_trip
  right_inv := state_from_closureCoordinates

/-- Transport preserves closure-state addition. -/
theorem closureStateTransport_add (x y : ClosureState) :
    closureStateTransport.toState (ClosureState.add x y) =
      State.add (closureStateTransport.toState x) (closureStateTransport.toState y) := by
  exact ClosureState.stateFromCoordinates_add x y

/-- Transport preserves the zero state. -/
theorem closureStateTransport_zero :
    closureStateTransport.toState ClosureState.zero = State.zero := by
  exact ClosureState.stateFromCoordinates_zero

/-- Transport preserves closure-state subtraction. -/
theorem closureStateTransport_sub (x y : ClosureState) :
    closureStateTransport.toState (ClosureState.sub x y) =
      State.sub (closureStateTransport.toState x) (closureStateTransport.toState y) := by
  exact ClosureState.stateFromCoordinates_sub x y

/-- Transport preserves closure-state negation. -/
theorem closureStateTransport_negate (x : ClosureState) :
    closureStateTransport.toState (ClosureState.negate x) =
      State.negate (closureStateTransport.toState x) := by
  exact ClosureState.stateFromCoordinates_negate x

/-- Transport preserves the closure-state energy. -/
theorem closureStateTransport_energy (x : ClosureState) :
    ClosureState.energy x = State.energy (closureStateTransport.toState x) := by
  rfl

/-- Transport carries the closure-state horizon cut to the rebuilt projection. -/
theorem closureStateTransport_projection (h : Nat) (x : ClosureState) :
    closureStateTransport.toState (closureProjectionState h x) =
      (closureTower.π h).toFun (closureStateTransport.toState x) := by
  calc
    closureStateTransport.toState (closureProjectionState h x)
        = closureProjectionFromCounting h (closureStateTransport.toState x) := by
            exact stateFromCoordinates_projection h x
    _ = (closureTower.π h).toFun (closureStateTransport.toState x) := by
          rfl

/-- Transport carries the closure-state shadow to the rebuilt shadow operator. -/
theorem closureStateTransport_shadow (h : Nat) (x : ClosureState) :
    closureStateTransport.toState (closureShadowState h x) =
      shadowProj closureTower h (closureStateTransport.toState x) := by
  exact stateFromCoordinates_shadow h x

/-- Transport carries the closure-state full boundary to the rebuilt full
boundary. -/
theorem closureStateTransport_boundary (x : ClosureState) :
    closureStateTransport.toState (closureBoundaryState x) =
      trueBoundary (closureStateTransport.toState x) := by
  calc
    closureStateTransport.toState (closureBoundaryState x)
        = closureBoundaryFromCounting (closureStateTransport.toState x) := by
            exact stateFromCoordinates_boundary x
    _ = trueBoundary (closureStateTransport.toState x) := by
          exact closureBoundary_realizes_trueBoundary (closureStateTransport.toState x)

/-- Transport carries the closure-state observed boundary to the rebuilt
observed boundary. -/
theorem closureStateTransport_observedBoundary (h : Nat) (x : ClosureState) :
    closureStateTransport.toState (closureObservedBoundaryState h x) =
      observedBoundary closureTower h (closureStateTransport.toState x) := by
  exact stateFromCoordinates_observedBoundary h x

/-- Transport carries the closure-state leakage to the rebuilt leakage
operator. -/
theorem closureStateTransport_leakage (h : Nat) (x : ClosureState) :
    closureStateTransport.toState (closureLeakageState h x) =
      boundaryLeakage closureTower h (closureStateTransport.toState x) := by
  exact stateFromCoordinates_leakage h x

/-- Transport carries the closure-state return to the rebuilt return operator. -/
theorem closureStateTransport_return (h : Nat) (x : ClosureState) :
    closureStateTransport.toState (closureReturnState h x) =
      boundaryReturn closureTower h (closureStateTransport.toState x) := by
  exact stateFromCoordinates_return h x

/-- Transport carries the closure-state defect to the rebuilt defect
operator. -/
theorem closureStateTransport_defect (h : Nat) (x : ClosureState) :
    closureStateTransport.toState (closureDefectState h x) =
      boundaryDefect closureTower h (closureStateTransport.toState x) := by
  exact stateFromCoordinates_defect h x

/-- The rebuilt Part I / Part II state layer is an explicit transport of the
closure-forced realization, with no additional data. -/
theorem state_layer_is_closure_transport (x : ClosureState) :
    closureStateTransport.toClosure (closureStateTransport.toState x) = x := by
  exact closureStateTransport.left_inv x

end CoherenceCalculus
