import CoherenceCalculus.Foundation.ClosureRealizationCore

/-!
# Foundation.ClosureDirectCore

Closure-realized Part I / Part II objects stated directly on the forced
four-grade closure state.

This layer does not add new mathematics. Its purpose is to remove as much
abstract wrapper language as possible from the realized calculus by restating
the key operators and HFT identities directly on `ClosureState`.
-/

namespace CoherenceCalculus

namespace ClosureState

/-- Extensionality for closure-realized states. -/
theorem ext {x y : ClosureState}
    (h0 : x.g0 = y.g0) (h1 : x.g1 = y.g1) (h2 : x.g2 = y.g2) (h3 : x.g3 = y.g3) :
    x = y := by
  cases x
  cases y
  cases h0
  cases h1
  cases h2
  cases h3
  rfl

/-- Pointwise closure-state addition. -/
def add (x y : ClosureState) : ClosureState :=
  ⟨SignedCount.addCount x.g0 y.g0,
   SignedCount.addCount x.g1 y.g1,
   SignedCount.addCount x.g2 y.g2,
   SignedCount.addCount x.g3 y.g3⟩

/-- Zero closure state. -/
def zero : ClosureState :=
  ⟨SignedCount.zero, SignedCount.zero, SignedCount.zero, SignedCount.zero⟩

/-- Pointwise closure-state subtraction. -/
def sub (x y : ClosureState) : ClosureState :=
  ⟨SignedCount.subCount x.g0 y.g0,
   SignedCount.subCount x.g1 y.g1,
   SignedCount.subCount x.g2 y.g2,
   SignedCount.subCount x.g3 y.g3⟩

/-- Pointwise closure-state negation. -/
def negate (x : ClosureState) : ClosureState :=
  ⟨SignedCount.negate x.g0,
   SignedCount.negate x.g1,
   SignedCount.negate x.g2,
   SignedCount.negate x.g3⟩

/-- Closure-state energy. -/
def energy (x : ClosureState) : Nat :=
  State.energy (stateFromClosureCoordinates x)

/-- Reading a rebuilt state as closure coordinates and repackaging it is exact. -/
theorem coordinates_round_trip (x : ClosureState) :
    closureCoordinates (stateFromClosureCoordinates x) = x := by
  cases x
  rfl

/-- The closure-realized state operations agree with the rebuilt state
operations. -/
theorem stateFromCoordinates_add (x y : ClosureState) :
    stateFromClosureCoordinates (add x y) =
      State.add (stateFromClosureCoordinates x) (stateFromClosureCoordinates y) := by
  apply State.ext <;> rfl

theorem stateFromCoordinates_zero :
    stateFromClosureCoordinates zero = State.zero := by
  rfl

theorem stateFromCoordinates_sub (x y : ClosureState) :
    stateFromClosureCoordinates (sub x y) =
      State.sub (stateFromClosureCoordinates x) (stateFromClosureCoordinates y) := by
  apply State.ext <;> rfl

theorem stateFromCoordinates_negate (x : ClosureState) :
    stateFromClosureCoordinates (negate x) =
      State.negate (stateFromClosureCoordinates x) := by
  apply State.ext <;> rfl

end ClosureState

/-- Closure-realized projection acting directly on closure states. -/
def closureProjectionState (h : Nat) (x : ClosureState) : ClosureState :=
  ⟨keepBelow (decide (0 < h)) x.g0,
   keepBelow (decide (1 < h)) x.g1,
   keepBelow (decide (2 < h)) x.g2,
   keepBelow (decide (3 < h)) x.g3⟩

/-- Closure-realized shadow acting directly on closure states. -/
def closureShadowState (h : Nat) (x : ClosureState) : ClosureState :=
  ClosureState.sub x (closureProjectionState h x)

/-- Closure-realized full boundary acting directly on closure states. -/
def closureBoundaryState (x : ClosureState) : ClosureState :=
  ⟨x.g1, SignedCount.zero, x.g3, SignedCount.zero⟩

/-- Closure-realized observed boundary. -/
def closureObservedBoundaryState (h : Nat) (x : ClosureState) : ClosureState :=
  closureProjectionState h (closureBoundaryState (closureProjectionState h x))

/-- Closure-realized leakage operator. -/
def closureLeakageState (h : Nat) (x : ClosureState) : ClosureState :=
  closureShadowState h (closureBoundaryState (closureProjectionState h x))

/-- Closure-realized return operator. -/
def closureReturnState (h : Nat) (x : ClosureState) : ClosureState :=
  closureProjectionState h (closureBoundaryState (closureShadowState h x))

/-- Closure-realized defect operator. -/
def closureDefectState (h : Nat) (x : ClosureState) : ClosureState :=
  closureReturnState h (closureLeakageState h x)

/-- Direct realization lemmas to and from the rebuilt state layer. -/
theorem stateFromCoordinates_projection (h : Nat) (x : ClosureState) :
    stateFromClosureCoordinates (closureProjectionState h x) =
      closureProjectionFromCounting h (stateFromClosureCoordinates x) := by
  apply State.ext <;> rfl

theorem stateFromCoordinates_shadow (h : Nat) (x : ClosureState) :
    stateFromClosureCoordinates (closureShadowState h x) =
      shadowProj closureTower h (stateFromClosureCoordinates x) := by
  rw [closureShadowState, ClosureState.stateFromCoordinates_sub, stateFromCoordinates_projection]
  rfl

theorem stateFromCoordinates_boundary (x : ClosureState) :
    stateFromClosureCoordinates (closureBoundaryState x) =
      closureBoundaryFromCounting (stateFromClosureCoordinates x) := by
  apply State.ext <;> rfl

theorem stateFromCoordinates_observedBoundary (h : Nat) (x : ClosureState) :
    stateFromClosureCoordinates (closureObservedBoundaryState h x) =
      observedBoundary closureTower h (stateFromClosureCoordinates x) := by
  rw [closureObservedBoundaryState, stateFromCoordinates_projection, stateFromCoordinates_boundary,
    stateFromCoordinates_projection]
  rfl

theorem stateFromCoordinates_leakage (h : Nat) (x : ClosureState) :
    stateFromClosureCoordinates (closureLeakageState h x) =
      boundaryLeakage closureTower h (stateFromClosureCoordinates x) := by
  rw [closureLeakageState, stateFromCoordinates_shadow, stateFromCoordinates_boundary,
    stateFromCoordinates_projection]
  rfl

theorem stateFromCoordinates_return (h : Nat) (x : ClosureState) :
    stateFromClosureCoordinates (closureReturnState h x) =
      boundaryReturn closureTower h (stateFromClosureCoordinates x) := by
  rw [closureReturnState, stateFromCoordinates_projection, stateFromCoordinates_boundary,
    stateFromCoordinates_shadow]
  rfl

theorem stateFromCoordinates_defect (h : Nat) (x : ClosureState) :
    stateFromClosureCoordinates (closureDefectState h x) =
      boundaryDefect closureTower h (stateFromClosureCoordinates x) := by
  rw [closureDefectState, closureReturnState, closureLeakageState]
  rw [stateFromCoordinates_projection, stateFromCoordinates_boundary, stateFromCoordinates_shadow]
  rfl

/-- The closure-realized full boundary closes on itself directly on
`ClosureState`. -/
theorem closureBoundaryState_square_zero (x : ClosureState) :
    closureBoundaryState (closureBoundaryState x) = ClosureState.zero := by
  apply ClosureState.ext <;> rfl

/-- The closure-realized tower becomes exact after the stable dimension becomes
fully visible. -/
theorem closureProjectionState_after_stable_dimension (h : Nat) (x : ClosureState) :
    closureProjectionState (h + closureStableDimension) x = x := by
  have h0 : decide (0 < h + closureStableDimension) = true := by
    apply decide_eq_true
    show 0 < Nat.succ (Nat.succ (Nat.succ (Nat.succ h)))
    exact Nat.zero_lt_succ _
  have h1 : decide (1 < h + closureStableDimension) = true := by
    apply decide_eq_true
    show Nat.succ 0 < Nat.succ (Nat.succ (Nat.succ (Nat.succ h)))
    exact Nat.succ_lt_succ (Nat.zero_lt_succ _)
  have h2 : decide (2 < h + closureStableDimension) = true := by
    apply decide_eq_true
    show Nat.succ (Nat.succ 0) < Nat.succ (Nat.succ (Nat.succ (Nat.succ h)))
    exact Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))
  have h3 : decide (3 < h + closureStableDimension) = true := by
    apply decide_eq_true
    show Nat.succ (Nat.succ (Nat.succ 0)) < Nat.succ (Nat.succ (Nat.succ (Nat.succ h)))
    exact Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _)))
  apply ClosureState.ext
  · rw [closureProjectionState, h0, keepBelow]
    rfl
  · rw [closureProjectionState, h1, keepBelow]
    rfl
  · rw [closureProjectionState, h2, keepBelow]
    rfl
  · rw [closureProjectionState, h3, keepBelow]
    rfl

/-- The closure-realized shadow vanishes after the stable dimension is fully
visible. -/
theorem closureShadowState_after_stable_dimension (h : Nat) (x : ClosureState) :
    closureShadowState (h + closureStableDimension) x = ClosureState.zero := by
  rw [closureShadowState, closureProjectionState_after_stable_dimension]
  apply ClosureState.ext
  · exact SignedCount.subCount_self x.g0
  · exact SignedCount.subCount_self x.g1
  · exact SignedCount.subCount_self x.g2
  · exact SignedCount.subCount_self x.g3

/-- Direct closure-state form of HFT-1. -/
theorem closureObservedBoundaryState_square_eq_neg_defect (h : Nat) (x : ClosureState) :
    closureObservedBoundaryState h (closureObservedBoundaryState h x) =
      ClosureState.negate (closureDefectState h x) := by
  apply ClosureState.ext
  · have hstate := congrArg State.c0
      (HFT1_closure_exact h (stateFromClosureCoordinates x))
    simpa [stateFromCoordinates_observedBoundary, stateFromCoordinates_defect,
      ClosureState.stateFromCoordinates_negate] using hstate
  · have hstate := congrArg State.c1
      (HFT1_closure_exact h (stateFromClosureCoordinates x))
    simpa [stateFromCoordinates_observedBoundary, stateFromCoordinates_defect,
      ClosureState.stateFromCoordinates_negate] using hstate
  · have hstate := congrArg State.c2
      (HFT1_closure_exact h (stateFromClosureCoordinates x))
    simpa [stateFromCoordinates_observedBoundary, stateFromCoordinates_defect,
      ClosureState.stateFromCoordinates_negate] using hstate
  · have hstate := congrArg State.c3
      (HFT1_closure_exact h (stateFromClosureCoordinates x))
    simpa [stateFromCoordinates_observedBoundary, stateFromCoordinates_defect,
      ClosureState.stateFromCoordinates_negate] using hstate

/-- Closure-state form of the finite HFT-2 identity. -/
theorem closureHFT2_state_finite
    (x : ClosureState) (h₀ : Nat) (hs : List Nat) (hmono : HorizonChain h₀ hs) :
    ClosureState.energy (closureShadowState h₀ x) =
      telescopingEnergyChain closureEnergyTower (stateFromClosureCoordinates x) h₀ hs := by
  simpa [ClosureState.energy, stateFromCoordinates_shadow] using
    HFT2_closure_finite (stateFromClosureCoordinates x) h₀ hs hmono

/-- Closure-state form of the faithful HFT-2 identity. -/
theorem closureHFT2_state_stabilized
    (x : ClosureState) (h₀ : Nat) :
    ∃ N, ∀ k,
      ClosureState.energy (closureShadowState h₀ x) =
        prefixIncrementEnergy closureEnergyTower (stateFromClosureCoordinates x) h₀ (N + k) := by
  obtain ⟨N, hN⟩ := HFT2_closure_stabilized (stateFromClosureCoordinates x) h₀
  refine ⟨N, ?_⟩
  intro k
  simpa [ClosureState.energy, stateFromCoordinates_shadow] using hN k

end CoherenceCalculus
