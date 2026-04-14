import CoherenceCalculus.Foundation.ClosureCore
import CoherenceCalculus.Foundation.SignedAlgebraCore

/-!
# Foundation.HorizonCore

Minimal horizon/operator core built above the rebuilt closure foundation.

This layer introduces only the compositional horizon machinery needed to restart
the calculus:
- states as concrete 4-coordinate signed-count records
- idempotent projections
- horizon towers
- shadow, observed, leakage, return, and defect endomaps

At this stage, operators are plain endomaps on states. Additive and scalar
structure can be rebuilt later once the signed-count algebra is proved at the
required level of rigor.
-/

namespace CoherenceCalculus

/-- State space at the stable dimension `D = 4`. -/
structure State where
  c0 : SignedCount
  c1 : SignedCount
  c2 : SignedCount
  c3 : SignedCount
  deriving DecidableEq, Repr

namespace State

/-- Pointwise signed-count addition of states. -/
def add (x y : State) : State :=
  ⟨SignedCount.addCount x.c0 y.c0,
   SignedCount.addCount x.c1 y.c1,
   SignedCount.addCount x.c2 y.c2,
   SignedCount.addCount x.c3 y.c3⟩

/-- Zero state. -/
def zero : State :=
  ⟨SignedCount.zero, SignedCount.zero, SignedCount.zero, SignedCount.zero⟩

/-- Pointwise signed-count subtraction of states. -/
def sub (x y : State) : State :=
  ⟨SignedCount.subCount x.c0 y.c0,
   SignedCount.subCount x.c1 y.c1,
   SignedCount.subCount x.c2 y.c2,
   SignedCount.subCount x.c3 y.c3⟩

/-- Pointwise signed-count negation of states. -/
def negate (x : State) : State :=
  ⟨SignedCount.negate x.c0,
   SignedCount.negate x.c1,
   SignedCount.negate x.c2,
   SignedCount.negate x.c3⟩

/-- Extensionality for states. -/
theorem ext {x y : State}
    (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1) (h2 : x.c2 = y.c2) (h3 : x.c3 = y.c3) :
    x = y := by
  cases x
  cases y
  cases h0
  cases h1
  cases h2
  cases h3
  rfl

/-- Zero is a right identity for state addition. -/
theorem add_zero (x : State) : add x zero = x := by
  apply ext <;> exact SignedCount.addCount_zero _

/-- Zero is a left identity for state addition. -/
theorem zero_add (x : State) : add zero x = x := by
  apply ext <;> exact SignedCount.zero_addCount _

/-- State addition is commutative. -/
theorem add_comm (x y : State) : add x y = add y x := by
  apply ext <;> exact addCount_comm _ _

/-- State addition is associative. -/
theorem add_assoc (x y z : State) : add (add x y) z = add x (add y z) := by
  apply ext <;> exact addCount_assoc _ _ _

/-- Self-subtraction yields the zero state. -/
theorem sub_self (x : State) : sub x x = zero := by
  apply ext <;> exact SignedCount.subCount_self _

/-- State subtraction distributes across state addition componentwise. -/
theorem sub_add_distrib (x y u v : State) :
    sub (add x y) (add u v) = add (sub x u) (sub y v) := by
  apply ext <;> exact subCount_add_distrib _ _ _ _

/-- Adding back a subtracted state recovers the original state. -/
theorem add_sub_cancel_right (x y : State) :
    add (sub x y) y = x := by
  apply ext <;> exact addCount_subCount_cancel_right _ _

/-- Adding back a subtracted state on the left recovers the original state. -/
theorem add_sub_cancel_left (x y : State) :
    add y (sub x y) = x := by
  apply ext <;> exact addCount_subCount_cancel_left _ _

/-- State subtraction by zero does nothing. -/
theorem sub_zero (x : State) : sub x zero = x := by
  apply ext <;> exact subCount_zero _

/-- State subtraction is addition with negation. -/
theorem sub_eq_add_negate (x y : State) : sub x y = add x (negate y) := by
  apply ext <;> rfl

/-- Adding a state to its negation yields zero. -/
theorem add_negate_right (x : State) : add x (negate x) = zero := by
  apply ext <;> exact addCount_negate_right _

/-- Adding the negation of a state on the left yields zero. -/
theorem add_negate_left (x : State) : add (negate x) x = zero := by
  apply ext <;> exact addCount_negate_left _

/-- State addition cancels a common left summand. -/
theorem add_left_cancel {x y z : State} (h : add x y = add x z) : y = z := by
  apply ext
  · exact addCount_left_cancel (congrArg State.c0 h)
  · exact addCount_left_cancel (congrArg State.c1 h)
  · exact addCount_left_cancel (congrArg State.c2 h)
  · exact addCount_left_cancel (congrArg State.c3 h)

/-- State addition cancels a common right summand. -/
theorem add_right_cancel {x y z : State} (h : add y x = add z x) : y = z := by
  apply ext
  · exact addCount_right_cancel (congrArg State.c0 h)
  · exact addCount_right_cancel (congrArg State.c1 h)
  · exact addCount_right_cancel (congrArg State.c2 h)
  · exact addCount_right_cancel (congrArg State.c3 h)

/-- A zero sum identifies one state as the negation of the other. -/
theorem eq_negate_of_add_eq_zero {x y : State} (h : add x y = zero) : x = negate y := by
  apply ext
  · exact eq_negate_of_addCount_eq_zero (congrArg State.c0 h)
  · exact eq_negate_of_addCount_eq_zero (congrArg State.c1 h)
  · exact eq_negate_of_addCount_eq_zero (congrArg State.c2 h)
  · exact eq_negate_of_addCount_eq_zero (congrArg State.c3 h)

/-- If `a + b = c`, then subtracting `a` from `c` recovers `b`. -/
theorem sub_eq_right_of_add_left {a b c : State} (h : add a b = c) : sub c a = b := by
  calc
    sub c a = sub (add a b) a := by rw [h]
    _ = sub (add a b) (add a zero) := by rw [add_zero]
    _ = add (sub a a) (sub b zero) := by
          exact sub_add_distrib a b a zero
    _ = add zero b := by rw [sub_self, sub_zero]
    _ = b := by rw [zero_add]

end State

/-- A projection is an idempotent endomap on the rebuilt state space. -/
structure Projection where
  toFun : State → State
  map_add : ∀ x y : State, toFun (State.add x y) = State.add (toFun x) (toFun y)
  map_zero : toFun State.zero = State.zero
  idem : ∀ x : State, toFun (toFun x) = toFun x

namespace Projection

instance : CoeFun Projection (fun _ => State → State) := ⟨Projection.toFun⟩

/-- Identity projection. -/
def id : Projection where
  toFun := fun x => x
  map_add := by
    intro x y
    rfl
  map_zero := rfl
  idem := by
    intro x
    rfl

end Projection

/-- A horizon tower is a nested family of projections. -/
structure HorizonTower where
  π : Nat → Projection
  nested : ∀ h₁ h₂, h₁ ≤ h₂ → ∀ x,
    (π h₁).toFun ((π h₂).toFun x) = (π h₁).toFun x
  nested_ge : ∀ h₁ h₂, h₂ ≤ h₁ → ∀ x,
    (π h₁).toFun ((π h₂).toFun x) = (π h₂).toFun x

/-- The trivial horizon tower with no shadow component. -/
def trivialTower : HorizonTower where
  π := fun _ => Projection.id
  nested := by
    intro _ _ _ x
    rfl
  nested_ge := by
    intro _ _ _ x
    rfl

/-- The shadow projection complementary to the observable horizon. -/
def shadowProj (T : HorizonTower) (h : Nat) : State → State :=
  fun x => State.sub x ((T.π h).toFun x)

/-- Coarse observable compression of an endomap. -/
def observedOp (T : HorizonTower) (h : Nat) (A : State → State) : State → State :=
  fun x => (T.π h).toFun (A ((T.π h).toFun x))

/-- Observable-to-shadow transport. -/
def leakageOp (T : HorizonTower) (h : Nat) (A : State → State) : State → State :=
  fun x => (shadowProj T h) (A ((T.π h).toFun x))

/-- Shadow-to-observable return map. -/
def returnOp (T : HorizonTower) (h : Nat) (A : State → State) : State → State :=
  fun x => (T.π h).toFun (A ((shadowProj T h) x))

/-- Round-trip defect through the horizon. -/
def defectOp (T : HorizonTower) (h : Nat) (A : State → State) : State → State :=
  fun x => (returnOp T h A) ((leakageOp T h A) x)

/-- Nilpotency predicate for a state endomap. -/
def isNilpotent (A : State → State) : Prop :=
  ∀ x : State, A (A x) = State.zero

/-- A state endomap preserves zero if it sends the zero state to zero. -/
def PreservesZero (A : State → State) : Prop :=
  A State.zero = State.zero

/-- Draft-facing transitivity lemma for nested horizons. -/
theorem nested_proj_comp (T : HorizonTower) (h₁ h₂ : Nat) (hle : h₁ ≤ h₂) (x : State) :
    (T.π h₁).toFun ((T.π h₂).toFun x) = (T.π h₁).toFun x :=
  T.nested h₁ h₂ hle x

/-- Reverse-order nested composition lemma. -/
theorem nested_proj_comp_ge (T : HorizonTower) (h₁ h₂ : Nat) (hle : h₂ ≤ h₁) (x : State) :
    (T.π h₁).toFun ((T.π h₂).toFun x) = (T.π h₂).toFun x :=
  T.nested_ge h₁ h₂ hle x

/-- The shadow projection annihilates points already fixed by the horizon. -/
theorem shadowProj_vanish_of_observable (T : HorizonTower) (h : Nat) (x : State)
    (hx : (T.π h).toFun x = x) :
    shadowProj T h x = State.zero := by
  unfold shadowProj
  rw [hx]
  exact State.sub_self x

/-- The shadow projection preserves the zero state. -/
theorem shadowProj_zero (T : HorizonTower) (h : Nat) :
    shadowProj T h State.zero = State.zero := by
  unfold shadowProj
  rw [(T.π h).map_zero]
  exact State.sub_self State.zero

/-- The shadow projection is additive because it is state subtraction against an
additive projection. -/
theorem shadowProj_add (T : HorizonTower) (h : Nat) (x y : State) :
    shadowProj T h (State.add x y) = State.add (shadowProj T h x) (shadowProj T h y) := by
  unfold shadowProj
  rw [(T.π h).map_add x y]
  exact State.sub_add_distrib x y ((T.π h).toFun x) ((T.π h).toFun y)

/-- Observable and shadow parts resolve the identity on states. -/
theorem resolution_of_identity_state (T : HorizonTower) (h : Nat) (x : State) :
    State.add ((T.π h).toFun x) (shadowProj T h x) = x := by
  unfold shadowProj
  exact State.add_sub_cancel_left x ((T.π h).toFun x)

/-- The observable projection annihilates the shadow component. -/
theorem projection_shadow_zero (T : HorizonTower) (h : Nat) (x : State) :
    (T.π h).toFun (shadowProj T h x) = State.zero := by
  have hproj :
      State.add ((T.π h).toFun ((T.π h).toFun x)) ((T.π h).toFun (shadowProj T h x))
        =
      (T.π h).toFun x := by
    calc
      State.add ((T.π h).toFun ((T.π h).toFun x)) ((T.π h).toFun (shadowProj T h x))
          = (T.π h).toFun (State.add ((T.π h).toFun x) (shadowProj T h x)) := by
              symm
              exact (T.π h).map_add ((T.π h).toFun x) (shadowProj T h x)
      _ = (T.π h).toFun x := by
            rw [resolution_of_identity_state]
  rw [(T.π h).idem x] at hproj
  have hproj' :
      State.add ((T.π h).toFun x) ((T.π h).toFun (shadowProj T h x))
        =
      State.add ((T.π h).toFun x) State.zero := by
    calc
      State.add ((T.π h).toFun x) ((T.π h).toFun (shadowProj T h x))
          = (T.π h).toFun x := hproj
      _ = State.add ((T.π h).toFun x) State.zero := by
            rw [State.add_zero]
  exact State.add_left_cancel hproj'

/-- The shadow projection is idempotent. -/
theorem shadowProj_idem (T : HorizonTower) (h : Nat) (x : State) :
    shadowProj T h (shadowProj T h x) = shadowProj T h x := by
  unfold shadowProj
  have hz : (T.π h).toFun (x.sub ((T.π h).toFun x)) = State.zero := by
    simpa [shadowProj] using projection_shadow_zero T h x
  rw [hz]
  exact State.sub_zero (shadowProj T h x)

/-- Applying an endomap to the observable component splits into observable and
leakage parts. -/
theorem observed_leakage_split (T : HorizonTower) (h : Nat) (A : State → State) (x : State) :
    State.add (observedOp T h A x) (leakageOp T h A x) = A ((T.π h).toFun x) := by
  unfold observedOp leakageOp
  exact resolution_of_identity_state T h (A ((T.π h).toFun x))

/-- Applying an endomap to the shadow component splits into return and residual
shadow parts. -/
theorem return_shadow_split (T : HorizonTower) (h : Nat) (A : State → State) (x : State) :
    State.add (returnOp T h A x) (shadowProj T h (A ((shadowProj T h) x))) =
      A ((shadowProj T h) x) := by
  unfold returnOp
  exact resolution_of_identity_state T h (A ((shadowProj T h) x))

/-- Leakage already lies in the shadow component. -/
theorem leakage_shadow_fixed (T : HorizonTower) (h : Nat) (A : State → State) (x : State) :
    shadowProj T h (leakageOp T h A x) = leakageOp T h A x := by
  unfold leakageOp
  exact shadowProj_idem T h (A ((T.π h).toFun x))

/-- The observable and shadow components resolve the image of a state under any
endomap once the input is split by the horizon. -/
theorem full_split_after_horizon_resolution
    (T : HorizonTower) (h : Nat) (A : State → State) (x : State) :
    State.add
        (State.add (observedOp T h A x) (leakageOp T h A x))
        (State.add (returnOp T h A x) (shadowProj T h (A ((shadowProj T h) x)))) =
      State.add (A ((T.π h).toFun x)) (A ((shadowProj T h) x)) := by
  rw [observed_leakage_split, return_shadow_split]

/-- The defect is the composite return-after-leakage map. -/
theorem defect_factorization (T : HorizonTower) (h : Nat) (A : State → State) (x : State) :
    defectOp T h A x = returnOp T h A (leakageOp T h A x) := rfl

/-- The image of the leakage component splits into the defect plus a residual
shadow term. -/
theorem defect_shadow_split (T : HorizonTower) (h : Nat) (A : State → State) (x : State) :
    State.add (defectOp T h A x) (shadowProj T h (A (leakageOp T h A x))) =
      A (leakageOp T h A x) := by
  have hsplit := return_shadow_split T h A (leakageOp T h A x)
  rw [leakage_shadow_fixed] at hsplit
  simpa [defectOp] using hsplit

/-- Under the trivial tower, the shadow projection vanishes identically. -/
theorem shadowProj_trivial (h : Nat) (x : State) :
    shadowProj trivialTower h x = State.zero := by
  exact shadowProj_vanish_of_observable trivialTower h x rfl

/-- Under the trivial tower, observation is the identity compression. -/
theorem observedOp_trivial (h : Nat) (A : State → State) (x : State) :
    observedOp trivialTower h A x = A x := rfl

/-- Under the trivial tower, leakage vanishes identically. -/
theorem leakageOp_trivial (h : Nat) (A : State → State) (x : State) :
    leakageOp trivialTower h A x = State.zero := by
  unfold leakageOp
  rw [shadowProj_trivial]

/-- Under the trivial tower, return vanishes for zero-preserving endomaps. -/
theorem returnOp_trivial_of_preservesZero (h : Nat) (A : State → State)
    (hA : PreservesZero A) (x : State) :
    returnOp trivialTower h A x = State.zero := by
  unfold returnOp
  rw [shadowProj_trivial, hA]
  rfl

/-- Under the trivial tower, the defect vanishes for zero-preserving endomaps. -/
theorem defectOp_trivial_of_preservesZero (h : Nat) (A : State → State)
    (hA : PreservesZero A) (x : State) :
    defectOp trivialTower h A x = State.zero := by
  rw [defect_factorization]
  exact returnOp_trivial_of_preservesZero h A hA (leakageOp trivialTower h A x)

end CoherenceCalculus
