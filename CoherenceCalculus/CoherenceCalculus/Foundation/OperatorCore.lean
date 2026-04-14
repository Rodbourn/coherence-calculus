import CoherenceCalculus.Foundation.HorizonCore

/-!
# Foundation.OperatorCore

Minimal additive operator layer above the rebuilt horizon core.

This layer introduces only:
- additive, zero-preserving state endomaps
- identity and composition
- observable compression along a horizon tower

It deliberately stops short of rebuilding shadow-additivity or the full defect
grammar; those require additional signed-count algebra that will be proved
separately.
-/

namespace CoherenceCalculus

/-- Additive zero-preserving endomaps on the rebuilt state space. -/
structure AddMap where
  toFun : State → State
  map_add : ∀ x y : State, toFun (State.add x y) = State.add (toFun x) (toFun y)
  map_zero : toFun State.zero = State.zero

namespace AddMap

instance : CoeFun AddMap (fun _ => State → State) := ⟨AddMap.toFun⟩

/-- Identity additive map. -/
def id : AddMap where
  toFun := fun x => x
  map_add := by
    intro x y
    rfl
  map_zero := rfl

/-- Any projection is an additive map. -/
def ofProjection (P : Projection) : AddMap where
  toFun := P.toFun
  map_add := P.map_add
  map_zero := P.map_zero

/-- Composition of additive maps. -/
def comp (A B : AddMap) : AddMap where
  toFun := fun x => A.toFun (B.toFun x)
  map_add := by
    intro x y
    rw [B.map_add, A.map_add]
  map_zero := by
    rw [B.map_zero, A.map_zero]

/-- Additive maps preserve state negation. -/
theorem map_negate (A : AddMap) (x : State) :
    A (State.negate x) = State.negate (A x) := by
  apply State.eq_negate_of_add_eq_zero
  calc
    State.add (A (State.negate x)) (A x)
        = A (State.add (State.negate x) x) := by
            rw [← A.map_add]
    _ = A State.zero := by
          rw [State.add_negate_left]
    _ = State.zero := by
          exact A.map_zero

/-- The shadow projection packaged as an additive map. -/
def shadowMap (T : HorizonTower) (h : Nat) : AddMap where
  toFun := shadowProj T h
  map_add := shadowProj_add T h
  map_zero := shadowProj_zero T h

/-- Observable compression of an additive map. -/
def observedMap (T : HorizonTower) (h : Nat) (A : AddMap) : AddMap where
  toFun := observedOp T h A.toFun
  map_add := by
    intro x y
    unfold observedOp
    rw [T.π h |>.map_add, A.map_add, T.π h |>.map_add]
  map_zero := by
    unfold observedOp
    rw [T.π h |>.map_zero, A.map_zero, T.π h |>.map_zero]

/-- Observable-to-shadow transport as an additive map. -/
def leakageMap (T : HorizonTower) (h : Nat) (A : AddMap) : AddMap :=
  comp (shadowMap T h) (comp A (ofProjection (T.π h)))

/-- Shadow-to-observable return as an additive map. -/
def returnMap (T : HorizonTower) (h : Nat) (A : AddMap) : AddMap :=
  comp (ofProjection (T.π h)) (comp A (shadowMap T h))

/-- Horizon defect as a composite additive map. -/
def defectMap (T : HorizonTower) (h : Nat) (A : AddMap) : AddMap :=
  comp (returnMap T h A) (leakageMap T h A)

/-- Residual shadow transport after applying an additive map to the shadow
component. -/
def residualShadowMap (T : HorizonTower) (h : Nat) (A : AddMap) : AddMap :=
  comp (shadowMap T h) (comp A (shadowMap T h))

/-- The packaged shadow map agrees with the plain shadow operator. -/
theorem shadowMap_apply (T : HorizonTower) (h : Nat) (x : State) :
    shadowMap T h x = shadowProj T h x := rfl

/-- The packaged leakage map agrees with the plain leakage operator. -/
theorem leakageMap_apply (T : HorizonTower) (h : Nat) (A : AddMap) (x : State) :
    leakageMap T h A x = leakageOp T h A.toFun x := rfl

/-- The packaged return map agrees with the plain return operator. -/
theorem returnMap_apply (T : HorizonTower) (h : Nat) (A : AddMap) (x : State) :
    returnMap T h A x = returnOp T h A.toFun x := rfl

/-- The packaged defect map agrees with the plain defect operator. -/
theorem defectMap_apply (T : HorizonTower) (h : Nat) (A : AddMap) (x : State) :
    defectMap T h A x = defectOp T h A.toFun x := rfl

/-- The packaged residual shadow map agrees with the corresponding plain
shadow-residual operator. -/
theorem residualShadowMap_apply (T : HorizonTower) (h : Nat) (A : AddMap) (x : State) :
    residualShadowMap T h A x = shadowProj T h (A (shadowProj T h x)) := rfl

/-- Observable compression is trivial under the identity tower. -/
theorem observedMap_trivial (h : Nat) (A : AddMap) :
    observedMap trivialTower h A = A := by
  cases A with
  | mk Ato Aadd Azero =>
      rfl

/-- Under the trivial tower, observed composition is ordinary composition. -/
theorem observedMap_comp_trivial (h : Nat) (A B : AddMap) :
    observedMap trivialTower h (comp A B) = comp A B := by
  exact observedMap_trivial h (comp A B)

/-- Under the trivial tower, the packaged shadow map vanishes identically. -/
theorem shadowMap_trivial (h : Nat) (x : State) :
    shadowMap trivialTower h x = State.zero := by
  exact shadowProj_trivial h x

/-- Under the trivial tower, packaged leakage vanishes identically. -/
theorem leakageMap_trivial (h : Nat) (A : AddMap) (x : State) :
    leakageMap trivialTower h A x = State.zero := by
  exact leakageOp_trivial h A.toFun x

/-- Under the trivial tower, packaged return vanishes identically. -/
theorem returnMap_trivial (h : Nat) (A : AddMap) (x : State) :
    returnMap trivialTower h A x = State.zero := by
  exact returnOp_trivial_of_preservesZero h A.toFun A.map_zero x

/-- Under the trivial tower, packaged defect vanishes identically. -/
theorem defectMap_trivial (h : Nat) (A : AddMap) (x : State) :
    defectMap trivialTower h A x = State.zero := by
  exact defectOp_trivial_of_preservesZero h A.toFun A.map_zero x

/-- Additive maps preserve the horizon resolution decomposition of a state. -/
theorem map_horizon_resolution (T : HorizonTower) (h : Nat) (A : AddMap) (x : State) :
    State.add (A ((T.π h).toFun x)) (A (shadowProj T h x)) = A x := by
  calc
    State.add (A ((T.π h).toFun x)) (A (shadowProj T h x))
        = A (State.add ((T.π h).toFun x) (shadowProj T h x)) := by
            rw [← A.map_add]
    _ = A x := by
          rw [resolution_of_identity_state]

/-- Whole-image decomposition for additive maps after horizon resolution. -/
theorem full_split_for_addMap (T : HorizonTower) (h : Nat) (A : AddMap) (x : State) :
    State.add
        (State.add (observedOp T h A.toFun x) (leakageOp T h A.toFun x))
        (State.add (returnOp T h A.toFun x) (shadowProj T h (A ((shadowProj T h) x)))) =
      A x := by
  calc
    State.add
        (State.add (observedOp T h A.toFun x) (leakageOp T h A.toFun x))
        (State.add (returnOp T h A.toFun x) (shadowProj T h (A ((shadowProj T h) x))))
        =
      State.add (A ((T.π h).toFun x)) (A ((shadowProj T h) x)) := by
        rw [full_split_after_horizon_resolution]
    _ = A x := by
        exact map_horizon_resolution T h A x

/-- The image of the packaged leakage component splits into the packaged defect
plus a residual shadow term. -/
theorem defect_split_for_addMap (T : HorizonTower) (h : Nat) (A : AddMap) (x : State) :
    State.add (defectMap T h A x) (shadowProj T h (A (leakageMap T h A x))) =
      A (leakageMap T h A x) := by
  exact defect_shadow_split T h A.toFun x

/-- The image of the packaged leakage component splits into the packaged defect
plus the packaged residual shadow map evaluated on the leakage input. -/
theorem defect_split_residual_for_addMap (T : HorizonTower) (h : Nat) (A : AddMap) (x : State) :
    State.add (defectMap T h A x) (residualShadowMap T h A (leakageMap T h A x)) =
      A (leakageMap T h A x) := by
  have hsplit := defect_split_for_addMap T h A x
  have hshadow :
      shadowProj T h (leakageMap T h A x) = leakageMap T h A x := by
    exact leakage_shadow_fixed T h A.toFun x
  rw [residualShadowMap_apply, hshadow]
  exact hsplit

end AddMap

end CoherenceCalculus
