import CoherenceCalculus.Foundation.FoundationalLemmasWidth

/-!
# Foundation.DefectRuleCore

Clean defect grammar on the rebuilt additive horizon core.

This module rebuilds the exact algebraic defect rules from the manuscript in the
active foundation chain, without importing the archived `LinOp` development.
The statements are expressed directly on:

- the rebuilt state space `State`
- additive endomaps `AddMap`
- explicit horizon projections `HorizonTower`
- explicit bilinear state operations
-/

namespace CoherenceCalculus

/-- Coherence defect of a state endomap at a horizon cut. -/
def coherenceDefect (T : HorizonTower) (h : Nat) (F : State → State) (x : State) : State :=
  State.sub ((T.π h).toFun (F x)) (F ((T.π h).toFun x))

/-- Two-argument defect for a bilinear state operation. -/
def bilinearDefect
    (T : HorizonTower) (h : Nat) (B : State → State → State) (x y : State) : State :=
  State.sub ((T.π h).toFun (B x y)) (B ((T.π h).toFun x) ((T.π h).toFun y))

/-- Additive chaining of two state differences. -/
theorem sub_eq_add_sub (a b c : State) :
    State.add (State.sub a b) (State.sub b c) = State.sub a c := by
  rw [State.sub_eq_add_negate, State.sub_eq_add_negate, State.sub_eq_add_negate]
  calc
    State.add (State.add a (State.negate b)) (State.add b (State.negate c))
        = State.add a (State.add (State.negate b) (State.add b (State.negate c))) := by
            exact State.add_assoc a (State.negate b) (State.add b (State.negate c))
    _ = State.add a (State.add (State.add (State.negate b) b) (State.negate c)) := by
          exact congrArg (State.add a) (State.add_assoc (State.negate b) b (State.negate c)).symm
    _ = State.add a (State.add State.zero (State.negate c)) := by
          rw [State.add_negate_left]
    _ = State.add a (State.negate c) := by
          rw [State.zero_add]
    _ = State.sub a c := by
          rw [← State.sub_eq_add_negate]

/-- Exact chain-rule decomposition for coherence defects. -/
theorem chain_rule_statement
    (T : HorizonTower) (h : Nat) (F G : State → State) (x : State) :
    coherenceDefect T h (fun y => F (G y)) x =
      State.add
        (coherenceDefect T h F (G x))
        (State.sub (F ((T.π h).toFun (G x))) (F (G ((T.π h).toFun x)))) := by
  unfold coherenceDefect
  exact (sub_eq_add_sub
    ((T.π h).toFun (F (G x)))
    (F ((T.π h).toFun (G x)))
    (F (G ((T.π h).toFun x)))).symm

/-- Observable leakage correction as an additive map. -/
def leakageCorrection (T : HorizonTower) (h : Nat) (A B : AddMap) : AddMap where
  toFun := leakageCorrectionTerm T h A B
  map_add := by
    intro x y
    unfold leakageCorrectionTerm
    rw [(T.π h).map_add, B.map_add, shadowProj_add, A.map_add, (T.π h).map_add]
  map_zero := by
    unfold leakageCorrectionTerm
    rw [(T.π h).map_zero, B.map_zero, shadowProj_zero, A.map_zero, (T.π h).map_zero]

/-- Exact bilinear defect decomposition under observable closure. -/
theorem product_rule_bilinear
    (T : HorizonTower) (h : Nat) (B : State → State → State)
    (hlin1 : ∀ x₁ x₂ y, B (State.add x₁ x₂) y = State.add (B x₁ y) (B x₂ y))
    (hlin2 : ∀ x y₁ y₂, B x (State.add y₁ y₂) = State.add (B x y₁) (B x y₂))
    (hclosure : ∀ x y,
      (T.π h).toFun (B ((T.π h).toFun x) ((T.π h).toFun y)) =
        B ((T.π h).toFun x) ((T.π h).toFun y))
    (x y : State) :
    bilinearDefect T h B x y =
      State.add
        ((T.π h).toFun (B ((T.π h).toFun x) (shadowProj T h y)))
        (State.add
          ((T.π h).toFun (B (shadowProj T h x) ((T.π h).toFun y)))
          ((T.π h).toFun (B (shadowProj T h x) (shadowProj T h y)))) := by
  let px := (T.π h).toFun x
  let sx := shadowProj T h x
  let py := (T.π h).toFun y
  let sy := shadowProj T h y

  have hx : x = State.add px sx := by
    exact (resolution_of_identity_state T h x).symm
  have hy : y = State.add py sy := by
    exact (resolution_of_identity_state T h y).symm

  have h_expand :
      B x y =
        State.add
          (B px py)
          (State.add (B px sy) (State.add (B sx py) (B sx sy))) := by
    calc
      B x y = B (State.add px sx) y := by
        rw [hx]
      _ = State.add (B px y) (B sx y) := by
        rw [hlin1]
      _ = State.add (B px (State.add py sy)) (B sx y) := by
        rw [hy]
      _ = State.add (State.add (B px py) (B px sy)) (B sx y) := by
        rw [hlin2]
      _ = State.add (State.add (B px py) (B px sy)) (B sx (State.add py sy)) := by
        rw [hy]
      _ = State.add (State.add (B px py) (B px sy)) (State.add (B sx py) (B sx sy)) := by
        rw [hlin2]
      _ = State.add (B px py) (State.add (B px sy) (State.add (B sx py) (B sx sy))) := by
        rw [State.add_assoc]

  have h_proj :
      (T.π h).toFun (B x y) =
        State.add
          ((T.π h).toFun (B px py))
          (State.add
            ((T.π h).toFun (B px sy))
            (State.add ((T.π h).toFun (B sx py)) ((T.π h).toFun (B sx sy)))) := by
    rw [h_expand]
    rw [(T.π h).map_add, (T.π h).map_add, (T.π h).map_add]

  unfold bilinearDefect
  rw [h_proj, hclosure]
  exact State.sub_eq_right_of_add_left rfl

/-- Quadratic defect as repeated observable-shadow and shadow-shadow terms. -/
theorem quadratic_defect
    (T : HorizonTower) (h : Nat) (B : State → State → State)
    (hlin1 : ∀ x₁ x₂ y, B (State.add x₁ x₂) y = State.add (B x₁ y) (B x₂ y))
    (hlin2 : ∀ x y₁ y₂, B x (State.add y₁ y₂) = State.add (B x y₁) (B x y₂))
    (hclosure : ∀ x y,
      (T.π h).toFun (B ((T.π h).toFun x) ((T.π h).toFun y)) =
        B ((T.π h).toFun x) ((T.π h).toFun y))
    (hsymm : ∀ x y, B x y = B y x)
    (x : State) :
    bilinearDefect T h B x x =
      State.add
        ((T.π h).toFun (B ((T.π h).toFun x) (shadowProj T h x)))
        (State.add
          ((T.π h).toFun (B ((T.π h).toFun x) (shadowProj T h x)))
          ((T.π h).toFun (B (shadowProj T h x) (shadowProj T h x)))) := by
  have hprod := product_rule_bilinear T h B hlin1 hlin2 hclosure x x
  have hswap :
      (T.π h).toFun (B (shadowProj T h x) ((T.π h).toFun x)) =
        (T.π h).toFun (B ((T.π h).toFun x) (shadowProj T h x)) := by
    rw [hsymm]
  rw [hswap] at hprod
  exact hprod

/-- Bilinear defect bound statement: on the rebuilt additive state space, the
exact bilinear defect is the observable sum of the three mixed/shadow terms.
Quantitative norm control can be layered on top of this identity later. -/
theorem bilinear_defect_bound_statement
    (T : HorizonTower) (h : Nat) (B : State → State → State)
    (hlin1 : ∀ x₁ x₂ y, B (State.add x₁ x₂) y = State.add (B x₁ y) (B x₂ y))
    (hlin2 : ∀ x y₁ y₂, B x (State.add y₁ y₂) = State.add (B x y₁) (B x y₂))
    (hclosure : ∀ x y,
      (T.π h).toFun (B ((T.π h).toFun x) ((T.π h).toFun y)) =
        B ((T.π h).toFun x) ((T.π h).toFun y))
    (x y : State) :
    bilinearDefect T h B x y =
      State.add
        ((T.π h).toFun (B ((T.π h).toFun x) (shadowProj T h y)))
        (State.add
          ((T.π h).toFun (B (shadowProj T h x) ((T.π h).toFun y)))
          ((T.π h).toFun (B (shadowProj T h x) (shadowProj T h y)))) :=
  product_rule_bilinear T h B hlin1 hlin2 hclosure x y

/-- Operator-multiplication defect is exactly the leakage correction term. -/
theorem operator_mult_defect_eq_leakage
    (T : HorizonTower) (h : Nat) (A B : AddMap) (x : State) :
    State.sub
        (observedOp T h (fun y => A (B y)) x)
        (observedOp T h A (observedOp T h B x)) =
      leakageCorrection T h A B x := by
  exact State.sub_eq_right_of_add_left (block_splitting T h A B x).symm

/-- Projected truth splits into the observed computation plus the shadow
correction term. -/
theorem resolution_correction
    (T : HorizonTower) (h : Nat) (L : AddMap) (x : State) :
    (T.π h).toFun (L x) =
      State.add
        (observedOp T h L.toFun x)
        ((T.π h).toFun (L (shadowProj T h x))) := by
  calc
    (T.π h).toFun (L x)
        = (T.π h).toFun (L (State.add ((T.π h).toFun x) (shadowProj T h x))) := by
            rw [resolution_of_identity_state]
    _ = (T.π h).toFun (State.add (L ((T.π h).toFun x)) (L (shadowProj T h x))) := by
          rw [L.map_add]
    _ = State.add ((T.π h).toFun (L ((T.π h).toFun x))) ((T.π h).toFun (L (shadowProj T h x))) := by
          rw [(T.π h).map_add]
    _ = State.add (observedOp T h L.toFun x) ((T.π h).toFun (L (shadowProj T h x))) := by
          unfold observedOp
          rfl

/-- Finite-rank observable recipe: once the input already lies in the observable
sector, the projected result is computed entirely by the horizon-compressed
operator. -/
theorem finite_rank_observable
    (T : HorizonTower) (h : Nat) (L : AddMap) (x : State)
    (hobs : (T.π h).toFun x = x) :
    (T.π h).toFun (L x) = observedOp T h L.toFun x := by
  calc
    (T.π h).toFun (L x)
        = (T.π h).toFun (L ((T.π h).toFun x)) := by
            rw [hobs]
    _ = observedOp T h L.toFun x := by
          unfold observedOp
          rw [hobs]

/-- A state is observable at horizon `h` when the projection fixes it. -/
def observableState (T : HorizonTower) (h : Nat) (x : State) : Prop :=
  (T.π h).toFun x = x

/-- Domain-restricted kernel of a constraint map on the observable layer. -/
def kernelAt (T : HorizonTower) (C : State → State) (h : Nat) (x : State) : Prop :=
  observableState T h x ∧ C x = State.zero

/-- States observable at a finer horizon remain observable at every coarser
enclosing horizon. -/
theorem observableState_monotone
    (T : HorizonTower) {h h' : Nat} (hle : h ≤ h') {x : State}
    (hx : observableState T h x) :
    observableState T h' x := by
  unfold observableState at hx ⊢
  calc
    (T.π h').toFun x = (T.π h').toFun ((T.π h).toFun x) := by
      rw [hx]
    _ = (T.π h).toFun x := by
      exact nested_proj_comp_ge T h' h hle x
    _ = x := hx

/-- Domain-restricted kernels are monotone under horizon refinement. -/
theorem kernel_monotone
    (T : HorizonTower) (C : State → State) {h h' : Nat} (hle : h ≤ h') {x : State}
    (hx : kernelAt T C h x) :
    kernelAt T C h' x := by
  rcases hx with ⟨hobs, hker⟩
  exact ⟨observableState_monotone T hle hobs, hker⟩

end CoherenceCalculus
