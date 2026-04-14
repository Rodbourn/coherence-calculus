import CoherenceCalculus.Foundation.ProjectionCalculusCore
import CoherenceCalculus.Foundation.DefectRuleCore

/-!
# Foundation.TowerCalculusCore

Clean tower-calculus interfaces on the rebuilt additive operator spine.

This module does not reintroduce the archived `LinOp` or scalar hierarchy.
Instead it records the exact algebraic content needed for the Part I tower
surface:

- a tower index operator as explicit band-scaling data
- the commutator tower derivative
- the block formula in additive `h - k` form
- the Leibniz rule
- an explicit antiderivative witness interface
- a trace-style integration-by-parts law

Any genuine reconstruction of a canonical antiderivative or trace can later be
plugged into these interfaces without changing the certified theorem surface.
-/

namespace CoherenceCalculus

namespace State

/-- Repeated state addition by a natural number. -/
def nsmul : Nat → State → State
  | 0, _ => zero
  | n + 1, x => add (nsmul n x) x

/-- Zero repeated addition is the zero state. -/
theorem nsmul_zero (x : State) : nsmul 0 x = zero := by
  rfl

/-- Successor repeated addition adds one more copy. -/
theorem nsmul_succ (n : Nat) (x : State) : nsmul (n + 1) x = add (nsmul n x) x := by
  rfl

/-- Additive maps of natural multiplicities split at sums of indices. -/
theorem nsmul_add (m n : Nat) (x : State) :
    nsmul (m + n) x = add (nsmul m x) (nsmul n x) := by
  induction m with
  | zero =>
      rw [Nat.zero_add, nsmul_zero, zero_add]
  | succ m ih =>
      rw [Nat.succ_add, nsmul_succ, ih, nsmul_succ]
      calc
        State.add (State.add (State.nsmul m x) (State.nsmul n x)) x
            = State.add (State.nsmul m x) (State.add (State.nsmul n x) x) := by
                rw [State.add_assoc]
        _ = State.add (State.nsmul m x) (State.add x (State.nsmul n x)) := by
              rw [State.add_comm (State.nsmul n x) x]
        _ = State.add (State.add (State.nsmul m x) x) (State.nsmul n x) := by
              rw [← State.add_assoc]

/-- Repeated addition of the zero state remains zero. -/
theorem nsmul_state_zero (n : Nat) : nsmul n zero = zero := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [nsmul_succ, ih, zero_add]

end State

namespace AddMap

/-- Extensionality for additive endomaps. -/
theorem ext {A B : AddMap} (h : ∀ x : State, A x = B x) : A = B := by
  cases A with
  | mk Ato Aadd Azero =>
      cases B with
      | mk Bto Badd Bzero =>
          have hfun : Ato = Bto := funext h
          cases hfun
          have hadd : Aadd = Badd := Subsingleton.elim _ _
          have hzero : Azero = Bzero := Subsingleton.elim _ _
          cases hadd
          cases hzero
          rfl

/-- The zero additive endomap. -/
def zero : AddMap where
  toFun := fun _ => State.zero
  map_add := by
    intro x y
    exact (State.zero_add State.zero).symm
  map_zero := rfl

/-- Additive endomaps preserve state subtraction. -/
theorem map_sub_state (A : AddMap) (x y : State) :
    A (State.sub x y) = State.sub (A x) (A y) := by
  rw [State.sub_eq_add_negate, A.map_add, AddMap.map_negate, State.sub_eq_add_negate]

/-- Pointwise subtraction of additive endomaps. -/
def sub (A B : AddMap) : AddMap where
  toFun := fun x => State.sub (A x) (B x)
  map_add := by
    intro x y
    rw [A.map_add, B.map_add]
    exact State.sub_add_distrib (A x) (A y) (B x) (B y)
  map_zero := by
    rw [A.map_zero, B.map_zero]
    exact State.sub_self State.zero

/-- Composition associates on additive endomaps. -/
theorem comp_assoc (A B C : AddMap) :
    comp A (comp B C) = comp (comp A B) C := by
  apply ext
  intro x
  rfl

/-- Left composition distributes over additive-map subtraction. -/
theorem comp_sub_left (A B C : AddMap) :
    comp (sub A B) C = sub (comp A C) (comp B C) := by
  apply ext
  intro x
  rfl

/-- Right composition distributes over additive-map subtraction. -/
theorem comp_sub_right (A B C : AddMap) :
    comp A (sub B C) = sub (comp A B) (comp A C) := by
  apply ext
  intro x
  exact map_sub_state A (B x) (C x)

/-- Additive endomaps preserve repeated addition. -/
theorem map_nsmul (A : AddMap) (n : Nat) (x : State) :
    A (State.nsmul n x) = State.nsmul n (A x) := by
  induction n with
  | zero =>
      rw [State.nsmul_zero, A.map_zero, State.nsmul_zero]
  | succ n ih =>
      rw [State.nsmul_succ, A.map_add, ih, State.nsmul_succ]

end AddMap

/-- The `(h,k)` tower block of an additive endomap. -/
def towerBlock (T : HorizonTower) (h k : Nat) (A : AddMap) : AddMap :=
  AddMap.comp (incrementProj T h) (AddMap.comp A (incrementProj T k))

/-- Tower blocks distribute pointwise over additive-map addition. -/
theorem towerBlock_add_apply
    (T : HorizonTower) (h k : Nat) (A B : AddMap) (x : State) :
    towerBlock T h k (AddMap.add A B) x =
      State.add (towerBlock T h k A x) (towerBlock T h k B x) := by
  unfold towerBlock
  change
    incrementProj T h
      (State.add (A (incrementProj T k x)) (B (incrementProj T k x))) =
      State.add
        (incrementProj T h (A (incrementProj T k x)))
        (incrementProj T h (B (incrementProj T k x)))
  rw [(incrementProj T h).map_add]

/-- An additive endomap has tower transport order at most `m` if its
`(h,k)`-block vanishes whenever the horizon-band gap exceeds `m`. This is the
reconstructed block-support form of the manuscript definition, written without
`Int` or absolute values. -/
def towerTransportOrderAtMost (T : HorizonTower) (A : AddMap) (m : Nat) : Prop :=
  ∀ h k : Nat, ∀ x : State, h + m < k ∨ k + m < h → towerBlock T h k A x = State.zero

/-- The identity additive endomap is diagonal in the tower bands, hence has
transport order `0`. -/
theorem towerTransportOrder_id (T : HorizonTower) :
    towerTransportOrderAtMost T AddMap.id 0 := by
  intro h k x hgap
  have hne : h ≠ k := by
    intro heq
    cases heq
    cases hgap with
    | inl hlt =>
        rw [Nat.add_zero] at hlt
        exact Nat.lt_irrefl _ hlt
    | inr hlt =>
        rw [Nat.add_zero] at hlt
        exact Nat.lt_irrefl _ hlt
  unfold towerBlock
  exact increment_orthogonality T h k hne x

private theorem horizonProjection_increment_eq
    (T : HorizonTower) (h0 k : Nat) (hle : k ≤ h0) (x : State) :
    (T.π h0) (incrementProj T k x) = incrementProj T k x := by
  change
    (AddMap.ofProjection (T.π h0)) (State.sub ((T.π k) x) ((T.π (k - 1)) x)) =
      State.sub ((T.π k) x) ((T.π (k - 1)) x)
  rw [AddMap.map_sub_state (AddMap.ofProjection (T.π h0))
    ((T.π k) x) ((T.π (k - 1)) x)]
  have hk1 : k - 1 ≤ h0 := Nat.le_trans (Nat.sub_le k 1) hle
  have hprojk :
      (AddMap.ofProjection (T.π h0)) ((T.π k) x) = (T.π k) x := by
    exact nested_proj_comp_ge T h0 k hle x
  have hprojkm1 :
      (AddMap.ofProjection (T.π h0)) ((T.π (k - 1)) x) = (T.π (k - 1)) x := by
    exact nested_proj_comp_ge T h0 (k - 1) hk1 x
  rw [hprojk, hprojkm1]

private theorem horizonProjection_increment_zero
    (T : HorizonTower) (h0 k : Nat) (hlt : h0 < k) (x : State) :
    (T.π h0) (incrementProj T k x) = State.zero := by
  change
    (AddMap.ofProjection (T.π h0)) (State.sub ((T.π k) x) ((T.π (k - 1)) x)) =
      State.zero
  rw [AddMap.map_sub_state (AddMap.ofProjection (T.π h0))
    ((T.π k) x) ((T.π (k - 1)) x)]
  have hk : h0 ≤ k := Nat.le_of_lt hlt
  have hk1 : h0 ≤ k - 1 := Nat.le_sub_one_of_lt hlt
  have hprojk :
      (AddMap.ofProjection (T.π h0)) ((T.π k) x) = (T.π h0) x := by
    exact nested_proj_comp T h0 k hk x
  have hprojkm1 :
      (AddMap.ofProjection (T.π h0)) ((T.π (k - 1)) x) = (T.π h0) x := by
    exact nested_proj_comp T h0 (k - 1) hk1 x
  rw [hprojk, hprojkm1]
  exact State.sub_self ((T.π h0) x)

private theorem horizonShadow_increment_zero
    (T : HorizonTower) (h0 k : Nat) (hle : k ≤ h0) (x : State) :
    projectionShadow (T.π h0) (incrementProj T k x) = State.zero := by
  unfold projectionShadow
  rw [horizonProjection_increment_eq T h0 k hle x]
  exact State.sub_self (incrementProj T k x)

private theorem horizonShadow_increment_eq
    (T : HorizonTower) (h0 k : Nat) (hlt : h0 < k) (x : State) :
    projectionShadow (T.π h0) (incrementProj T k x) = incrementProj T k x := by
  unfold projectionShadow
  rw [horizonProjection_increment_zero T h0 k hlt x]
  exact State.sub_zero (incrementProj T k x)

/-- Any horizon projection is diagonal in the tower bands and therefore has
transport order `0`. -/
theorem towerTransportOrder_projection
    (T : HorizonTower) (h0 : Nat) :
    towerTransportOrderAtMost T (AddMap.ofProjection (T.π h0)) 0 := by
  intro h k x hgap
  have hne : h ≠ k := by
    intro heq
    cases heq
    cases hgap with
    | inl hlt =>
        rw [Nat.add_zero] at hlt
        exact Nat.lt_irrefl _ hlt
    | inr hlt =>
        rw [Nat.add_zero] at hlt
        exact Nat.lt_irrefl _ hlt
  unfold towerBlock
  change incrementProj T h ((T.π h0) (incrementProj T k x)) = State.zero
  cases Nat.lt_or_ge h0 k with
  | inl hlt =>
      rw [horizonProjection_increment_zero T h0 k hlt x]
      exact (incrementProj T h).map_zero
  | inr hle =>
      rw [horizonProjection_increment_eq T h0 k hle x]
      exact increment_orthogonality T h k hne x

/-- The complementary shadow projection is also diagonal in the tower bands and
therefore has transport order `0`. -/
theorem towerTransportOrder_shadowProjection
    (T : HorizonTower) (h0 : Nat) :
    towerTransportOrderAtMost T
      (AddMap.ofProjection (complementProjection (T.π h0))) 0 := by
  intro h k x hgap
  have hne : h ≠ k := by
    intro heq
    cases heq
    cases hgap with
    | inl hlt =>
        rw [Nat.add_zero] at hlt
        exact Nat.lt_irrefl _ hlt
    | inr hlt =>
        rw [Nat.add_zero] at hlt
        exact Nat.lt_irrefl _ hlt
  unfold towerBlock
  change incrementProj T h (projectionShadow (T.π h0) (incrementProj T k x)) = State.zero
  cases Nat.lt_or_ge h0 k with
  | inl hlt =>
      rw [horizonShadow_increment_eq T h0 k hlt x]
      exact increment_orthogonality T h k hne x
  | inr hle =>
      rw [horizonShadow_increment_zero T h0 k hle x]
      exact (incrementProj T h).map_zero

/-- If two additive endomaps have bounded tower transport order, their sum has
order bounded by the maximum of the two bounds. -/
theorem towerTransportOrder_add
    (T : HorizonTower) {A B : AddMap} {m n : Nat}
    (hA : towerTransportOrderAtMost T A m)
    (hB : towerTransportOrderAtMost T B n) :
    towerTransportOrderAtMost T (AddMap.add A B) (Nat.max m n) := by
  intro h k x hgap
  unfold towerBlock
  change
    incrementProj T h
      (State.add (A (incrementProj T k x)) (B (incrementProj T k x))) =
      State.zero
  rw [(incrementProj T h).map_add]
  cases hgap with
  | inl hlt =>
      have hm : h + m < k := Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_max_left m n) h) hlt
      have hn : h + n < k := Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_max_right m n) h) hlt
      have hAz :
          incrementProj T h (A (incrementProj T k x)) = State.zero := by
        simpa [towerBlock] using hA h k x (Or.inl hm)
      have hBz :
          incrementProj T h (B (incrementProj T k x)) = State.zero := by
        simpa [towerBlock] using hB h k x (Or.inl hn)
      rw [hAz, hBz, State.zero_add]
  | inr hlt =>
      have hm : k + m < h := Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_max_left m n) k) hlt
      have hn : k + n < h := Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_max_right m n) k) hlt
      have hAz :
          incrementProj T h (A (incrementProj T k x)) = State.zero := by
        simpa [towerBlock] using hA h k x (Or.inr hm)
      have hBz :
          incrementProj T h (B (incrementProj T k x)) = State.zero := by
        simpa [towerBlock] using hB h k x (Or.inr hn)
      rw [hAz, hBz, State.zero_add]

/-- Explicit certificate for the additive clause of tower-order arithmetic. -/
structure TowerTransportOrderAddDatum
    (T : HorizonTower) (A B : AddMap) (m n : Nat) where
  leftBound : towerTransportOrderAtMost T A m
  rightBound : towerTransportOrderAtMost T B n
  sumBound : towerTransportOrderAtMost T (AddMap.add A B) (Nat.max m n)

/-- The additive clause of tower-order arithmetic exported from an explicit
certificate package. -/
theorem towerTransportOrder_add_certificate
    {T : HorizonTower} {A B : AddMap} {m n : Nat}
    (data : TowerTransportOrderAddDatum T A B m n) :
    towerTransportOrderAtMost T (AddMap.add A B) (Nat.max m n) := by
  exact data.sumBound

/-- Tower transport-order bounds are monotone in the order parameter. -/
theorem towerTransportOrderAtMost_mono
    (T : HorizonTower) {A : AddMap} {m n : Nat}
    (hA : towerTransportOrderAtMost T A m) (hmn : m ≤ n) :
    towerTransportOrderAtMost T A n := by
  intro h k x hgap
  apply hA h k x
  cases hgap with
  | inl hlt =>
      exact Or.inl (Nat.lt_of_le_of_lt (Nat.add_le_add_left hmn h) hlt)
  | inr hlt =>
      exact Or.inr (Nat.lt_of_le_of_lt (Nat.add_le_add_left hmn k) hlt)

/-- Explicit datum supplying the composition clause of tower-order arithmetic.
The additive and derivative clauses are rebuilt directly below. -/
structure TowerOrderArithmeticDatum (T : HorizonTower) where
  comp_rule :
    ∀ {A B : AddMap} {m n : Nat},
      towerTransportOrderAtMost T A m →
        towerTransportOrderAtMost T B n →
          towerTransportOrderAtMost T (AddMap.comp A B) (m + n)

/-- The composition clause of tower-order arithmetic exported from the
explicit arithmetic datum. -/
theorem towerTransportOrder_comp
    (T : HorizonTower) (arith : TowerOrderArithmeticDatum T)
    {A B : AddMap} {m n : Nat}
    (hA : towerTransportOrderAtMost T A m)
    (hB : towerTransportOrderAtMost T B n) :
    towerTransportOrderAtMost T (AddMap.comp A B) (m + n) := by
  exact arith.comp_rule hA hB

/-- Observable compression by a horizon projection does not enlarge a tower
transport-order bound. -/
theorem towerTransportOrder_blockPP
    (T : HorizonTower) (arith : TowerOrderArithmeticDatum T) (h0 : Nat)
    {A : AddMap} {r : Nat}
    (hA : towerTransportOrderAtMost T A r) :
    towerTransportOrderAtMost T (blockPP (T.π h0) A) r := by
  unfold blockPP
  have hinner := arith.comp_rule hA (towerTransportOrder_projection T h0)
  rw [Nat.add_zero] at hinner
  have houter := arith.comp_rule (towerTransportOrder_projection T h0) hinner
  rw [Nat.zero_add] at houter
  exact houter

/-- Observable-to-shadow transport along a horizon projection preserves the
same tower transport-order bound. -/
theorem towerTransportOrder_blockPQ
    (T : HorizonTower) (arith : TowerOrderArithmeticDatum T) (h0 : Nat)
    {A : AddMap} {r : Nat}
    (hA : towerTransportOrderAtMost T A r) :
    towerTransportOrderAtMost T (blockPQ (T.π h0) A) r := by
  unfold blockPQ
  have hinner := arith.comp_rule hA (towerTransportOrder_shadowProjection T h0)
  rw [Nat.add_zero] at hinner
  have houter := arith.comp_rule (towerTransportOrder_projection T h0) hinner
  rw [Nat.zero_add] at houter
  exact houter

/-- Shadow-to-observable transport along a horizon projection preserves the
same tower transport-order bound. -/
theorem towerTransportOrder_blockQP
    (T : HorizonTower) (arith : TowerOrderArithmeticDatum T) (h0 : Nat)
    {A : AddMap} {r : Nat}
    (hA : towerTransportOrderAtMost T A r) :
    towerTransportOrderAtMost T (blockQP (T.π h0) A) r := by
  unfold blockQP
  have hinner := arith.comp_rule hA (towerTransportOrder_projection T h0)
  rw [Nat.add_zero] at hinner
  have houter := arith.comp_rule (towerTransportOrder_shadowProjection T h0) hinner
  rw [Nat.zero_add] at houter
  exact houter

/-- Internal shadow transport along a horizon projection preserves the same
tower transport-order bound. -/
theorem towerTransportOrder_blockQQ
    (T : HorizonTower) (arith : TowerOrderArithmeticDatum T) (h0 : Nat)
    {A : AddMap} {r : Nat}
    (hA : towerTransportOrderAtMost T A r) :
    towerTransportOrderAtMost T (blockQQ (T.π h0) A) r := by
  unfold blockQQ
  have hinner := arith.comp_rule hA (towerTransportOrder_shadowProjection T h0)
  rw [Nat.add_zero] at hinner
  have houter := arith.comp_rule (towerTransportOrder_shadowProjection T h0) hinner
  rw [Nat.zero_add] at houter
  exact houter

/-- An explicit scale-index operator for a tower is any additive endomap that
acts diagonally on each increment band, both before and after projection back
to that band. -/
structure towerIndexOperator (T : HorizonTower) where
  toAddMap : AddMap
  projected_band_scale :
    ∀ h : Nat, ∀ x : State,
      incrementProj T h (toAddMap x) = State.nsmul h (incrementProj T h x)
  band_scale :
    ∀ h : Nat, ∀ x : State,
      toAddMap (incrementProj T h x) = State.nsmul h (incrementProj T h x)

/-- The tower derivative is the commutator with the chosen index operator. -/
def towerDerivative (T : HorizonTower) (N : towerIndexOperator T) (A : AddMap) : AddMap :=
  AddMap.sub (AddMap.comp N.toAddMap A) (AddMap.comp A N.toAddMap)

/-- On the `(h,k)` block, the tower derivative contributes the additive
`h - k` scaling induced by the index operator. -/
theorem towerDerivative_block_formula
    (T : HorizonTower) (N : towerIndexOperator T) (A : AddMap)
    (h k : Nat) (x : State) :
    towerBlock T h k (towerDerivative T N A) x =
      State.sub
        (State.nsmul h (towerBlock T h k A x))
        (State.nsmul k (towerBlock T h k A x)) := by
  unfold towerBlock towerDerivative
  change
    incrementProj T h
      (State.sub
        (N.toAddMap (A (incrementProj T k x)))
        (A (N.toAddMap (incrementProj T k x))))
      =
    State.sub
      (State.nsmul h (incrementProj T h (A (incrementProj T k x))))
      (State.nsmul k (incrementProj T h (A (incrementProj T k x))))
  rw [AddMap.map_sub_state (incrementProj T h)
    (N.toAddMap (A (incrementProj T k x)))
    (A (N.toAddMap (incrementProj T k x)))]
  rw [N.projected_band_scale h (A (incrementProj T k x))]
  rw [N.band_scale k x]
  rw [AddMap.map_nsmul A k (incrementProj T k x)]
  rw [AddMap.map_nsmul (incrementProj T h) k (A (incrementProj T k x))]

/-- The tower derivative preserves a tower transport-order bound. -/
theorem towerTransportOrder_derivative
    (T : HorizonTower) (N : towerIndexOperator T) {A : AddMap} {m : Nat}
    (hA : towerTransportOrderAtMost T A m) :
    towerTransportOrderAtMost T (towerDerivative T N A) m := by
  intro h k x hgap
  have hAx : towerBlock T h k A x = State.zero := hA h k x hgap
  calc
    towerBlock T h k (towerDerivative T N A) x
        = State.sub
            (State.nsmul h (towerBlock T h k A x))
            (State.nsmul k (towerBlock T h k A x)) := by
              exact towerDerivative_block_formula T N A h k x
    _ = State.sub (State.nsmul h State.zero) (State.nsmul k State.zero) := by
          rw [hAx]
    _ = State.sub State.zero (State.nsmul k State.zero) := by
          rw [State.nsmul_state_zero]
    _ = State.sub State.zero State.zero := by
          rw [State.nsmul_state_zero]
    _ = State.zero := by
          exact State.sub_self State.zero

/-- The tower derivative is a derivation for additive endomap composition. -/
theorem towerDerivative_leibniz
    (T : HorizonTower) (N : towerIndexOperator T) (A B : AddMap) (x : State) :
    towerDerivative T N (AddMap.comp A B) x =
      AddMap.add
        (AddMap.comp (towerDerivative T N A) B)
        (AddMap.comp A (towerDerivative T N B)) x := by
  unfold towerDerivative
  change
    State.sub
      (N.toAddMap (A (B x)))
      (A (B (N.toAddMap x)))
      =
    State.add
      (State.sub
        (N.toAddMap (A (B x)))
        (A (N.toAddMap (B x))))
      (A (State.sub (N.toAddMap (B x)) (B (N.toAddMap x))))
  rw [AddMap.map_sub_state A (N.toAddMap (B x)) (B (N.toAddMap x))]
  exact (sub_eq_add_sub
    (N.toAddMap (A (B x)))
    (A (N.toAddMap (B x)))
    (A (B (N.toAddMap x)))).symm

/-- Explicit antiderivative data for a chosen tower derivative. -/
structure towerAntiderivativeData
    (T : HorizonTower) (N : towerIndexOperator T) (B : AddMap) where
  toAddMap : AddMap
  derivative_eq : towerDerivative T N toAddMap = B

/-- A tower antiderivative is any explicitly supplied right inverse to the
chosen tower derivative on the operator under study. -/
def towerAntiderivative
    (T : HorizonTower) (N : towerIndexOperator T) (B : AddMap)
    (data : towerAntiderivativeData T N B) : AddMap :=
  data.toAddMap

/-- Fundamental theorem of tower calculus: the supplied antiderivative
differentiates back to the original additive endomap. -/
theorem towerCalculus_FTC
    (T : HorizonTower) (N : towerIndexOperator T) (B : AddMap)
    (data : towerAntiderivativeData T N B) :
    towerDerivative T N (towerAntiderivative T N B data) = B := by
  exact data.derivative_eq

/-- A trace-style functional sufficient for the tower integration-by-parts
identity: it must respect operator subtraction and cyclic permutation. -/
structure towerTrace where
  toFun : AddMap → State
  map_sub_left_comp :
    ∀ A B C : AddMap,
      toFun (AddMap.comp (AddMap.sub A B) C) =
        State.sub (toFun (AddMap.comp A C)) (toFun (AddMap.comp B C))
  map_sub_right_comp :
    ∀ A B C : AddMap,
      toFun (AddMap.comp A (AddMap.sub B C)) =
        State.sub (toFun (AddMap.comp A B)) (toFun (AddMap.comp A C))
  assoc :
    ∀ A B C : AddMap,
      toFun (AddMap.comp (AddMap.comp A B) C) =
        toFun (AddMap.comp A (AddMap.comp B C))
  cyclic : ∀ A B : AddMap, toFun (AddMap.comp A B) = toFun (AddMap.comp B A)

/-- Integration by parts for the tower derivative follows from subtraction
linearity and cyclicity of the supplied trace-style functional. -/
theorem towerCalculus_IBP
    (trace : towerTrace) (T : HorizonTower) (N : towerIndexOperator T)
    (A B : AddMap) :
    trace.toFun (AddMap.comp (towerDerivative T N A) B) =
      State.negate (trace.toFun (AddMap.comp A (towerDerivative T N B))) := by
  apply State.eq_negate_of_add_eq_zero
  have hlhs :
      trace.toFun (AddMap.comp (towerDerivative T N A) B) =
        State.sub
          (trace.toFun (AddMap.comp (AddMap.comp N.toAddMap A) B))
          (trace.toFun (AddMap.comp (AddMap.comp A N.toAddMap) B)) := by
    unfold towerDerivative
    exact trace.map_sub_left_comp (AddMap.comp N.toAddMap A) (AddMap.comp A N.toAddMap) B
  have hrhs :
      trace.toFun (AddMap.comp A (towerDerivative T N B)) =
        State.sub
          (trace.toFun (AddMap.comp A (AddMap.comp N.toAddMap B)))
          (trace.toFun (AddMap.comp A (AddMap.comp B N.toAddMap))) := by
    unfold towerDerivative
    exact trace.map_sub_right_comp A (AddMap.comp N.toAddMap B) (AddMap.comp B N.toAddMap)
  have hfirst :
      trace.toFun (AddMap.comp (AddMap.comp N.toAddMap A) B) =
        trace.toFun (AddMap.comp N.toAddMap (AddMap.comp A B)) := by
    exact trace.assoc N.toAddMap A B
  have hmiddle :
      trace.toFun (AddMap.comp (AddMap.comp A N.toAddMap) B) =
        trace.toFun (AddMap.comp A (AddMap.comp N.toAddMap B)) := by
    exact trace.assoc A N.toAddMap B
  have hthird :
      trace.toFun (AddMap.comp A (AddMap.comp B N.toAddMap)) =
        trace.toFun (AddMap.comp (AddMap.comp A B) N.toAddMap) := by
    exact (trace.assoc A B N.toAddMap).symm
  have hcyc :
      trace.toFun (AddMap.comp N.toAddMap (AddMap.comp A B)) =
        trace.toFun (AddMap.comp (AddMap.comp A B) N.toAddMap) := by
    exact trace.cyclic N.toAddMap (AddMap.comp A B)
  rw [hlhs, hrhs, hfirst, hmiddle, hthird]
  calc
    State.add
      (State.sub
        (trace.toFun (AddMap.comp N.toAddMap (AddMap.comp A B)))
        (trace.toFun (AddMap.comp A (AddMap.comp N.toAddMap B))))
      (State.sub
        (trace.toFun (AddMap.comp A (AddMap.comp N.toAddMap B)))
        (trace.toFun (AddMap.comp (AddMap.comp A B) N.toAddMap)))
        =
      State.sub
        (trace.toFun (AddMap.comp N.toAddMap (AddMap.comp A B)))
        (trace.toFun (AddMap.comp (AddMap.comp A B) N.toAddMap)) := by
          exact sub_eq_add_sub
            (trace.toFun (AddMap.comp N.toAddMap (AddMap.comp A B)))
            (trace.toFun (AddMap.comp A (AddMap.comp N.toAddMap B)))
            (trace.toFun (AddMap.comp (AddMap.comp A B) N.toAddMap))
    _ = State.zero := by
          rw [hcyc]
          exact State.sub_self (trace.toFun (AddMap.comp (AddMap.comp A B) N.toAddMap))

/-- Summary packaging of the tower-calculus surface: derivation plus
integration by parts once the index operator and trace-style witness have been
made explicit. -/
theorem towerCalculus_summary
    (T : HorizonTower) (N : towerIndexOperator T) (trace : towerTrace) :
    (∀ A B x,
      towerDerivative T N (AddMap.comp A B) x =
        AddMap.add
          (AddMap.comp (towerDerivative T N A) B)
          (AddMap.comp A (towerDerivative T N B)) x) ∧
    (∀ A B,
      trace.toFun (AddMap.comp (towerDerivative T N A) B) =
        State.negate (trace.toFun (AddMap.comp A (towerDerivative T N B)))) := by
  refine ⟨?_, ?_⟩
  · intro A B x
    exact towerDerivative_leibniz T N A B x
  · intro A B
    exact towerCalculus_IBP trace T N A B

/-- Bilateral indices for transport recursions. `pos n` encodes the index
`n + 1`, while `neg n` encodes `-(n + 1)`. -/
inductive BilateralIndex where
  | zero
  | pos : Nat → BilateralIndex
  | neg : Nat → BilateralIndex
  deriving DecidableEq, Repr

/-- Forward shift on bilateral transport indices. -/
def bilateralSucc : BilateralIndex → BilateralIndex
  | .zero => .pos 0
  | .pos n => .pos (n + 1)
  | .neg 0 => .zero
  | .neg (n + 1) => .neg n

/-- Backward shift on bilateral transport indices. -/
def bilateralPred : BilateralIndex → BilateralIndex
  | .zero => .neg 0
  | .pos 0 => .zero
  | .pos (n + 1) => .pos n
  | .neg n => .neg (n + 1)

/-- Rebuilt bilateral sequence space for reversible transport channels. -/
abbrev SequenceTransportSpace := BilateralIndex → State

/-- The recursion operator induced by a one-step transport base on the rebuilt
bilateral sequence space. -/
def transportRecursionOperator (B : AddMap) (x : SequenceTransportSpace) :
    SequenceTransportSpace :=
  fun n =>
    State.sub
      (x (bilateralSucc n))
      (State.sub (B (x n)) (x (bilateralPred n)))

/-- Pointwise kernel condition for the rebuilt transport recursion operator. -/
def inTransportKernel (B : AddMap) (x : SequenceTransportSpace) : Prop :=
  ∀ n : BilateralIndex, transportRecursionOperator B x n = State.zero

private theorem state_sub_eq_zero_iff_eq (x y : State) :
    State.sub x y = State.zero ↔ x = y := by
  constructor
  · intro h
    calc
      x = State.add (State.sub x y) y := by
            symm
            exact State.add_sub_cancel_right x y
      _ = State.add State.zero y := by rw [h]
      _ = y := by rw [State.zero_add]
  · intro h
    rw [h]
    exact State.sub_self y

/-- The transport recursion kernel condition is exactly the second-order
reversible recurrence written pointwise on bilateral indices. -/
theorem transport_recursion_kernel (B : AddMap) (x : SequenceTransportSpace) :
    inTransportKernel B x ↔
      ∀ n : BilateralIndex,
        x (bilateralSucc n) = State.sub (B (x n)) (x (bilateralPred n)) := by
  constructor
  · intro hk n
    exact (state_sub_eq_zero_iff_eq
      (x (bilateralSucc n))
      (State.sub (B (x n)) (x (bilateralPred n)))).mp (hk n)
  · intro hrec n
    exact (state_sub_eq_zero_iff_eq
      (x (bilateralSucc n))
      (State.sub (B (x n)) (x (bilateralPred n)))).2 (hrec n)

/-- A reversible one-step transport base determines exactly the corresponding
second-order recursion constraint on the rebuilt bilateral sequence space. -/
theorem reversible_transport_recursion (B : AddMap) (x : SequenceTransportSpace) :
    inTransportKernel B x ↔
      ∀ n : BilateralIndex,
        x (bilateralSucc n) = State.sub (B (x n)) (x (bilateralPred n)) := by
  exact transport_recursion_kernel B x

end CoherenceCalculus
