namespace CoherenceCalculus

/-- Pointwise scalar-algebra interface for multiplier reconstruction on a real
scalar lane. This is intentionally extensionality-free: the reconstruction
theorems below identify operators only through their action on test scalars. -/
structure ScalarMultiplierAlgebra (ScalarFn : Type) where
  zero : ScalarFn
  one : ScalarFn
  add : ScalarFn → ScalarFn → ScalarFn
  sub : ScalarFn → ScalarFn → ScalarFn
  mul : ScalarFn → ScalarFn → ScalarFn
  add_zero : ∀ f : ScalarFn, add f zero = f
  mul_one : ∀ f : ScalarFn, mul f one = f
  mul_zero : ∀ f : ScalarFn, mul f zero = zero
  mul_comm : ∀ f g : ScalarFn, mul f g = mul g f
  mul_assoc : ∀ f g h : ScalarFn, mul f (mul g h) = mul (mul f g) h
  sub_self : ∀ f : ScalarFn, sub f f = zero
  sub_zero : ∀ f : ScalarFn, sub f zero = f
  sub_eq_zero_iff : ∀ {f g : ScalarFn}, sub f g = zero ↔ f = g
  sub_eq_iff_eq_add : ∀ {x y z : ScalarFn}, sub x y = z ↔ x = add y z
  mul_sub : ∀ f x y : ScalarFn, mul f (sub x y) = sub (mul f x) (mul f y)
  sub_sub_distrib :
    ∀ a b c d : ScalarFn,
      sub (sub a b) (sub c d) = sub (sub a c) (sub b d)

/-- Scalar endomaps on the real scalar lane. -/
abbrev ScalarOp (ScalarFn : Type) : Type := ScalarFn → ScalarFn

/-- Multiplication by a scalar test function. -/
def mulOp {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn) (f : ScalarFn) : ScalarOp ScalarFn :=
  fun u => alg.mul f u

/-- Pointwise commutator. -/
def commApply {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (A B : ScalarOp ScalarFn) (u : ScalarFn) : ScalarFn :=
  alg.sub (A (B u)) (B (A u))

/-- Second multiplier commutator evaluated pointwise. -/
def secondCommApply {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (L : ScalarOp ScalarFn) (f g u : ScalarFn) : ScalarFn :=
  commApply alg (fun v => commApply alg L (mulOp alg f) v) (mulOp alg g) u

/-- Third multiplier commutator evaluated pointwise. -/
def thirdCommApply {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (L : ScalarOp ScalarFn) (f g h u : ScalarFn) : ScalarFn :=
  commApply alg (fun v => secondCommApply alg L f g v) (mulOp alg h) u

/-- Product defect of a scalar operator relative to multiplication by a test
scalar. This is the bilinear obstruction to a Leibniz rule on the real scalar
lane. -/
def productDefectApply {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (L : ScalarOp ScalarFn) (f u : ScalarFn) : ScalarFn :=
  alg.sub
    (alg.sub (L (alg.mul f u)) (alg.mul f (L u)))
    (alg.mul u (L f))

/-- Pointwise difference of two scalar operators. -/
def scalarRemainder {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (L Q : ScalarOp ScalarFn) : ScalarOp ScalarFn :=
  fun u => alg.sub (L u) (Q u)

/-- Zeroth-order multiplication term extracted from an operator remainder. -/
def scalarPotentialFromRemainder {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (R : ScalarOp ScalarFn) : ScalarFn :=
  R alg.one

/-- First-order remainder obtained by subtracting the multiplication term given
by evaluation on the unit. -/
def scalarDerivationFromRemainder {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (R : ScalarOp ScalarFn) : ScalarOp ScalarFn :=
  fun u => alg.sub (R u) (alg.mul (scalarPotentialFromRemainder alg R) u)

/-- Pointwise derivation law on the scalar lane. -/
def IsScalarDerivation {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (D : ScalarOp ScalarFn) : Prop :=
  D alg.one = alg.zero ∧
    ∀ f u : ScalarFn,
      D (alg.mul f u) = alg.add (alg.mul f (D u)) (alg.mul (D f) u)

/-- Any operator that commutes pointwise with all multipliers is itself
multiplication by its value on the unit. -/
theorem commuting_with_all_multipliers_is_multiplication
    {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (T : ScalarOp ScalarFn)
    (hcomm :
      ∀ f u : ScalarFn,
        commApply alg T (mulOp alg f) u = alg.zero) :
    ∀ u : ScalarFn, T u = alg.mul u (T alg.one) := by
  intro u
  have hzero := hcomm u alg.one
  unfold commApply mulOp at hzero
  rw [alg.mul_one] at hzero
  exact (alg.sub_eq_zero_iff.mp hzero)

/-- Third commutator truncation forces the second commutator to be a
multiplication operator determined by its value on the unit. -/
theorem second_commutator_is_multiplication
    {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (L : ScalarOp ScalarFn)
    (hthird :
      ∀ f g h u : ScalarFn,
        thirdCommApply alg L f g h u = alg.zero) :
    ∀ f g u : ScalarFn,
      secondCommApply alg L f g u =
        alg.mul u (secondCommApply alg L f g alg.one) := by
  intro f g
  exact
    commuting_with_all_multipliers_is_multiplication
      alg
      (fun u => secondCommApply alg L f g u)
      (fun h u => hthird f g h u)

/-- If two operators have third commutator truncation and their second
commutators agree on the unit, then their full second commutators agree
pointwise. -/
theorem second_commutators_agree_of_third_comm_zero_and_unit_agreement
    {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (L Q : ScalarOp ScalarFn)
    (hthirdL :
      ∀ f g h u : ScalarFn,
        thirdCommApply alg L f g h u = alg.zero)
    (hthirdQ :
      ∀ f g h u : ScalarFn,
        thirdCommApply alg Q f g h u = alg.zero)
    (hunit :
      ∀ f g : ScalarFn,
        secondCommApply alg L f g alg.one =
          secondCommApply alg Q f g alg.one) :
    ∀ f g u : ScalarFn,
      secondCommApply alg L f g u = secondCommApply alg Q f g u := by
  intro f g u
  rw [second_commutator_is_multiplication alg L hthirdL f g u]
  rw [second_commutator_is_multiplication alg Q hthirdQ f g u]
  rw [hunit f g]

/-- If two operators have identical second commutators pointwise, then any
third-commutator truncation for the comparison operator transfers to the
original operator. -/
theorem third_comm_zero_of_second_comm_agreement
    {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (L Q : ScalarOp ScalarFn)
    (hmatch :
      ∀ f g u : ScalarFn,
        secondCommApply alg L f g u =
          secondCommApply alg Q f g u)
    (hthirdQ :
      ∀ f g h u : ScalarFn,
        thirdCommApply alg Q f g h u = alg.zero) :
      ∀ f g h u : ScalarFn,
      thirdCommApply alg L f g h u = alg.zero := by
  intro f g h u
  change
    alg.sub
      (secondCommApply alg L f g (alg.mul h u))
      (alg.mul h (secondCommApply alg L f g u)) = alg.zero
  rw [hmatch f g (alg.mul h u), hmatch f g u]
  exact hthirdQ f g h u

/-- Full second-commutator agreement implies unit agreement automatically. -/
theorem second_commutator_unit_agreement_of_pointwise_agreement
    {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (L Q : ScalarOp ScalarFn)
    (hmatch :
      ∀ f g u : ScalarFn,
        secondCommApply alg L f g u =
          secondCommApply alg Q f g u) :
    ∀ f g : ScalarFn,
      secondCommApply alg L f g alg.one =
        secondCommApply alg Q f g alg.one := by
  intro f g
  exact hmatch f g alg.one

/-- Product defect controls the second multiplier commutator exactly. -/
theorem second_commutator_from_product_defect
    {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (L : ScalarOp ScalarFn)
    (f g u : ScalarFn) :
    secondCommApply alg L f g u =
      alg.sub
        (productDefectApply alg L f (alg.mul g u))
        (alg.mul g (productDefectApply alg L f u)) := by
  let A :=
    alg.sub
      (L (alg.mul f (alg.mul g u)))
      (alg.mul f (L (alg.mul g u)))
  let B :=
    alg.sub
      (alg.mul g (L (alg.mul f u)))
      (alg.mul g (alg.mul f (L u)))
  let C := alg.mul g (alg.mul u (L f))
  have hleft :
      secondCommApply alg L f g u =
        alg.sub
          (alg.sub (L (alg.mul f (alg.mul g u)))
            (alg.mul g (L (alg.mul f u))))
          (alg.sub
            (alg.mul f (L (alg.mul g u)))
            (alg.mul g (alg.mul f (L u)))) := by
    unfold secondCommApply commApply mulOp
    rw [alg.mul_sub, alg.sub_sub_distrib]
  have hright :
      alg.sub
          (productDefectApply alg L f (alg.mul g u))
          (alg.mul g (productDefectApply alg L f u)) =
        alg.sub (alg.sub A C) (alg.sub B C) := by
    unfold productDefectApply A B C
    rw [alg.mul_sub, alg.mul_sub, ← alg.mul_assoc g u (L f)]
  have hcollapse :
      alg.sub (alg.sub A C) (alg.sub B C) = alg.sub A B := by
    calc
      alg.sub (alg.sub A C) (alg.sub B C)
          = alg.sub (alg.sub A B) (alg.sub C C) := by
              exact alg.sub_sub_distrib A C B C
      _ = alg.sub (alg.sub A B) alg.zero := by
            rw [alg.sub_self]
      _ = alg.sub A B := by
            rw [alg.sub_zero]
  calc
    secondCommApply alg L f g u
        = alg.sub
            (alg.sub (L (alg.mul f (alg.mul g u)))
              (alg.mul g (L (alg.mul f u))))
            (alg.sub
              (alg.mul f (L (alg.mul g u)))
              (alg.mul g (alg.mul f (L u)))) := hleft
    _ = alg.sub A B := by
          unfold A B
          exact
            (alg.sub_sub_distrib
              (L (alg.mul f (alg.mul g u)))
              (alg.mul f (L (alg.mul g u)))
              (alg.mul g (L (alg.mul f u)))
              (alg.mul g (alg.mul f (L u)))).symm
    _ = alg.sub (alg.sub A C) (alg.sub B C) := by
          exact hcollapse.symm
    _ =
        alg.sub
          (productDefectApply alg L f (alg.mul g u))
          (alg.mul g (productDefectApply alg L f u)) := by
          exact hright.symm

/-- Sharing the same product defect is enough to force equality of second
multiplier commutators. -/
theorem second_commutator_match_of_shared_product_defect
    {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (L Q : ScalarOp ScalarFn)
    (hdefect :
      ∀ f u : ScalarFn,
        productDefectApply alg L f u =
          productDefectApply alg Q f u) :
    ∀ f g u : ScalarFn,
      secondCommApply alg L f g u =
        secondCommApply alg Q f g u := by
  intro f g u
  rw [second_commutator_from_product_defect alg L f g u]
  rw [second_commutator_from_product_defect alg Q f g u]
  rw [hdefect f (alg.mul g u), hdefect f u]

/-- The commutator is pointwise linear in the first operator with respect to
operator subtraction. -/
theorem commApply_sub
    {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (A B : ScalarOp ScalarFn)
    (f u : ScalarFn) :
    commApply alg (fun x => alg.sub (A x) (B x)) (mulOp alg f) u =
      alg.sub (commApply alg A (mulOp alg f) u)
        (commApply alg B (mulOp alg f) u) := by
  unfold commApply mulOp
  rw [alg.mul_sub, alg.sub_sub_distrib]

/-- The second commutator is pointwise linear in the first operator with
respect to operator subtraction. -/
theorem secondCommApply_sub
    {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (L Q : ScalarOp ScalarFn)
    (f g u : ScalarFn) :
    secondCommApply alg (fun x => alg.sub (L x) (Q x)) f g u =
        alg.sub (secondCommApply alg L f g u)
        (secondCommApply alg Q f g u) := by
  unfold secondCommApply commApply mulOp
  change
    alg.sub
        (alg.sub
          ((fun x => alg.sub (L x) (Q x)) (alg.mul f (alg.mul g u)))
          (alg.mul f ((fun x => alg.sub (L x) (Q x)) (alg.mul g u))))
        (alg.mul g
          (alg.sub
            ((fun x => alg.sub (L x) (Q x)) (alg.mul f u))
            (alg.mul f ((fun x => alg.sub (L x) (Q x)) u)))) =
      alg.sub
        (alg.sub
          (commApply alg L (mulOp alg f) (alg.mul g u))
          (alg.mul g (commApply alg L (mulOp alg f) u)))
        (alg.sub
          (commApply alg Q (mulOp alg f) (alg.mul g u))
          (alg.mul g (commApply alg Q (mulOp alg f) u)))
  have hleft :
      alg.sub
          ((fun x => alg.sub (L x) (Q x)) (alg.mul f (alg.mul g u)))
          (alg.mul f ((fun x => alg.sub (L x) (Q x)) (alg.mul g u))) =
        alg.sub
          (commApply alg L (mulOp alg f) (alg.mul g u))
          (commApply alg Q (mulOp alg f) (alg.mul g u)) := by
    simpa [commApply, mulOp] using
      (commApply_sub alg L Q f (alg.mul g u))
  have hright :
      alg.sub
          ((fun x => alg.sub (L x) (Q x)) (alg.mul f u))
          (alg.mul f ((fun x => alg.sub (L x) (Q x)) u)) =
        alg.sub
          (commApply alg L (mulOp alg f) u)
          (commApply alg Q (mulOp alg f) u) := by
    simpa [commApply, mulOp] using
      (commApply_sub alg L Q f u)
  rw [hleft, hright, alg.mul_sub, alg.sub_sub_distrib]

/-- Multiplication operators commute with all multipliers. -/
theorem multiplier_commutator_zero
    {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (v f u : ScalarFn) :
    commApply alg (mulOp alg v) (mulOp alg f) u = alg.zero := by
  unfold commApply mulOp
  rw [alg.mul_assoc, alg.mul_assoc, alg.mul_comm v f, alg.sub_self]

/-- Multiplication operators have zero second multiplier commutator. -/
theorem multiplier_second_commutator_zero
    {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (v f g u : ScalarFn) :
    secondCommApply alg (mulOp alg v) f g u = alg.zero := by
  unfold secondCommApply commApply mulOp
  change
    alg.sub
      (commApply alg (mulOp alg v) (mulOp alg f) (alg.mul g u))
      (alg.mul g (commApply alg (mulOp alg v) (mulOp alg f) u)) = alg.zero
  have hmult : ∀ x : ScalarFn,
      commApply alg (mulOp alg v) (mulOp alg f) x = alg.zero := by
    intro x
    exact multiplier_commutator_zero alg v f x
  rw [hmult (alg.mul g u), hmult u]
  rw [alg.mul_zero, alg.sub_self]

/-- If two operators have matching second commutators, then their pointwise
difference has zero second commutator. -/
theorem remainder_second_commutator_zero_of_matching_second_commutators
    {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (L Q : ScalarOp ScalarFn)
    (hmatch :
      ∀ f g u : ScalarFn,
        secondCommApply alg L f g u =
          secondCommApply alg Q f g u) :
    ∀ f g u : ScalarFn,
      secondCommApply alg (scalarRemainder alg L Q) f g u = alg.zero := by
  intro f g u
  unfold scalarRemainder
  rw [secondCommApply_sub, hmatch f g u, alg.sub_self]

/-- The unit value of the first-order remainder vanishes by construction. -/
theorem scalar_derivation_from_remainder_at_one
    {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (R : ScalarOp ScalarFn) :
    scalarDerivationFromRemainder alg R alg.one = alg.zero := by
  unfold scalarDerivationFromRemainder scalarPotentialFromRemainder
  rw [alg.mul_one, alg.sub_self]

/-- The remainder after subtracting the multiplication term carries zero second
commutator whenever the original remainder does. -/
theorem scalar_derivation_from_remainder_second_commutator_zero
    {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (R : ScalarOp ScalarFn)
    (hsecond :
      ∀ f g u : ScalarFn,
        secondCommApply alg R f g u = alg.zero) :
      ∀ f g u : ScalarFn,
      secondCommApply alg (scalarDerivationFromRemainder alg R) f g u = alg.zero := by
  intro f g u
  let V : ScalarFn := scalarPotentialFromRemainder alg R
  have hsplit :
      secondCommApply alg (scalarDerivationFromRemainder alg R) f g u =
        alg.sub
          (secondCommApply alg R f g u)
          (secondCommApply alg (fun x => alg.mul V x) f g u) := by
    simpa [scalarDerivationFromRemainder, V] using
      (secondCommApply_sub alg R (fun x => alg.mul V x) f g u)
  have hmult :
      secondCommApply alg (fun x => alg.mul V x) f g u = alg.zero := by
    simpa [mulOp, V] using
      (multiplier_second_commutator_zero alg V f g u)
  rw [hsplit, hsecond f g u, hmult, alg.sub_self]

/-- A remainder with zero second multiplier commutator becomes a derivation
after subtracting its value on the unit. -/
theorem scalar_derivation_from_remainder_is_derivation
    {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (R : ScalarOp ScalarFn)
    (hsecond :
      ∀ f g u : ScalarFn,
        secondCommApply alg R f g u = alg.zero) :
    IsScalarDerivation alg (scalarDerivationFromRemainder alg R) := by
  refine ⟨scalar_derivation_from_remainder_at_one alg R, ?_⟩
  intro f u
  have hmul :=
    commuting_with_all_multipliers_is_multiplication
      alg
      (fun x => commApply alg (scalarDerivationFromRemainder alg R) (mulOp alg f) x)
      (fun g x => scalar_derivation_from_remainder_second_commutator_zero alg R hsecond f g x)
  have hsub :
      alg.sub
          (scalarDerivationFromRemainder alg R (alg.mul f u))
          (alg.mul f (scalarDerivationFromRemainder alg R u)) =
        alg.mul u
          (commApply alg (scalarDerivationFromRemainder alg R) (mulOp alg f) alg.one) := by
    exact hmul u
  have hunit :
      commApply alg (scalarDerivationFromRemainder alg R) (mulOp alg f) alg.one =
        scalarDerivationFromRemainder alg R f := by
    unfold commApply mulOp
    rw [alg.mul_one]
    rw [scalar_derivation_from_remainder_at_one alg R]
    rw [alg.mul_zero, alg.sub_zero]
  rw [hunit, alg.mul_comm u (scalarDerivationFromRemainder alg R f)] at hsub
  exact (alg.sub_eq_iff_eq_add.mp hsub)

/-- Pointwise splitting of a second-commutator-zero remainder into its
multiplication term plus the residual derivation. -/
theorem scalar_remainder_splits_pointwise
    {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (R : ScalarOp ScalarFn)
    (u : ScalarFn) :
    R u =
      alg.add
        (alg.mul (scalarPotentialFromRemainder alg R) u)
        (scalarDerivationFromRemainder alg R u) := by
  unfold scalarDerivationFromRemainder scalarPotentialFromRemainder
  exact (alg.sub_eq_iff_eq_add.mp rfl)

/-- Extensionality-free reconstruction theorem: matching second multiplier
commutators force an operator to split pointwise into the comparison operator,
a multiplication term, and a derivation term. -/
theorem reconstruct_mod_derivation_pointwise
    {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (L Q : ScalarOp ScalarFn)
    (hmatch :
      ∀ f g u : ScalarFn,
        secondCommApply alg L f g u =
          secondCommApply alg Q f g u) :
    IsScalarDerivation alg
        (scalarDerivationFromRemainder alg (scalarRemainder alg L Q)) ∧
      ∀ u : ScalarFn,
        L u =
          alg.add (Q u)
            (alg.add
              (alg.mul
                (scalarPotentialFromRemainder alg (scalarRemainder alg L Q)) u)
              (scalarDerivationFromRemainder alg (scalarRemainder alg L Q) u)) := by
  have hsecond :=
    remainder_second_commutator_zero_of_matching_second_commutators
      alg L Q hmatch
  refine ⟨scalar_derivation_from_remainder_is_derivation
    alg (scalarRemainder alg L Q) hsecond, ?_⟩
  intro u
  have hsplit :=
    scalar_remainder_splits_pointwise
      alg (scalarRemainder alg L Q) u
  unfold scalarRemainder at hsplit
  exact (alg.sub_eq_iff_eq_add.mp hsplit)

/-- If every formally self-adjoint derivation on the chosen real scalar lane
vanishes, then matching second commutators already force a pointwise
comparison-operator-plus-potential normal form. -/
theorem reconstruct_mod_multiplication_pointwise_of_vanishing_derivations
    {ScalarFn : Type}
    (alg : ScalarMultiplierAlgebra ScalarFn)
    (L Q : ScalarOp ScalarFn)
    (hmatch :
      ∀ f g u : ScalarFn,
        secondCommApply alg L f g u =
          secondCommApply alg Q f g u)
    (hvanish :
      ∀ D : ScalarOp ScalarFn,
        IsScalarDerivation alg D → ∀ u : ScalarFn, D u = alg.zero) :
    ∀ u : ScalarFn,
      L u =
        alg.add (Q u)
          (alg.mul
            (scalarPotentialFromRemainder alg (scalarRemainder alg L Q)) u) := by
  have hrec := reconstruct_mod_derivation_pointwise alg L Q hmatch
  have hderiv := hrec.1
  have hzero :=
    hvanish
      (scalarDerivationFromRemainder alg (scalarRemainder alg L Q))
      hderiv
  intro u
  have hpoint := hrec.2 u
  rw [hzero u, alg.add_zero] at hpoint
  exact hpoint

end CoherenceCalculus
