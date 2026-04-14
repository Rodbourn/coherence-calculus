import CoherenceCalculus.Foundation.PairingCore

/-!
# Foundation.ConstraintCompilerCore

Minimal rebuilt compiler interface for the manuscript's constraint-compiler
section.

This module does not reattach the archived Hilbert/group infrastructure. It
records the structural compiler surface directly on the active additive-state
spine:
- admissible quadratic forms on the observed state space
- equivariant operators and the commutant
- isotypic block restriction
- a canonical defect-to-bound compiler certificate
- blockwise symmetry reduction of admissibility
-/

namespace Compiler

open CoherenceCalculus

/-- Quadratic forms are represented by additive endomaps on the active state
space. -/
structure QuadForm where
  op : AddMap

namespace QuadForm

/-- Positive semidefiniteness on the rebuilt state space is expressed by the
nonnegativity of the coordinate pairing. Since the pairing lands in `Nat`, this
is a direct arithmetic predicate. -/
def IsPSD (Q : QuadForm) : Prop :=
  ∀ x : State, 0 ≤ State.pair x (Q.op x)

/-- Pointwise PSD order on quadratic forms. -/
def le (Q₁ Q₂ : QuadForm) : Prop :=
  ∀ x : State, State.pair x (Q₁.op x) ≤ State.pair x (Q₂.op x)

instance : LE QuadForm := ⟨le⟩

theorem le_refl (Q : QuadForm) : Q ≤ Q := by
  intro x
  exact Nat.le_refl _

end QuadForm

/-- Admissibility packages positivity together with minimality in the PSD
order. -/
structure Admissible (Q : QuadForm) : Prop where
  psd : QuadForm.IsPSD Q
  minimal : ∀ Q' : QuadForm, QuadForm.IsPSD Q' → Q' ≤ Q → Q'.op = Q.op

/-- Minimal finite group interface for the compiler's symmetry layer. -/
structure FinGroup where
  Carrier : Type
  mul : Carrier → Carrier → Carrier
  one : Carrier
  inv : Carrier → Carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  inv_mul : ∀ a, mul (inv a) a = one
  mul_inv : ∀ a, mul a (inv a) = one
  card : Nat
  card_pos : 0 < card

/-- Representation of a finite group by additive endomaps on the active state
space. -/
structure UnitaryRep (G : FinGroup) where
  U : G.Carrier → AddMap
  hom : ∀ g h : G.Carrier, ∀ x : State, U (G.mul g h) x = U g (U h x)
  map_one : ∀ x : State, U G.one x = x

/-- Equivariance means commuting with the group action. -/
def IsGEquivariant (G : FinGroup) (rep : UnitaryRep G) (A : AddMap) : Prop :=
  ∀ g : G.Carrier, ∀ x : State, A (rep.U g x) = rep.U g (A x)

/-- The commutant is the space of equivariant operators. -/
def IsInCommutant (G : FinGroup) (rep : UnitaryRep G) (A : AddMap) : Prop :=
  IsGEquivariant G rep A

/-- Isotypic projectors in the rebuilt compiler interface. -/
structure IsotypicProjector (G : FinGroup) (rep : UnitaryRep G) where
  proj : Projection
  equivariant : IsGEquivariant G rep (AddMap.ofProjection proj)

/-- A finite isotypic decomposition together with the off-diagonal vanishing and
commutation laws used by the compiler. -/
structure IsotypicDecomposition (G : FinGroup) (rep : UnitaryRep G) where
  numIrreps : Nat
  P : Fin numIrreps → IsotypicProjector G rep
  orthog : ∀ rho sigma : Fin numIrreps, rho ≠ sigma →
    ∀ x : State, (P rho).proj ((P sigma).proj x) = State.zero
  block_diagonal : ∀ rho sigma : Fin numIrreps, rho ≠ sigma →
    ∀ A : AddMap, IsGEquivariant G rep A →
    ∀ x : State, (P rho).proj (A ((P sigma).proj x)) = State.zero
  commutes_with_equivariant : ∀ rho : Fin numIrreps, ∀ A : AddMap,
    IsGEquivariant G rep A →
    ∀ x : State, A ((P rho).proj x) = (P rho).proj (A x)

/-- Normal form: equivariant operators have no off-diagonal isotypic blocks. -/
theorem normal_form (G : FinGroup) (rep : UnitaryRep G)
    (decomp : IsotypicDecomposition G rep) (A : AddMap)
    (hA : IsGEquivariant G rep A)
    (rho sigma : Fin decomp.numIrreps) (hne : rho ≠ sigma) :
    ∀ x : State, (decomp.P rho).proj (A ((decomp.P sigma).proj x)) = State.zero :=
  decomp.block_diagonal rho sigma hne A hA

/-- Block restriction of an operator to a projection sector. -/
def blockRestriction (P : Projection) (A : AddMap) : AddMap :=
  AddMap.comp (AddMap.ofProjection P) (AddMap.comp A (AddMap.ofProjection P))

/-- Restricting a `G`-equivariant operator to one isotypic block preserves
equivariance. -/
theorem isotypic_block_structure (G : FinGroup) (rep : UnitaryRep G)
    (decomp : IsotypicDecomposition G rep) (A : AddMap)
    (hA : IsGEquivariant G rep A) (rho : Fin decomp.numIrreps) :
    IsGEquivariant G rep (blockRestriction (decomp.P rho).proj A) := by
  intro g x
  unfold blockRestriction
  change
    (decomp.P rho).proj (A ((decomp.P rho).proj (rep.U g x))) =
      rep.U g ((decomp.P rho).proj (A ((decomp.P rho).proj x)))
  have hP_left : (decomp.P rho).proj (rep.U g x) = rep.U g ((decomp.P rho).proj x) := by
    exact (decomp.P rho).equivariant g x
  have hA_mid : A (rep.U g ((decomp.P rho).proj x)) = rep.U g (A ((decomp.P rho).proj x)) := by
    exact hA g ((decomp.P rho).proj x)
  have hP_right :
      (decomp.P rho).proj (rep.U g (A ((decomp.P rho).proj x))) =
        rep.U g ((decomp.P rho).proj (A ((decomp.P rho).proj x))) := by
    exact (decomp.P rho).equivariant g (A ((decomp.P rho).proj x))
  calc
    (decomp.P rho).proj (A ((decomp.P rho).proj (rep.U g x)))
        = (decomp.P rho).proj (A (rep.U g ((decomp.P rho).proj x))) := by
            rw [hP_left]
    _ = (decomp.P rho).proj (rep.U g (A ((decomp.P rho).proj x))) := by
          rw [hA_mid]
    _ = rep.U g ((decomp.P rho).proj (A ((decomp.P rho).proj x))) := by
          rw [hP_right]

/-- Parameter-count data for the commutant decomposition. -/
structure ParameterCount (G : FinGroup) (rep : UnitaryRep G) where
  numIrreps : Nat
  multiplicity : Fin numIrreps → Nat
  endomorphismDim : Fin numIrreps → Nat
  type_valid : ∀ rho, endomorphismDim rho = 1 ∨
    endomorphismDim rho = 2 ∨ endomorphismDim rho = 4

/-- Finite sum over `Fin n`, rebuilt by explicit recursion on `n`. -/
def finNatSum (n : Nat) (f : Fin n → Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 =>
      finNatSum k (fun i => f ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩) +
      f ⟨k, Nat.lt_succ_self k⟩

/-- Dimension formula for the equivariant parameter space. -/
def commutantDim (G : FinGroup) (rep : UnitaryRep G) (pc : ParameterCount G rep) : Nat :=
  finNatSum pc.numIrreps
    (fun rho => pc.multiplicity rho * pc.multiplicity rho * pc.endomorphismDim rho)

/-- Parameter-count formula for the rebuilt compiler interface. -/
theorem parameter_count_formula (G : FinGroup) (rep : UnitaryRep G)
    (pc : ParameterCount G rep) :
    commutantDim G rep pc =
      finNatSum pc.numIrreps
        (fun rho => pc.multiplicity rho * pc.multiplicity rho * pc.endomorphismDim rho) :=
  rfl

/-- A compiler derivation step carries an admissible quadratic form. -/
structure DerivationStep where
  form : QuadForm
  admissible : Admissible form

/-- The compiler's defect target is the quadratic form currently being
stabilized. -/
def stepDefect (step : DerivationStep) : QuadForm :=
  step.form

/-- A bound certificate packages a PSD upper bound for the current defect
target. -/
structure BoundCertificate (step : DerivationStep) where
  bound : QuadForm
  bound_psd : QuadForm.IsPSD bound
  defect_bounded : stepDefect step ≤ bound

/-- The compiler contract: every admissible derivation step carries a canonical
bound certificate, namely the defect target itself. -/
theorem compiler_contract (step : DerivationStep) :
    ∃ bc : BoundCertificate step,
      ∀ x : State,
        State.pair x (bc.bound.op x) = State.pair x ((stepDefect step).op x) := by
  refine ⟨{
    bound := stepDefect step
    bound_psd := step.admissible.psd
    defect_bounded := QuadForm.le_refl (stepDefect step)
  }, ?_⟩
  intro x
  rfl

/-- Equivariance for quadratic forms is just equivariance of the associated
additive operator. -/
def QuadForm.IsGEquivariant' (G : FinGroup) (rep : UnitaryRep G) (Q : QuadForm) : Prop :=
  IsGEquivariant G rep Q.op

/-- Symmetry reduction: minimality against all PSD competitors implies
minimality against the equivariant competitors in particular. -/
theorem symmetry_reduction (G : FinGroup) (rep : UnitaryRep G)
    (Q : QuadForm) (hQ : Admissible Q) (_hQeq : QuadForm.IsGEquivariant' G rep Q) :
    ∀ Q' : QuadForm, QuadForm.IsGEquivariant' G rep Q' →
      QuadForm.IsPSD Q' → Q' ≤ Q → Q'.op = Q.op := by
  intro Q' _hQ'eq hQ'psd hQ'le
  exact hQ.minimal Q' hQ'psd hQ'le

end Compiler
