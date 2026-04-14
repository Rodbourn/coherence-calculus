import CoherenceCalculus.Foundation.ConstraintSelectorCore

/-!
# Foundation.AdmissibilityCore

Minimal rebuilt admissibility layer for the manuscript's Chapter 4
`admissibility` section.

This module stays on the active finite/additive surface. It records:
- one-parameter boundary completions over `Nat`
- admissibility as least feasible scalar completion along that ray
- a concrete nonuniqueness example for minimal completion data
- the transfer-matrix / ratio-iteration shell behind branch selection

It does not rebuild Hilbert-space spectral theory inside the certified spine.
-/

namespace CoherenceCalculus

/-- One-parameter boundary completion along a nonnegative scalar ray. -/
structure BoundaryCompletion where
  baseValue : Nat
  boundaryWeight : Nat
  coeff : Nat

namespace BoundaryCompletion

/-- Value of the completed quadratic quantity on the displayed scalar ray. -/
def value (C : BoundaryCompletion) : Nat :=
  C.baseValue + C.coeff * C.boundaryWeight

end BoundaryCompletion

/-- Admissibility for the rebuilt scalar-ray surface: the displayed
coefficient is feasible and is least among all feasible scalar coefficients on
the same ray. -/
structure AdmissibleCompletion where
  candidate : BoundaryCompletion
  requiredLowerBound : Nat
  feasible : requiredLowerBound ≤ candidate.value
  minimal :
    ∀ n : Nat,
      requiredLowerBound ≤
          candidate.baseValue + n * candidate.boundaryWeight →
        candidate.coeff ≤ n

/-- Minimal scalar completion exports the scalar-ray feasibility/minimality
core of the manuscript statement. -/
theorem minimal_scalar_completion
    (A : AdmissibleCompletion) :
    A.requiredLowerBound ≤ A.candidate.value ∧
      (∀ n : Nat,
        A.requiredLowerBound ≤
            A.candidate.baseValue + n * A.candidate.boundaryWeight →
          A.candidate.coeff ≤ n) := by
  exact ⟨A.feasible, A.minimal⟩

/-- The scalar completion theorem packages both the selected coefficient and
its feasibility certificate. -/
theorem scalar_completion_compiler_output
    (A : AdmissibleCompletion) :
    ∃ ν : Nat,
      ν = A.candidate.coeff ∧
      A.requiredLowerBound ≤
        A.candidate.baseValue + ν * A.candidate.boundaryWeight := by
  refine ⟨A.candidate.coeff, rfl, ?_⟩
  simpa [BoundaryCompletion.value] using A.feasible

/-- The least-feasible-scalar formulation underlying the manuscript's
generalized-eigenvalue remark. -/
theorem generalized_eigenvalue_formulation
    (A : AdmissibleCompletion) :
    ∀ n : Nat,
      A.requiredLowerBound ≤
          A.candidate.baseValue + n * A.candidate.boundaryWeight →
        A.candidate.coeff ≤ n := by
  exact A.minimal

/-- The active compiler selector already carries the same least-feasible-scalar
data on the rebuilt finite state space. -/
theorem scalar_completion_matches_selector
    (data : Compiler.MinimalScalarRepair) :
    data.feasibleScalar data.scalarRepair ∧
      (∀ n : Nat, data.feasibleScalar n → data.scalarRepair ≤ n) := by
  exact ⟨data.scalarRepair_feasible, data.leastNonnegative⟩

/-- A two-sided completion toy model used only to witness nonuniqueness of
minimal feasible completions in a partial order. -/
structure SplitCompletion where
  leftCoeff : Nat
  rightCoeff : Nat

namespace SplitCompletion

/-- Feasibility is measured by the total completion mass reaching the required
threshold. -/
def feasible (required : Nat) (C : SplitCompletion) : Prop :=
  required ≤ C.leftCoeff + C.rightCoeff

/-- Pointwise order on split completions. -/
def le (A B : SplitCompletion) : Prop :=
  A.leftCoeff ≤ B.leftCoeff ∧ A.rightCoeff ≤ B.rightCoeff

/-- Explicit witness that a split completion is minimal among feasible split
completions for the displayed threshold. -/
structure MinimalWitness (required : Nat) (C : SplitCompletion) where
  witnessTag : Nat := 0
  feasible : SplitCompletion.feasible required C
  minimality :
    ∀ C' : SplitCompletion,
      SplitCompletion.feasible required C' → le C' C → le C C'

end SplitCompletion

/-- Left-supported minimal split completion. -/
def leftMinimalSplit : SplitCompletion where
  leftCoeff := 1
  rightCoeff := 0

/-- Right-supported minimal split completion. -/
def rightMinimalSplit : SplitCompletion where
  leftCoeff := 0
  rightCoeff := 1

/-- The left-supported split completion is minimal for threshold `1`. -/
def leftMinimalSplit_minimal :
    SplitCompletion.MinimalWitness 1 leftMinimalSplit where
  feasible := by
    change 1 ≤ 1 + 0
    rw [Nat.add_zero]
    exact Nat.le_refl 1
  minimality := by
    intro C' hfeas hle
    rcases hle with ⟨hleft, hright⟩
    have hright0 : C'.rightCoeff = 0 := by
      exact Nat.eq_zero_of_le_zero hright
    have hleft_ge : 1 ≤ C'.leftCoeff := by
      change 1 ≤ C'.leftCoeff + C'.rightCoeff at hfeas
      rw [hright0, Nat.add_zero] at hfeas
      exact hfeas
    have hleft_eq : C'.leftCoeff = 1 := Nat.le_antisymm hleft hleft_ge
    constructor
    · change 1 ≤ C'.leftCoeff
      rw [hleft_eq]
      exact Nat.le_refl 1
    · change 0 ≤ C'.rightCoeff
      rw [hright0]
      exact Nat.le_refl 0

/-- The right-supported split completion is minimal for threshold `1`. -/
def rightMinimalSplit_minimal :
    SplitCompletion.MinimalWitness 1 rightMinimalSplit where
  feasible := by
    change 1 ≤ 0 + 1
    rw [Nat.zero_add]
    exact Nat.le_refl 1
  minimality := by
    intro C' hfeas hle
    rcases hle with ⟨hleft, hright⟩
    have hleft0 : C'.leftCoeff = 0 := by
      exact Nat.eq_zero_of_le_zero hleft
    have hright_ge : 1 ≤ C'.rightCoeff := by
      change 1 ≤ C'.leftCoeff + C'.rightCoeff at hfeas
      rw [hleft0, Nat.zero_add] at hfeas
      exact hfeas
    have hright_eq : C'.rightCoeff = 1 := Nat.le_antisymm hright hright_ge
    constructor
    · change 0 ≤ C'.leftCoeff
      rw [hleft0]
      exact Nat.le_refl 0
    · change 1 ≤ C'.rightCoeff
      rw [hright_eq]
      exact Nat.le_refl 1

/-- Minimal feasible completions need not be unique in a partial order: the
left-supported and right-supported split completions are distinct minimal
examples at threshold `1`. -/
theorem leftMinimalSplit_feasible_example :
    SplitCompletion.feasible 1 leftMinimalSplit := by
  change 1 ≤ 1 + 0
  rw [Nat.add_zero]
  exact Nat.le_refl 1

/-- The left-supported split completion is pointwise minimal among feasible
split completions below it. -/
theorem leftMinimalSplit_minimal_example :
    ∀ C' : SplitCompletion,
      SplitCompletion.feasible 1 C' →
        SplitCompletion.le C' leftMinimalSplit →
          SplitCompletion.le leftMinimalSplit C' := by
  intro C' hfeas hle
  rcases hle with ⟨hleft, hright⟩
  have hright0 : C'.rightCoeff = 0 := by
    exact Nat.eq_zero_of_le_zero hright
  have hleft_ge : 1 ≤ C'.leftCoeff := by
    change 1 ≤ C'.leftCoeff + C'.rightCoeff at hfeas
    rw [hright0, Nat.add_zero] at hfeas
    exact hfeas
  have hleft_eq : C'.leftCoeff = 1 := Nat.le_antisymm hleft hleft_ge
  constructor
  · change 1 ≤ C'.leftCoeff
    rw [hleft_eq]
    exact Nat.le_refl 1
  · change 0 ≤ C'.rightCoeff
    rw [hright0]
    exact Nat.le_refl 0

/-- The right-supported split completion reaches the same threshold. -/
theorem rightMinimalSplit_feasible_example :
    SplitCompletion.feasible 1 rightMinimalSplit := by
  change 1 ≤ 0 + 1
  rw [Nat.zero_add]
  exact Nat.le_refl 1

/-- The right-supported split completion is pointwise minimal among feasible
split completions below it. -/
theorem rightMinimalSplit_minimal_example :
    ∀ C' : SplitCompletion,
      SplitCompletion.feasible 1 C' →
        SplitCompletion.le C' rightMinimalSplit →
          SplitCompletion.le rightMinimalSplit C' := by
  intro C' hfeas hle
  rcases hle with ⟨hleft, hright⟩
  have hleft0 : C'.leftCoeff = 0 := by
    exact Nat.eq_zero_of_le_zero hleft
  have hright_ge : 1 ≤ C'.rightCoeff := by
    change 1 ≤ C'.leftCoeff + C'.rightCoeff at hfeas
    rw [hleft0, Nat.zero_add] at hfeas
    exact hfeas
  have hright_eq : C'.rightCoeff = 1 := Nat.le_antisymm hright hright_ge
  constructor
  · change 0 ≤ C'.leftCoeff
    rw [hleft0]
    exact Nat.le_refl 0
  · change 1 ≤ C'.rightCoeff
    rw [hright_eq]
    exact Nat.le_refl 1

/-- The two canonical minimal split completions differ on their left
coefficient. -/
theorem leftRightMinimalSplit_distinct :
    leftMinimalSplit.leftCoeff ≠ rightMinimalSplit.leftCoeff := by
  change 1 ≠ 0
  exact succ_not_zero_counting 0

/-- Minimal feasible completions need not be unique in a partial order: the
left-supported and right-supported split completions are distinct minimal
examples at threshold `1`. -/
theorem admissible_completion_nonunique_example :
    SplitCompletion.feasible 1 leftMinimalSplit ∧
      (∀ C' : SplitCompletion,
        SplitCompletion.feasible 1 C' →
          SplitCompletion.le C' leftMinimalSplit →
            SplitCompletion.le leftMinimalSplit C') ∧
      SplitCompletion.feasible 1 rightMinimalSplit ∧
      (∀ C' : SplitCompletion,
        SplitCompletion.feasible 1 C' →
          SplitCompletion.le C' rightMinimalSplit →
            SplitCompletion.le rightMinimalSplit C') ∧
      leftMinimalSplit.leftCoeff ≠ rightMinimalSplit.leftCoeff := by
  exact ⟨leftMinimalSplit_feasible_example, leftMinimalSplit_minimal_example,
    rightMinimalSplit_feasible_example, rightMinimalSplit_minimal_example,
    leftRightMinimalSplit_distinct⟩

/-- Minimal transfer-matrix interface: only the trace/invariant parameter is
retained on the rebuilt finite surface. -/
structure TransferMatrix where
  traceInvariant : Nat

namespace TransferMatrix

/-- Characteristic equation of the two-branch transfer shell on the rebuilt
surface. -/
def characteristicEquation (M : TransferMatrix) (lam : Nat) : Prop :=
  lam * lam + 1 = M.traceInvariant * lam

end TransferMatrix

/-- The eigenvalue equation is exactly the characteristic equation attached to
the transfer shell. -/
theorem eigenvalue_equation (M : TransferMatrix) (lam : Nat) :
    M.characteristicEquation lam ↔ lam * lam + 1 = M.traceInvariant * lam := by
  rfl

/-- Ratio-iteration shell attached to the transfer invariant. The datum `zInv`
plays the role of the reciprocal term in the manuscript recurrence, but no
division is imported into the certified spine. -/
structure RatioIteration where
  matrix : TransferMatrix
  z : Nat → Nat
  zInv : Nat → Nat
  recurrence : ∀ n : Nat, z (n + 1) + zInv n = matrix.traceInvariant

/-- The two abstract branches of the transfer shell. -/
inductive TransferBranch where
  | contracting
  | expanding

/-- Crude branch magnitude on the rebuilt finite surface: the contracting
branch is normalized to `1`, while the expanding branch carries the invariant
scale. -/
def branchMagnitude (M : TransferMatrix) : TransferBranch → Nat
  | .contracting => 1
  | .expanding => M.traceInvariant

/-- The admissibility/stability selector on the rebuilt two-branch shell. -/
def selectedBranch (M : TransferMatrix) : TransferBranch :=
  if _h : 2 < M.traceInvariant then
    TransferBranch.expanding
  else
    TransferBranch.contracting

/-- Once the invariant exceeds `2`, the rebuilt selector chooses the expanding
branch, and that branch has strictly larger scale than the contracting one. -/
theorem expanding_branch_selected
    (M : TransferMatrix) (h : 2 < M.traceInvariant) :
    selectedBranch M = TransferBranch.expanding ∧
      branchMagnitude M TransferBranch.contracting <
        branchMagnitude M TransferBranch.expanding := by
  refine ⟨?_, ?_⟩
  · unfold selectedBranch
    rw [dif_pos h]
  · unfold branchMagnitude
    exact Nat.lt_trans (Nat.lt_succ_self 1) h

end CoherenceCalculus
