/-
# Foundation.SignedCount

Derived signed counts built from natural-number tallies.

This layer replaces imported integer arithmetic in the active foundation. A
signed count is represented in normalized form by a positive tally and a
negative tally, with at most one side nonzero.
-/

import CoherenceCalculus.Foundation.CancellationCore

namespace CoherenceCalculus

/-- Raw signed tally: positive and negative contributions before cancellation. -/
structure RawCount where
  pos : Nat
  neg : Nat
  deriving DecidableEq, Repr

/-- Normalized signed count: one side has been fully cancelled. -/
structure SignedCount where
  pos : Nat
  neg : Nat
  normalized : pos = 0 ∨ neg = 0
  deriving DecidableEq, Repr

namespace SignedCount


/-- The zero signed count. -/
def zero : SignedCount := ⟨0, 0, Or.inl rfl⟩

/-- Purely nonnegative count. -/
def ofNat (n : Nat) : SignedCount := ⟨n, 0, Or.inr rfl⟩

/-- Purely negative count. -/
def negOfNat (n : Nat) : SignedCount := ⟨0, n, Or.inl rfl⟩

/-- Forget normalization back to the raw tally pair. -/
def toRaw (z : SignedCount) : RawCount := ⟨z.pos, z.neg⟩

/-- Normalize a raw tally pair by cancelling the smaller side. -/
def normalize (r : RawCount) : SignedCount := by
  by_cases h : r.neg ≤ r.pos
  · refine ⟨r.pos - r.neg, 0, Or.inr rfl⟩
  · refine ⟨0, r.neg - r.pos, Or.inl rfl⟩

/-- Every raw tally admits a normalized signed-count representative. -/
theorem normalize_normalized (r : RawCount) : (normalize r).pos = 0 ∨ (normalize r).neg = 0 :=
  (normalize r).normalized


/-- Extensionality for signed counts: equality is determined by the positive and
negative tallies; the normalization proof is proposition-valued and therefore
irrelevant. -/
theorem ext {a b : SignedCount} (hpos : a.pos = b.pos) (hneg : a.neg = b.neg) : a = b := by
  cases a with
  | mk apos aneg anorm =>
      cases b with
      | mk bpos bneg bnorm =>
          cases hpos
          cases hneg
          have hproof : anorm = bnorm := Subsingleton.elim _ _
          cases hproof
          rfl

/-- Normalization of a pure natural difference when the positive side dominates. -/
theorem normalize_pos_dom (a b : Nat) (h : b ≤ a) :
    normalize ⟨a, b⟩ = ⟨a - b, 0, Or.inr rfl⟩ := by
  unfold normalize
  rw [dif_pos h]

/-- Normalization of a pure natural difference when the negative side dominates. -/
theorem normalize_neg_dom (a b : Nat) (h : ¬ b ≤ a) :
    normalize ⟨a, b⟩ = ⟨0, b - a, Or.inl rfl⟩ := by
  unfold normalize
  rw [dif_neg h]

/-- Re-normalizing an already normalized signed count does nothing. -/
theorem normalize_toRaw (z : SignedCount) :
    normalize (toRaw z) = z := by
  cases z with
  | mk pos neg normalized =>
      dsimp [toRaw]
      cases normalized with
      | inl hpos =>
          cases hpos
          cases neg with
          | zero =>
              apply ext
              · rfl
              · rfl
          | succ n =>
              unfold normalize
              rw [dif_neg (Nat.not_succ_le_zero n)]
              apply ext
              · rfl
              · exact Nat.sub_zero (n + 1)
      | inr hneg =>
          cases hneg
          unfold normalize
          rw [dif_pos (Nat.zero_le pos)]
          apply ext
          · exact Nat.sub_zero pos
          · rfl

/-- Addition is performed on raw tallies and then normalized. -/
def addCount (a b : SignedCount) : SignedCount :=
  normalize ⟨a.pos + b.pos, a.neg + b.neg⟩

/-- Negation swaps positive and negative tally. -/
def negate (a : SignedCount) : SignedCount := ⟨a.neg, a.pos, by
  cases a.normalized with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl h⟩

/-- Subtraction is addition with negation. -/
def subCount (a b : SignedCount) : SignedCount := addCount a (negate b)

/-- A signed count is nonnegative if its negative side is zero. -/
def IsNonnegative (z : SignedCount) : Prop := z.neg = 0

/-- A signed count is nonpositive if its positive side is zero. -/
def IsNonpositive (z : SignedCount) : Prop := z.pos = 0

/-- Zero is both nonnegative and nonpositive. -/
theorem zero_nonnegative : IsNonnegative zero := rfl

/-- Zero is both nonnegative and nonpositive. -/
theorem zero_nonpositive : IsNonpositive zero := rfl

/-- Zero is a right identity for signed-count addition. -/
theorem addCount_zero (a : SignedCount) : addCount a zero = a := by
  simpa [addCount, zero, toRaw] using normalize_toRaw a

/-- Zero is a left identity for signed-count addition. -/
theorem zero_addCount (a : SignedCount) : addCount zero a = a := by
  simpa [addCount, zero, toRaw, Nat.zero_add] using normalize_toRaw a

/-- A strictly positive natural count is not zero as a signed count. -/
theorem ofNat_succ_ne_zero (n : Nat) : ofNat (n + 1) ≠ zero := by
  intro h
  cases h

/-- A strictly negative natural count is not zero as a signed count. -/
theorem negOfNat_succ_ne_zero (n : Nat) : negOfNat (n + 1) ≠ zero := by
  intro h
  cases h

/-- Subtracting two pure natural counts normalizes the raw difference. -/
theorem subCount_ofNat_ofNat (a b : Nat) :
    subCount (ofNat a) (ofNat b) = normalize ⟨a, b⟩ := by
  unfold subCount addCount ofNat negate normalize
  by_cases h : b ≤ a
  · simp [h]
  · simp [h]

/-- Normalizing equal positive and negative raw tallies yields zero. -/
theorem normalize_diag (n : Nat) :
    normalize ⟨n, n⟩ = zero := by
  unfold normalize zero
  rw [dif_pos (Nat.le_refl n)]
  apply ext
  · exact Nat.sub_self n
  · rfl

/-- A normalized raw tally vanishes only on the diagonal. -/
theorem normalize_eq_zero_implies_eq {a b : Nat}
    (hzero : normalize ⟨a, b⟩ = zero) : a = b := by
  by_cases h : b ≤ a
  · rw [normalize_pos_dom a b h] at hzero
    have hsub : a - b = 0 := by
      exact congrArg SignedCount.pos hzero
    exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hsub) h
  · rw [normalize_neg_dom a b h] at hzero
    have hsub : b - a = 0 := by
      exact congrArg SignedCount.neg hzero
    exact False.elim (h (Nat.le_of_sub_eq_zero hsub))

/-- Normalization hits zero exactly on diagonal raw tallies. -/
theorem normalize_eq_zero_iff_eq {a b : Nat} :
    normalize ⟨a, b⟩ = zero ↔ a = b := by
  constructor
  · exact normalize_eq_zero_implies_eq
  · intro hab
    cases hab
    exact normalize_diag a

/-- Subtracting a signed count from itself yields zero. -/
theorem subCount_self (a : SignedCount) :
    subCount a a = zero := by
  unfold subCount addCount negate
  rw [Nat.add_comm a.neg a.pos]
  exact normalize_diag (a.pos + a.neg)

/-- Equal pure natural tallies cancel exactly in signed-count subtraction. -/
theorem subCount_ofNat_eq_zero {a b : Nat} (h : a = b) :
    subCount (ofNat a) (ofNat b) = zero := by
  cases h
  exact subCount_self (ofNat a)

end SignedCount

end CoherenceCalculus
