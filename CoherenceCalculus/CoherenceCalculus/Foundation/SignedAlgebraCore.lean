import CoherenceCalculus.Foundation.NormalizationCore

/-!
# Foundation.SignedAlgebraCore

Semantic algebra for signed counts via raw tally pairs.

This module keeps the algebraic burden at the raw-count level, where
normalization congruence can lift semantic equivalences back to canonical
signed-count equalities.
-/

namespace CoherenceCalculus

namespace RawCount

/-- Extensionality for raw tally pairs. -/
theorem ext {r s : RawCount} (hpos : r.pos = s.pos) (hneg : r.neg = s.neg) : r = s := by
  cases r with
  | mk rpos rneg =>
      cases s with
      | mk spos sneg =>
          cases hpos
          cases hneg
          rfl

/-- The zero raw tally pair. -/
def zero : RawCount := ⟨0, 0⟩

/-- Raw addition combines positive and negative tallies componentwise. -/
def add (r s : RawCount) : RawCount :=
  ⟨r.pos + s.pos, r.neg + s.neg⟩

/-- Raw negation swaps positive and negative tallies. -/
def negate (r : RawCount) : RawCount :=
  ⟨r.neg, r.pos⟩

/-- Raw addition is associative. -/
theorem add_assoc (r s t : RawCount) : add (add r s) t = add r (add s t) := by
  cases r with
  | mk rpos rneg =>
      cases s with
      | mk spos sneg =>
          cases t with
          | mk tpos tneg =>
              exact RawCount.ext
                (by
                  dsimp [add]
                  exact add_assoc_counting rpos spos tpos)
                (by
                  dsimp [add]
                  exact add_assoc_counting rneg sneg tneg)

/-- Raw zero is a right identity for raw addition. -/
theorem add_zero (r : RawCount) : add r zero = r := by
  cases r with
  | mk pos neg =>
      rfl

/-- Raw zero is a left identity for raw addition. -/
theorem zero_add (r : RawCount) : add zero r = r := by
  cases r with
  | mk pos neg =>
      exact RawCount.ext
        (by
          dsimp [add, zero]
          exact zero_add_counting pos)
        (by
          dsimp [add, zero]
          exact zero_add_counting neg)

end RawCount

/-- Equality of raw tally pairs implies raw equivalence. -/
theorem rawEquivalent_of_eq {r s : RawCount} (h : r = s) : RawEquivalent r s := by
  cases h
  exact rawEquivalent_refl r

/-- Raw equivalence is preserved by componentwise raw addition. -/
theorem rawEquivalent_add {r r' s s' : RawCount}
    (hr : RawEquivalent r r') (hs : RawEquivalent s s') :
    RawEquivalent (RawCount.add r s) (RawCount.add r' s') := by
  unfold RawEquivalent at hr hs ⊢
  dsimp [RawCount.add]
  calc
    (r.pos + s.pos) + (r'.neg + s'.neg)
        = (r.pos + r'.neg) + (s.pos + s'.neg) := by
            exact add_pair_swap_counting r.pos s.pos r'.neg s'.neg
    _ = (r'.pos + r.neg) + (s.pos + s'.neg) := by
          rw [hr]
    _ = (r'.pos + s'.pos) + (r.neg + s.neg) := by
          rw [hs]
          exact add_pair_swap_counting r'.pos r.neg s'.pos s.neg

/-- Raw equivalence is preserved by raw negation. -/
theorem rawEquivalent_negate {r s : RawCount} (h : RawEquivalent r s) :
    RawEquivalent (RawCount.negate r) (RawCount.negate s) := by
  unfold RawEquivalent at h ⊢
  dsimp [RawCount.negate]
  calc
    r.neg + s.pos = s.pos + r.neg := by
      rw [add_comm_counting]
    _ = r.pos + s.neg := by
      exact h.symm
    _ = s.neg + r.pos := by
      rw [add_comm_counting]

/-- A raw tally plus its negation is raw-equivalent to zero. -/
theorem rawEquivalent_neg_add_zero (r : RawCount) :
    RawEquivalent (RawCount.add (RawCount.negate r) r) RawCount.zero := by
  unfold RawEquivalent
  dsimp [RawCount.add, RawCount.negate, RawCount.zero]
  calc
    r.neg + r.pos = r.pos + r.neg := by
      rw [add_comm_counting]
    _ = 0 + (r.pos + r.neg) := by
      rw [zero_add_counting]

/-- Signed-count addition is commutative. -/
theorem addCount_comm (a b : SignedCount) :
    SignedCount.addCount a b = SignedCount.addCount b a := by
  unfold SignedCount.addCount
  apply normalize_congr
  apply rawEquivalent_of_eq
  apply RawCount.ext
  · dsimp [RawCount.add, SignedCount.toRaw]
    rw [add_comm_counting a.pos b.pos]
  · dsimp [RawCount.add, SignedCount.toRaw]
    rw [add_comm_counting a.neg b.neg]

/-- The raw tally underlying normalized signed-count addition carries the same
signed value as the componentwise raw sum. -/
theorem addCount_sound (a b : SignedCount) :
    RawEquivalent
      (SignedCount.toRaw (SignedCount.addCount a b))
      (RawCount.add (SignedCount.toRaw a) (SignedCount.toRaw b)) := by
  unfold SignedCount.addCount
  exact normalize_sound (RawCount.add (SignedCount.toRaw a) (SignedCount.toRaw b))

/-- The raw tally underlying normalized signed-count subtraction carries the
same signed value as raw addition against the raw negation. -/
theorem subCount_sound (a b : SignedCount) :
    RawEquivalent
      (SignedCount.toRaw (SignedCount.subCount a b))
      (RawCount.add (SignedCount.toRaw a) (RawCount.negate (SignedCount.toRaw b))) := by
  unfold SignedCount.subCount SignedCount.addCount SignedCount.negate
  exact normalize_sound (RawCount.add (SignedCount.toRaw a) (RawCount.negate (SignedCount.toRaw b)))

/-- Raw equivalence cancels a common raw addend on the left. -/
theorem rawEquivalent_add_left_cancel {r s t : RawCount}
    (h : RawEquivalent (RawCount.add r s) (RawCount.add r t)) : RawEquivalent s t := by
  unfold RawEquivalent at h ⊢
  dsimp [RawCount.add] at h ⊢
  have h' : (r.pos + r.neg) + (s.pos + t.neg) = (r.pos + r.neg) + (t.pos + s.neg) := by
    calc
      (r.pos + r.neg) + (s.pos + t.neg) = (r.pos + s.pos) + (r.neg + t.neg) := by
        exact add_pair_swap_counting r.pos r.neg s.pos t.neg
      _ = (r.pos + t.pos) + (r.neg + s.neg) := h
      _ = (r.pos + r.neg) + (t.pos + s.neg) := by
        exact add_pair_swap_counting r.pos t.pos r.neg s.neg
  exact add_left_cancel_counting h'

/-- Signed-count addition is associative. -/
theorem addCount_assoc (a b c : SignedCount) :
    SignedCount.addCount (SignedCount.addCount a b) c =
      SignedCount.addCount a (SignedCount.addCount b c) := by
  apply signedCount_eq_of_rawEquivalent
  have hleft :
      RawEquivalent
        (SignedCount.toRaw (SignedCount.addCount (SignedCount.addCount a b) c))
        (RawCount.add (RawCount.add (SignedCount.toRaw a) (SignedCount.toRaw b)) (SignedCount.toRaw c)) := by
    have h1 := addCount_sound (SignedCount.addCount a b) c
    have h2 := rawEquivalent_add (addCount_sound a b) (rawEquivalent_refl (SignedCount.toRaw c))
    exact rawEquivalent_trans h1 h2
  have hmid :
      RawEquivalent
        (RawCount.add (RawCount.add (SignedCount.toRaw a) (SignedCount.toRaw b)) (SignedCount.toRaw c))
        (RawCount.add (SignedCount.toRaw a) (RawCount.add (SignedCount.toRaw b) (SignedCount.toRaw c))) := by
    exact rawEquivalent_of_eq
      (RawCount.add_assoc (SignedCount.toRaw a) (SignedCount.toRaw b) (SignedCount.toRaw c))
  have hright :
      RawEquivalent
        (SignedCount.toRaw (SignedCount.addCount a (SignedCount.addCount b c)))
        (RawCount.add (SignedCount.toRaw a) (RawCount.add (SignedCount.toRaw b) (SignedCount.toRaw c))) := by
    have h1 := addCount_sound a (SignedCount.addCount b c)
    have h2 := rawEquivalent_add (rawEquivalent_refl (SignedCount.toRaw a)) (addCount_sound b c)
    exact rawEquivalent_trans h1 h2
  exact rawEquivalent_trans (rawEquivalent_trans hleft hmid) (rawEquivalent_symm hright)

/-- Raw subtraction distributes across raw addition. -/
theorem raw_sub_add_distrib (a b c d : SignedCount) :
    RawCount.add
        (RawCount.add (SignedCount.toRaw a) (SignedCount.toRaw b))
        (RawCount.negate (RawCount.add (SignedCount.toRaw c) (SignedCount.toRaw d)))
      =
    RawCount.add
        (RawCount.add (SignedCount.toRaw a) (RawCount.negate (SignedCount.toRaw c)))
        (RawCount.add (SignedCount.toRaw b) (RawCount.negate (SignedCount.toRaw d))) := by
  apply RawCount.ext
  · dsimp [RawCount.add, RawCount.negate, SignedCount.toRaw]
    exact add_pair_swap_counting a.pos b.pos c.neg d.neg
  · dsimp [RawCount.add, RawCount.negate, SignedCount.toRaw]
    exact add_pair_swap_counting a.neg b.neg c.pos d.pos

/-- Signed-count subtraction distributes across signed-count addition. -/
theorem subCount_add_distrib (a b c d : SignedCount) :
    SignedCount.subCount (SignedCount.addCount a b) (SignedCount.addCount c d)
      =
    SignedCount.addCount (SignedCount.subCount a c) (SignedCount.subCount b d) := by
  apply signedCount_eq_of_rawEquivalent
  have hleft :
      RawEquivalent
        (SignedCount.toRaw (SignedCount.subCount (SignedCount.addCount a b) (SignedCount.addCount c d)))
        (RawCount.add
          (RawCount.add (SignedCount.toRaw a) (SignedCount.toRaw b))
          (RawCount.negate (RawCount.add (SignedCount.toRaw c) (SignedCount.toRaw d)))) := by
    have h1 := subCount_sound (SignedCount.addCount a b) (SignedCount.addCount c d)
    have h2 := rawEquivalent_add
      (addCount_sound a b)
      (rawEquivalent_negate (addCount_sound c d))
    exact rawEquivalent_trans h1 h2
  have hright :
      RawEquivalent
        (SignedCount.toRaw (SignedCount.addCount (SignedCount.subCount a c) (SignedCount.subCount b d)))
        (RawCount.add
          (RawCount.add (SignedCount.toRaw a) (RawCount.negate (SignedCount.toRaw c)))
          (RawCount.add (SignedCount.toRaw b) (RawCount.negate (SignedCount.toRaw d)))) := by
    have h1 := addCount_sound (SignedCount.subCount a c) (SignedCount.subCount b d)
    have h2 := rawEquivalent_add
      (subCount_sound a c)
      (subCount_sound b d)
    exact rawEquivalent_trans h1 h2
  have hmid :
      RawEquivalent
        (RawCount.add
          (RawCount.add (SignedCount.toRaw a) (SignedCount.toRaw b))
          (RawCount.negate (RawCount.add (SignedCount.toRaw c) (SignedCount.toRaw d))))
        (RawCount.add
          (RawCount.add (SignedCount.toRaw a) (RawCount.negate (SignedCount.toRaw c)))
          (RawCount.add (SignedCount.toRaw b) (RawCount.negate (SignedCount.toRaw d)))) := by
    exact rawEquivalent_of_eq (raw_sub_add_distrib a b c d)
  exact rawEquivalent_trans (rawEquivalent_trans hleft hmid) (rawEquivalent_symm hright)

/-- Signed-count subtraction by zero does nothing. -/
theorem subCount_zero (a : SignedCount) : SignedCount.subCount a SignedCount.zero = a := by
  unfold SignedCount.subCount SignedCount.negate
  change SignedCount.addCount a SignedCount.zero = a
  exact SignedCount.addCount_zero a

/-- Adding a signed count to its negation yields zero. -/
theorem addCount_negate_right (a : SignedCount) :
    SignedCount.addCount a (SignedCount.negate a) = SignedCount.zero := by
  apply signedCount_eq_of_rawEquivalent
  have h1 :
      RawEquivalent
        (SignedCount.toRaw (SignedCount.addCount a (SignedCount.negate a)))
        (RawCount.add (SignedCount.toRaw a) (SignedCount.toRaw (SignedCount.negate a))) := by
    exact addCount_sound a (SignedCount.negate a)
  have h2 :
      RawEquivalent
        (RawCount.add (SignedCount.toRaw a) (SignedCount.toRaw (SignedCount.negate a)))
        (RawCount.add (SignedCount.toRaw a) (RawCount.negate (SignedCount.toRaw a))) := by
    exact rawEquivalent_of_eq rfl
  have h3 :
      RawEquivalent
        (RawCount.add (SignedCount.toRaw a) (RawCount.negate (SignedCount.toRaw a)))
        RawCount.zero := by
    have hswap :
        RawEquivalent
          (RawCount.add (SignedCount.toRaw a) (RawCount.negate (SignedCount.toRaw a)))
          (RawCount.add (RawCount.negate (SignedCount.toRaw a)) (SignedCount.toRaw a)) := by
      apply rawEquivalent_of_eq
      apply RawCount.ext
      · dsimp [RawCount.add, RawCount.negate, SignedCount.toRaw]
        rw [add_comm_counting a.pos a.neg]
      · dsimp [RawCount.add, RawCount.negate, SignedCount.toRaw]
        rw [add_comm_counting a.neg a.pos]
    exact rawEquivalent_trans hswap (rawEquivalent_neg_add_zero (SignedCount.toRaw a))
  exact rawEquivalent_trans (rawEquivalent_trans h1 h2) h3

/-- Adding the negation of a signed count on the left yields zero. -/
theorem addCount_negate_left (a : SignedCount) :
    SignedCount.addCount (SignedCount.negate a) a = SignedCount.zero := by
  rw [addCount_comm]
  exact addCount_negate_right a

/-- Signed-count subtraction followed by adding back the subtrahend recovers the
original signed count. -/
theorem addCount_subCount_cancel_right (a b : SignedCount) :
    SignedCount.addCount (SignedCount.subCount a b) b = a := by
  apply signedCount_eq_of_rawEquivalent
  have h1 :
      RawEquivalent
        (SignedCount.toRaw (SignedCount.addCount (SignedCount.subCount a b) b))
        (RawCount.add (SignedCount.toRaw (SignedCount.subCount a b)) (SignedCount.toRaw b)) := by
    exact addCount_sound (SignedCount.subCount a b) b
  have h2 :
      RawEquivalent
        (RawCount.add (SignedCount.toRaw (SignedCount.subCount a b)) (SignedCount.toRaw b))
        (RawCount.add
          (RawCount.add (SignedCount.toRaw a) (RawCount.negate (SignedCount.toRaw b)))
          (SignedCount.toRaw b)) := by
    exact rawEquivalent_add (subCount_sound a b) (rawEquivalent_refl (SignedCount.toRaw b))
  have h3 :
      RawEquivalent
        (RawCount.add
          (RawCount.add (SignedCount.toRaw a) (RawCount.negate (SignedCount.toRaw b)))
          (SignedCount.toRaw b))
        (RawCount.add
          (SignedCount.toRaw a)
          (RawCount.add (RawCount.negate (SignedCount.toRaw b)) (SignedCount.toRaw b))) := by
    exact rawEquivalent_of_eq
      (RawCount.add_assoc (SignedCount.toRaw a) (RawCount.negate (SignedCount.toRaw b)) (SignedCount.toRaw b))
  have h4 :
      RawEquivalent
        (RawCount.add
          (SignedCount.toRaw a)
          (RawCount.add (RawCount.negate (SignedCount.toRaw b)) (SignedCount.toRaw b)))
        (RawCount.add (SignedCount.toRaw a) RawCount.zero) := by
    exact rawEquivalent_add (rawEquivalent_refl (SignedCount.toRaw a))
      (rawEquivalent_neg_add_zero (SignedCount.toRaw b))
  have h5 :
      RawEquivalent
        (RawCount.add (SignedCount.toRaw a) RawCount.zero)
        (SignedCount.toRaw a) := by
    exact rawEquivalent_of_eq (RawCount.add_zero (SignedCount.toRaw a))
  exact rawEquivalent_trans (rawEquivalent_trans (rawEquivalent_trans (rawEquivalent_trans h1 h2) h3) h4) h5

/-- Signed-count subtraction followed by adding back the subtrahend on the left
also recovers the original signed count. -/
theorem addCount_subCount_cancel_left (a b : SignedCount) :
    SignedCount.addCount b (SignedCount.subCount a b) = a := by
  rw [addCount_comm]
  exact addCount_subCount_cancel_right a b

/-- Signed-count addition cancels a common left summand. -/
theorem addCount_left_cancel {a b c : SignedCount}
    (h : SignedCount.addCount a b = SignedCount.addCount a c) : b = c := by
  apply signedCount_eq_of_rawEquivalent
  have hraw :
      RawEquivalent
        (SignedCount.toRaw (SignedCount.addCount a b))
        (SignedCount.toRaw (SignedCount.addCount a c)) := by
    exact rawEquivalent_of_eq (congrArg SignedCount.toRaw h)
  have hleft :
      RawEquivalent
        (RawCount.add (SignedCount.toRaw a) (SignedCount.toRaw b))
        (RawCount.add (SignedCount.toRaw a) (SignedCount.toRaw c)) := by
    have hab : RawEquivalent
        (RawCount.add (SignedCount.toRaw a) (SignedCount.toRaw b))
        (SignedCount.toRaw (SignedCount.addCount a b)) := by
      exact rawEquivalent_symm (addCount_sound a b)
    have hac : RawEquivalent
        (SignedCount.toRaw (SignedCount.addCount a c))
        (RawCount.add (SignedCount.toRaw a) (SignedCount.toRaw c)) := by
      exact addCount_sound a c
    exact rawEquivalent_trans (rawEquivalent_trans hab hraw) hac
  exact rawEquivalent_add_left_cancel hleft

/-- Signed-count addition cancels a common right summand. -/
theorem addCount_right_cancel {a b c : SignedCount}
    (h : SignedCount.addCount b a = SignedCount.addCount c a) : b = c := by
  rw [addCount_comm b a, addCount_comm c a] at h
  exact addCount_left_cancel h

/-- A zero sum identifies one summand as the negation of the other. -/
theorem eq_negate_of_addCount_eq_zero {a b : SignedCount}
    (h : SignedCount.addCount a b = SignedCount.zero) : a = SignedCount.negate b := by
  have h' : SignedCount.addCount a b = SignedCount.addCount (SignedCount.negate b) b := by
    rw [h, addCount_negate_left]
  exact addCount_right_cancel h'

end CoherenceCalculus
