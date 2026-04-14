import CoherenceCalculus.Foundation.SignedCount

/-!
# Foundation.RawCountCore

Semantic layer for raw signed tallies.

This module introduces a raw equivalence relation expressing when two tally
pairs encode the same signed quantity, and proves that normalization is sound
with respect to that relation.
-/

namespace CoherenceCalculus

/-- Two raw tally pairs encode the same signed quantity when cross-cancellation
balances. -/
def RawEquivalent (r s : RawCount) : Prop :=
  r.pos + s.neg = s.pos + r.neg

/-- Raw equivalence is reflexive. -/
theorem rawEquivalent_refl (r : RawCount) : RawEquivalent r r := by
  unfold RawEquivalent
  rfl

/-- Raw equivalence is symmetric. -/
theorem rawEquivalent_symm {r s : RawCount} (h : RawEquivalent r s) : RawEquivalent s r := by
  unfold RawEquivalent at h ⊢
  exact h.symm

/-- Raw equivalence is transitive. -/
theorem rawEquivalent_trans {r s t : RawCount}
    (hrs : RawEquivalent r s) (hst : RawEquivalent s t) : RawEquivalent r t := by
  have hsum : r.pos + t.neg + s.neg = t.pos + r.neg + s.neg := by
    calc
      r.pos + t.neg + s.neg = r.pos + (t.neg + s.neg) := by
        rw [add_assoc_counting]
      _ = r.pos + (s.neg + t.neg) := by
        rw [add_comm_counting t.neg s.neg]
      _ = r.pos + s.neg + t.neg := by
        rw [← add_assoc_counting]
      _ = s.pos + r.neg + t.neg := by
        unfold RawEquivalent at hrs
        rw [hrs]
      _ = s.pos + (r.neg + t.neg) := by
        rw [add_assoc_counting]
      _ = s.pos + (t.neg + r.neg) := by
        rw [add_comm_counting r.neg t.neg]
      _ = s.pos + t.neg + r.neg := by
        rw [← add_assoc_counting]
      _ = t.pos + s.neg + r.neg := by
        unfold RawEquivalent at hst
        rw [hst]
      _ = t.pos + (s.neg + r.neg) := by
        rw [add_assoc_counting]
      _ = t.pos + (r.neg + s.neg) := by
        rw [add_comm_counting s.neg r.neg]
      _ = t.pos + r.neg + s.neg := by
        rw [← add_assoc_counting]
  exact add_right_cancel_counting hsum

/-- Normalization is sound: the normalized representative carries the same raw
signed value as the original tally pair. -/
theorem normalize_sound (r : RawCount) :
    RawEquivalent (SignedCount.toRaw (SignedCount.normalize r)) r := by
  unfold RawEquivalent
  by_cases h : r.neg ≤ r.pos
  · rw [SignedCount.normalize_pos_dom _ _ h]
    dsimp [SignedCount.toRaw]
    exact sub_add_cancel_counting h
  · rw [SignedCount.normalize_neg_dom _ _ h]
    dsimp [SignedCount.toRaw]
    rw [zero_add_counting]
    rw [add_comm_counting r.pos (r.neg - r.pos)]
    exact (sub_add_cancel_counting (Nat.le_of_not_ge h)).symm

end CoherenceCalculus
