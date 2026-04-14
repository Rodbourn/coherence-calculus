import CoherenceCalculus.Foundation.RawCountCore

/-!
# Foundation.NormalizationCore

Canonicality of normalized signed-count representatives.

This module proves that raw-equivalent normalized signed counts are equal, and
therefore that normalization is congruent with respect to raw equivalence.
-/

namespace CoherenceCalculus

/-- Two normalized signed counts with raw-equivalent tallies are equal. -/
theorem signedCount_eq_of_rawEquivalent
    {a b : SignedCount}
    (h : RawEquivalent (SignedCount.toRaw a) (SignedCount.toRaw b)) : a = b := by
  cases a with
  | mk apos aneg anorm =>
      cases b with
      | mk bpos bneg bnorm =>
          dsimp [SignedCount.toRaw, RawEquivalent] at h
          cases anorm with
          | inl hapos =>
              cases bnorm with
              | inl hbpos =>
                  apply SignedCount.ext
                  · exact hapos.trans hbpos.symm
                  · rw [hapos, hbpos, zero_add_counting, zero_add_counting] at h
                    exact h.symm
              | inr hbneg =>
                  have hsum : bpos + aneg = 0 := by
                    rw [hapos, hbneg] at h
                    calc
                      bpos + aneg = 0 + 0 := h.symm
                      _ = 0 := rfl
                  have hbpos0 : bpos = 0 := add_eq_zero_left_counting hsum
                  have haneg0 : aneg = 0 := add_eq_zero_right_counting hsum
                  apply SignedCount.ext
                  · exact hapos.trans hbpos0.symm
                  · exact haneg0.trans hbneg.symm
          | inr haneg =>
              cases bnorm with
              | inl hbpos =>
                  have hsum : apos + bneg = 0 := by
                    rw [haneg, hbpos] at h
                    calc
                      apos + bneg = 0 + 0 := h
                      _ = 0 := rfl
                  have hapos0 : apos = 0 := add_eq_zero_left_counting hsum
                  have hbneg0 : bneg = 0 := add_eq_zero_right_counting hsum
                  apply SignedCount.ext
                  · exact hapos0.trans hbpos.symm
                  · exact haneg.trans hbneg0.symm
              | inr hbneg =>
                  apply SignedCount.ext
                  · rw [haneg, hbneg, add_zero_counting, add_zero_counting] at h
                    exact h
                  · exact haneg.trans hbneg.symm

/-- Normalization is congruent: raw-equivalent tally pairs normalize to the same
signed count. -/
theorem normalize_congr {r s : RawCount} (h : RawEquivalent r s) :
    SignedCount.normalize r = SignedCount.normalize s := by
  apply signedCount_eq_of_rawEquivalent
  have hr : RawEquivalent (SignedCount.toRaw (SignedCount.normalize r)) r :=
    normalize_sound r
  have hs : RawEquivalent s (SignedCount.toRaw (SignedCount.normalize s)) :=
    rawEquivalent_symm (normalize_sound s)
  exact rawEquivalent_trans (rawEquivalent_trans hr h) hs

end CoherenceCalculus
