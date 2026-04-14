import CoherenceCalculus.Foundation.DyadicContinuumCore

/-!
# Foundation.BinaryWordCore

Primitive finite binary words.

This module introduces a direct finite binary-word syntax beneath the dyadic
cell layer. The goal is to support explicit finite address comparison without
relying on theorem wrappers over the more abstract `DyadicCell` interface.
-/

namespace CoherenceCalculus

/-- Explicit finite binary words of fixed length. -/
inductive BinaryWord : Nat → Type where
  | nil : BinaryWord 0
  | snoc : BinaryWord n → BinaryDigit → BinaryWord (n + 1)

/-- Interpret a finite binary word as the corresponding dyadic cell. -/
def BinaryWord.toDyadicCell : {n : Nat} → BinaryWord n → DyadicCell n
  | 0, .nil => rootDyadicCell
  | _ + 1, .snoc w b => refineDyadicCell (w.toDyadicCell) b

/-- Numeric address index of a finite binary word on the depth-`n` mesh. -/
def binaryWordIndex : {n : Nat} → BinaryWord n → Nat
  | 0, .nil => 0
  | _ + 1, .snoc w BinaryDigit.left => 2 * binaryWordIndex w
  | _ + 1, .snoc w BinaryDigit.right => 2 * binaryWordIndex w + 1

/-- Appending a left digit doubles the binary-word index. -/
theorem binaryWordIndex_snoc_left (w : BinaryWord n) :
    binaryWordIndex (BinaryWord.snoc w BinaryDigit.left) = 2 * binaryWordIndex w := by
  rfl

/-- Appending a right digit doubles the binary-word index and adds one. -/
theorem binaryWordIndex_snoc_right (w : BinaryWord n) :
    binaryWordIndex (BinaryWord.snoc w BinaryDigit.right) = 2 * binaryWordIndex w + 1 := by
  rfl

/-- For a fixed prefix, appending a left digit yields a smaller binary-word
index than appending a right digit. -/
theorem binaryWordIndex_snoc_left_lt_right (w : BinaryWord n) :
    binaryWordIndex (BinaryWord.snoc w BinaryDigit.left) <
      binaryWordIndex (BinaryWord.snoc w BinaryDigit.right) := by
  rw [binaryWordIndex_snoc_left, binaryWordIndex_snoc_right]
  exact Nat.lt_succ_self _

/-- Strict binary-word index order is preserved when both words are extended by
one more binary digit. -/
theorem binaryWordIndex_snoc_lt_snoc {n : Nat}
    {u v : BinaryWord n} {b₁ b₂ : BinaryDigit}
    (h : binaryWordIndex u < binaryWordIndex v) :
    binaryWordIndex (BinaryWord.snoc u b₁) <
      binaryWordIndex (BinaryWord.snoc v b₂) := by
  cases b₁ <;> cases b₂
  · rw [binaryWordIndex_snoc_left, binaryWordIndex_snoc_left]
    exact Nat.mul_lt_mul_of_pos_left h (by decide)
  · rw [binaryWordIndex_snoc_left, binaryWordIndex_snoc_right]
    exact Nat.lt_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_left h (by decide))
      (Nat.le_succ _)
  · rw [binaryWordIndex_snoc_right, binaryWordIndex_snoc_left]
    exact Nat.lt_of_lt_of_le
      (by
        have hstep : 2 * binaryWordIndex u + 1 < 2 * binaryWordIndex u + 2 := by
          exact Nat.lt_succ_self _
        exact hstep)
      (by
        have hs : binaryWordIndex u + 1 ≤ binaryWordIndex v := Nat.succ_le_of_lt h
        calc
          2 * binaryWordIndex u + 2 = 2 * (binaryWordIndex u + 1) := by
            simp [Nat.mul_add]
          _ ≤ 2 * binaryWordIndex v := Nat.mul_le_mul_left 2 hs)
  · rw [binaryWordIndex_snoc_right, binaryWordIndex_snoc_right]
    have hmul : 2 * binaryWordIndex u < 2 * binaryWordIndex v := by
      exact Nat.mul_lt_mul_of_pos_left h (by decide)
    exact Nat.succ_lt_succ hmul

end CoherenceCalculus
