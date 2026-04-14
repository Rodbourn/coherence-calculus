import CoherenceCalculus.Foundation.DyadicIntervalCore

/-!
# Foundation.DyadicAddressCore

Explicit finite dyadic addresses.

This module assigns a concrete mesh index to each dyadic cell directly through
the bedrock `PartialChoice` presentation. It avoids introducing a new public
address object: the finite address is extracted from the existing dyadic cell,
and the resulting index is tied back to the exact endpoints of the induced
dyadic interval.
-/

namespace CoherenceCalculus

/-- Numeric address of a dyadic cell on the stage-`n` mesh. -/
def dyadicCellIndex : {n : Nat} → DyadicCell n → Nat
  | 0, PartialChoice.nil => 0
  | _ + 1, PartialChoice.snoc c BinaryDigit.left => 2 * dyadicCellIndex c
  | _ + 1, PartialChoice.snoc c BinaryDigit.right => 2 * dyadicCellIndex c + 1

/-- Refining a dyadic cell to the left doubles its address index. -/
theorem dyadicCellIndex_refine_left {n : Nat} (c : DyadicCell n) :
    dyadicCellIndex (refineDyadicCell c BinaryDigit.left) = 2 * dyadicCellIndex c := by
  rfl

/-- Refining a dyadic cell to the right doubles its address index and adds one. -/
theorem dyadicCellIndex_refine_right {n : Nat} (c : DyadicCell n) :
    dyadicCellIndex (refineDyadicCell c BinaryDigit.right) = 2 * dyadicCellIndex c + 1 := by
  rfl

/-- At fixed parent cell, the left child address strictly precedes the right
child address. -/
theorem dyadicCellIndex_refine_left_lt_right {n : Nat} (c : DyadicCell n) :
    dyadicCellIndex (refineDyadicCell c BinaryDigit.left) <
      dyadicCellIndex (refineDyadicCell c BinaryDigit.right) := by
  rw [dyadicCellIndex_refine_left, dyadicCellIndex_refine_right]
  exact Nat.lt_succ_self _

/-- The interval induced by a dyadic cell starts exactly at that cell's address
index. -/
theorem intervalOfCell_leftIndex_eq_index : {n : Nat} → (c : DyadicCell n) →
    (intervalOfCell c).leftIndex = dyadicCellIndex c
  | 0, PartialChoice.nil => rfl
  | _ + 1, PartialChoice.snoc c BinaryDigit.left => by
      calc
        (intervalOfCell (PartialChoice.snoc c BinaryDigit.left)).leftIndex
            = (leftChildInterval (intervalOfCell c)).leftIndex := by
                rfl
        _ = 2 * (intervalOfCell c).leftIndex := by
              rfl
        _ = 2 * dyadicCellIndex c := by
              rw [intervalOfCell_leftIndex_eq_index c]
  | _ + 1, PartialChoice.snoc c BinaryDigit.right => by
      calc
        (intervalOfCell (PartialChoice.snoc c BinaryDigit.right)).leftIndex
            = (rightChildInterval (intervalOfCell c)).leftIndex := by
                rfl
        _ = 2 * (intervalOfCell c).leftIndex + 1 := by
              rfl
        _ = 2 * dyadicCellIndex c + 1 := by
              rw [intervalOfCell_leftIndex_eq_index c]

/-- The interval induced by a dyadic cell ends one mesh step past that cell's
address index. -/
theorem intervalOfCell_rightIndex_eq_index_succ {n : Nat} (c : DyadicCell n) :
    (intervalOfCell c).rightIndex = dyadicCellIndex c + 1 := by
  rw [(intervalOfCell c).unit_width, intervalOfCell_leftIndex_eq_index]

/-- Every dyadic cell address stays strictly inside the stage mesh. -/
theorem dyadicCellIndex_lt_powTwo {n : Nat} (c : DyadicCell n) :
    dyadicCellIndex c < powTwo n := by
  have hbound : dyadicCellIndex c + 1 ≤ powTwo n := by
    calc
      dyadicCellIndex c + 1 = (intervalOfCell c).rightIndex := by
        rw [intervalOfCell_rightIndex_eq_index_succ]
      _ ≤ powTwo n := (intervalOfCell c).right_bound
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hbound

end CoherenceCalculus
