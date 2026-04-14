import CoherenceCalculus.Foundation.DyadicIntervalCore

/-!
# Foundation.DyadicPointCore

Dyadic point-candidates as shrinking interval threads.

This layer does not yet quotient binary ambiguities such as
`0.01111... = 0.10000...`. It isolates the pre-real notion of a point on the
unit line: a coherent nested thread of dyadic intervals whose mesh refines
without bound.
-/

namespace CoherenceCalculus

/-- A dyadic unit-point candidate is a shrinking interval thread on the unit
line. -/
abbrev DyadicUnitPoint : Type := DyadicIntervalThread

/-- The left child sits inside its parent after rescaling the parent to the
next mesh. -/
theorem leftChild_nested_scaled (I : DyadicInterval n) :
    2 * I.leftIndex ≤ (leftChildInterval I).leftIndex ∧
    (leftChildInterval I).rightIndex ≤ 2 * I.rightIndex := by
  refine ⟨?_, ?_⟩
  · exact Nat.le_refl _
  · calc
      (leftChildInterval I).rightIndex = 2 * I.leftIndex + 1 := rfl
      _ ≤ 2 * I.leftIndex + 2 := Nat.le_succ _
      _ = 2 * I.rightIndex := by
            rw [I.unit_width, Nat.mul_add]

/-- The right child sits inside its parent after rescaling the parent to the
next mesh. -/
theorem rightChild_nested_scaled (I : DyadicInterval n) :
    2 * I.leftIndex ≤ (rightChildInterval I).leftIndex ∧
    (rightChildInterval I).rightIndex ≤ 2 * I.rightIndex := by
  refine ⟨?_, ?_⟩
  · calc
      2 * I.leftIndex ≤ 2 * I.leftIndex + 1 := Nat.le_succ _
      _ = (rightChildInterval I).leftIndex := rfl
  · exact Nat.le_refl _

/-- Every interval thread is nested under one-step dyadic refinement when
viewed on the common finer mesh. -/
theorem thread_step_nested_scaled (T : DyadicIntervalThread) (n : Nat) :
    2 * (T.intervals n).leftIndex ≤ (T.intervals (n + 1)).leftIndex ∧
    (T.intervals (n + 1)).rightIndex ≤ 2 * (T.intervals n).rightIndex := by
  cases T.refine n with
  | inl hleft =>
      rw [hleft]
      exact leftChild_nested_scaled (T.intervals n)
  | inr hright =>
      rw [hright]
      exact rightChild_nested_scaled (T.intervals n)

/-- Every dyadic point-candidate shrinks by strict mesh refinement at each
stage. -/
theorem unitPoint_mesh_strict (n : Nat) :
    powTwo n < powTwo (n + 1) := by
  exact powTwo_lt_step n

/-- Every binary sequence determines a dyadic unit-point candidate. -/
def unitPointOfDigits (digits : Nat → BinaryDigit) : DyadicUnitPoint :=
  intervalThreadOfDigits digits

/-- The intervals attached directly to a binary sequence are nested under one
step of dyadic refinement. -/
theorem intervalsOfDigits_nested_scaled (digits : Nat → BinaryDigit) (n : Nat) :
    2 * (intervalsOfDigits digits n).leftIndex
      ≤ (intervalsOfDigits digits (n + 1)).leftIndex ∧
    (intervalsOfDigits digits (n + 1)).rightIndex
      ≤ 2 * (intervalsOfDigits digits n).rightIndex := by
  cases h : digits n with
  | left =>
      simp [intervalsOfDigits, h]
      exact leftChild_nested_scaled (intervalsOfDigits digits n)
  | right =>
      simp [intervalsOfDigits, h]
      exact rightChild_nested_scaled (intervalsOfDigits digits n)

/-- A canonical left-branch unit-point candidate exists. -/
def leftUnitPoint : DyadicUnitPoint :=
  unitPointOfDigits (fun _ => BinaryDigit.left)

end CoherenceCalculus
