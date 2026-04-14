import CoherenceCalculus.Foundation.DiophantineWidth
import CoherenceCalculus.Foundation.BedrockContinuationCore

/-!
# Foundation.CountingRealizationCore

Counting-surface wrappers for the chapter-4 closure narrative.

These declarations keep the manuscript-facing counting realization explicit on
the active import-free lane:

- the counting realization of the closure defect on an event
- the zero-defect/balanced-count equivalence on that realized surface
- the distinguished `D = 3` and `D = 4` counting carriers

No new arithmetic or representation machinery is introduced here.
-/

namespace CoherenceCalculus

/-- The counting realization of the closure defect on an event is the
holographic operator evaluated at its dimension. -/
def countingRealizationClosureDefect (e : Event) : SignedCount :=
  holographicOperator (dimensionOfEvent e)

/-- On a pure-dimensional event, the counting realization is exactly the
counting defect at that event's dimension. -/
theorem pure_dimensional_counting_realization (e : Event) :
    countingRealizationClosureDefect e =
      holographicOperator (dimensionOfEvent e) := by
  rfl

/-- On the counting surface, vanishing counting defect forces exact pair/order
count balance. -/
theorem counting_zero_implies_balanced (e : Event) :
    countingRealizationClosureDefect e = SignedCount.zero →
      pairings (dimensionOfEvent e) = orderings (dimensionOfEvent e) := by
  intro hzero
  unfold countingRealizationClosureDefect holographicOperator holographicImbalance at hzero
  unfold SignedCount.subCount SignedCount.addCount SignedCount.ofNat SignedCount.negate at hzero
  dsimp at hzero
  rw [zero_add_counting] at hzero
  unfold SignedCount.normalize at hzero
  by_cases hle : orderings (dimensionOfEvent e) ≤ pairings (dimensionOfEvent e)
  · rw [dif_pos hle] at hzero
    have hsub : pairings (dimensionOfEvent e) - orderings (dimensionOfEvent e) = 0 := by
      exact congrArg SignedCount.pos hzero
    exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hsub) hle
  · rw [dif_neg hle] at hzero
    have hsub : orderings (dimensionOfEvent e) - pairings (dimensionOfEvent e) = 0 := by
      exact congrArg SignedCount.neg hzero
    exact False.elim (hle (Nat.le_of_sub_eq_zero hsub))

/-- Exact pair/order count balance kills the counting realization of the
closure defect. -/
theorem counting_balanced_implies_zero (e : Event) :
    pairings (dimensionOfEvent e) = orderings (dimensionOfEvent e) →
      countingRealizationClosureDefect e = SignedCount.zero := by
  intro hbalanced
  unfold countingRealizationClosureDefect holographicOperator holographicImbalance
  exact SignedCount.subCount_ofNat_eq_zero hbalanced

/-- The minimal nonterminal counting carrier is the residual `D = 3` event. -/
theorem minimal_nonterminal_counting_carrier :
    countingRealizationClosureDefect ⟨3⟩ = SignedCount.ofNat 1 := by
  exact holographicOperator_D3

/-- The first nontrivial terminal counting carrier is the balanced `D = 4`
event. -/
theorem first_nontrivial_terminal_counting_carrier :
    countingRealizationClosureDefect ⟨4⟩ = SignedCount.zero := by
  exact holographicOperator_D4_stable

/-- If the counting realization vanishes exactly when the declared bedrock
closure defect vanishes on a chosen surface, then counting closure reflects
terminality on that surface. -/
theorem counting_realization_reflects_terminality
    {S : IncidenceSystem}
    (T : TerminationData S)
    (e : Event) (I : S.Incidence)
    (hsound :
      countingRealizationClosureDefect e = SignedCount.zero ↔
        T.defect I = T.space.zero) :
    countingRealizationClosureDefect e = SignedCount.zero ↔
      TerminalIncidence S I := by
  constructor
  · intro hzero
    exact zero_defect_implies_terminal T I ((hsound).1 hzero)
  · intro hterminal
    exact (hsound).2 (terminal_implies_zero_defect T I hterminal)

end CoherenceCalculus
