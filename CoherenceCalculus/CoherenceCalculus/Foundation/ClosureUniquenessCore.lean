import CoherenceCalculus.Foundation.ClosureTransportCore

/-!
# Foundation.ClosureUniquenessCore

Uniqueness of the realized closure tower and boundary.

The transport layer shows that the rebuilt `State` language is only a wrapper
around the closure-forced four-grade realization. This module goes one step
further: once the grade-cut and grade-lowering laws are fixed, the canonical
realized horizon tower and full boundary are uniquely determined.
-/

namespace CoherenceCalculus

/-- A closure-state projection family is admissible when it acts by the forced
grade cutoff on each coordinate. -/
def HasClosureProjectionLaw (P : Nat → ClosureState → ClosureState) : Prop :=
  ∀ h x,
    (P h x).g0 = keepBelow (decide (0 < h)) x.g0 ∧
    (P h x).g1 = keepBelow (decide (1 < h)) x.g1 ∧
    (P h x).g2 = keepBelow (decide (2 < h)) x.g2 ∧
    (P h x).g3 = keepBelow (decide (3 < h)) x.g3

/-- A closure-state boundary is admissible when it lowers odd grades and kills
even grades. -/
def HasClosureBoundaryLaw (d : ClosureState → ClosureState) : Prop :=
  ∀ x,
    (d x).g0 = x.g1 ∧
    (d x).g1 = SignedCount.zero ∧
    (d x).g2 = x.g3 ∧
    (d x).g3 = SignedCount.zero

/-- The canonical closure-state projection family satisfies the forced
grade-cut law. -/
theorem closureProjectionState_has_law : HasClosureProjectionLaw closureProjectionState := by
  intro h x
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- The canonical closure-state boundary satisfies the forced grade-lowering
law. -/
theorem closureBoundaryState_has_law : HasClosureBoundaryLaw closureBoundaryState := by
  intro x
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- Any admissible closure-state projection family is the canonical one. -/
theorem closureProjectionState_unique
    {P : Nat → ClosureState → ClosureState} (hP : HasClosureProjectionLaw P) :
    ∀ h x, P h x = closureProjectionState h x := by
  intro h x
  obtain ⟨h0, h1, h2, h3⟩ := hP h x
  apply ClosureState.ext
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- Any admissible closure-state boundary is the canonical one. -/
theorem closureBoundaryState_unique
    {d : ClosureState → ClosureState} (hd : HasClosureBoundaryLaw d) :
    ∀ x, d x = closureBoundaryState x := by
  intro x
  obtain ⟨h0, h1, h2, h3⟩ := hd x
  apply ClosureState.ext
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- A state-level projection family is closure-realized when it transports to
the forced closure-state grade cut. -/
def RealizesClosureProjectionTransport (P : Nat → State → State) : Prop :=
  ∀ h x,
    closureCoordinates (P h x) = closureProjectionState h (closureCoordinates x)

/-- A state-level boundary is closure-realized when it transports to the forced
closure-state boundary. -/
def RealizesClosureBoundaryTransport (d : State → State) : Prop :=
  ∀ x, closureCoordinates (d x) = closureBoundaryState (closureCoordinates x)

/-- The canonical transported projection satisfies the closure transport law. -/
theorem closureTower_projection_has_transport_law :
    RealizesClosureProjectionTransport (fun h x => (closureTower.π h).toFun x) := by
  intro h x
  apply ClosureState.ext
  · rfl
  · rfl
  · rfl
  · rfl

/-- The canonical full boundary satisfies the closure transport law. -/
theorem trueBoundary_has_transport_law :
    RealizesClosureBoundaryTransport trueBoundary := by
  intro x
  apply ClosureState.ext
  · rfl
  · rfl
  · rfl
  · rfl

/-- Any state-level projection family realizing the closure transport law agrees
pointwise with the canonical closure tower. -/
theorem closureTower_projection_unique
    {P : Nat → State → State} (hP : RealizesClosureProjectionTransport P) :
    ∀ h x, P h x = (closureTower.π h).toFun x := by
  intro h x
  apply State.ext
  · have hcoord := congrArg ClosureState.g0 (hP h x)
    simpa [closureCoordinates, closureProjectionState] using hcoord
  · have hcoord := congrArg ClosureState.g1 (hP h x)
    simpa [closureCoordinates, closureProjectionState] using hcoord
  · have hcoord := congrArg ClosureState.g2 (hP h x)
    simpa [closureCoordinates, closureProjectionState] using hcoord
  · have hcoord := congrArg ClosureState.g3 (hP h x)
    simpa [closureCoordinates, closureProjectionState] using hcoord

/-- Any state-level boundary realizing the closure transport law agrees
pointwise with the canonical full boundary. -/
theorem trueBoundary_unique
    {d : State → State} (hd : RealizesClosureBoundaryTransport d) :
    ∀ x, d x = trueBoundary x := by
  intro x
  apply State.ext
  · have hcoord := congrArg ClosureState.g0 (hd x)
    simpa [closureCoordinates, closureBoundaryState, trueBoundary] using hcoord
  · have hcoord := congrArg ClosureState.g1 (hd x)
    simpa [closureCoordinates, closureBoundaryState, trueBoundary] using hcoord
  · have hcoord := congrArg ClosureState.g2 (hd x)
    simpa [closureCoordinates, closureBoundaryState, trueBoundary] using hcoord
  · have hcoord := congrArg ClosureState.g3 (hd x)
    simpa [closureCoordinates, closureBoundaryState, trueBoundary] using hcoord

end CoherenceCalculus
