import CoherenceCalculus.Foundation.CoherenceTowerCore
import CoherenceCalculus.Foundation.DiophantineWidth
import CoherenceCalculus.Foundation.ClosureClassificationCore

/-!
# Foundation.ClosureRealizationCore

Closure-driven realization of the canonical fourfold coherence model.

This module strengthens the foundation story for Part I / Part II by showing
that the active finite state/tower model is not merely convenient. It is the
canonical realization obtained by:

- taking the nontrivial stable closure dimension `D = 4`,
- using those four grades as the visible coordinate layers,
- and cutting observation by grade cutoff.

The result does not yet derive every higher structure from closure alone, but it
does remove arbitrariness from the finite state layering and from the canonical
horizon tower used in the realized HFT statements.
-/

namespace CoherenceCalculus

/-- The active coherence model uses the nontrivial stable closure dimension. -/
def closureStableDimension : Nat := 4

/-- The realized coherence dimension is closure-stable. -/
theorem closureStableDimension_stable : isStable closureStableDimension := by
  exact stable_D4

/-- The realized coherence dimension is strictly beyond the trivial stable case
`D = 2`. -/
theorem closureStableDimension_nontrivial : 2 < closureStableDimension := by
  decide

/-- In the low-dimensional closure range, stability occurs only at the trivial
dimension `2` and at the realized nontrivial dimension `4`. -/
theorem stable_dimension_upto_four
    {D : Nat} (hD : D ≤ 4) (hstable : isStable D) :
    D = 2 ∨ D = closureStableDimension := by
  cases D with
  | zero =>
      exfalso
      exact not_stable_D0 hstable
  | succ D =>
      cases D with
      | zero =>
          exfalso
          exact not_stable_D1 hstable
      | succ D =>
          cases D with
          | zero =>
              exact Or.inl rfl
          | succ D =>
              cases D with
              | zero =>
                  exfalso
                  exact not_stable_D3 hstable
              | succ D =>
                  cases D with
                  | zero =>
                      exact Or.inr rfl
                  | succ D =>
                      exfalso
                      change D + 5 ≤ 4 at hD
                      have h54 : 5 ≤ 4 := by
                        exact Nat.le_trans
                          (Nat.le_add_left 5 D)
                          hD
                      have hcontra : ¬ 5 ≤ 4 := Nat.not_succ_le_self 4
                      exact hcontra h54

/-- The nontrivial stable closure dimension in the low-dimensional closure range
is forced to be the realized fourfold dimension. -/
theorem closureStableDimension_forced
    {D : Nat} (hD : D ≤ 4) (hstable : isStable D) (hnontrivial : 2 < D) :
    D = closureStableDimension := by
  obtain h2 | h4 := stable_dimension_upto_four hD hstable
  · exfalso
    rw [h2] at hnontrivial
    exact Nat.lt_irrefl 2 hnontrivial
  · exact h4

/-- Globally, the unique nontrivial closure-stable dimension is the realized
fourfold dimension. -/
theorem closureStableDimension_globally_forced
    {D : Nat} (hstable : isStable D) (hnontrivial : 2 < D) :
    D = closureStableDimension := by
  have hclass := (stable_dimension_classification.mp hstable)
  rcases hclass with h2 | h4
  · exfalso
    rw [h2] at hnontrivial
    exact Nat.lt_irrefl 2 hnontrivial
  · exact h4

/-- The closure-realized four-grade state induced by the stable closure
dimension. -/
structure ClosureState where
  g0 : SignedCount
  g1 : SignedCount
  g2 : SignedCount
  g3 : SignedCount
  deriving DecidableEq, Repr

/-- Read a rebuilt state as its closure-grade coordinate assignment. -/
def closureCoordinates (x : State) : ClosureState :=
  ⟨x.c0, x.c1, x.c2, x.c3⟩

/-- Package closure-grade coordinates back into the rebuilt finite state. -/
def stateFromClosureCoordinates (x : ClosureState) : State :=
  ⟨x.g0, x.g1, x.g2, x.g3⟩

/-- The rebuilt state is exactly the closure-grade realization. -/
theorem state_from_closureCoordinates (x : State) :
    stateFromClosureCoordinates (closureCoordinates x) = x := by
  apply State.ext <;> rfl

/-- Grade-cut projection induced by the closure-realized layering. -/
def closureProjectionFromCounting (h : Nat) (x : State) : State :=
  stateFromClosureCoordinates
    { g0 := keepBelow (decide (0 < h)) (closureCoordinates x).g0
      g1 := keepBelow (decide (1 < h)) (closureCoordinates x).g1
      g2 := keepBelow (decide (2 < h)) (closureCoordinates x).g2
      g3 := keepBelow (decide (3 < h)) (closureCoordinates x).g3 }

/-- The current canonical coherence projection is exactly the grade-cut
projection induced by the closure-realized fourfold layering. -/
theorem closureProjection_realizes_coherenceProjection (h : Nat) (x : State) :
    closureProjectionFromCounting h x = coherenceProjectionFun h x := by
  apply State.ext <;> rfl

/-- The closure-realized grade-cut map packaged as a projection. -/
def closureProjection (h : Nat) : Projection where
  toFun := closureProjectionFromCounting h
  map_add := by
    intro x y
    rw [closureProjection_realizes_coherenceProjection,
      closureProjection_realizes_coherenceProjection,
      closureProjection_realizes_coherenceProjection]
    exact (coherenceProjection h).map_add x y
  map_zero := by
    rw [closureProjection_realizes_coherenceProjection]
    exact (coherenceProjection h).map_zero
  idem := by
    intro x
    rw [closureProjection_realizes_coherenceProjection]
    exact (coherenceProjection h).idem x

/-- The closure-realized projection agrees pointwise with the canonical
coherence projection. -/
theorem closureProjection_apply (h : Nat) (x : State) :
    (closureProjection h).toFun x = (coherenceProjection h).toFun x := by
  exact closureProjection_realizes_coherenceProjection h x

/-- The closure-realized projection becomes the identity after the stable
dimension is fully visible. -/
theorem closureProjection_after_stable_dimension (h : Nat) (x : State) :
    closureProjectionFromCounting (h + closureStableDimension) x = x := by
  rw [closureProjection_realizes_coherenceProjection]
  simpa [closureStableDimension] using coherenceProjection_after_four h x

/-- The closure-realized shadow vanishes after the stable dimension is fully
visible. -/
theorem closureShadow_after_stable_dimension (h : Nat) (x : State) :
    State.sub x (closureProjectionFromCounting (h + closureStableDimension) x) =
      State.zero := by
  rw [closureProjection_after_stable_dimension]
  exact State.sub_self x

/-- The active canonical tower is the tower induced by closure-realized grade
cuts. -/
theorem coherenceTower_is_closure_realized (h : Nat) (x : State) :
    (coherenceTower.π h).toFun x = closureProjectionFromCounting h x := by
  rw [closureProjection_realizes_coherenceProjection]
  rfl

/-- The closure-realized canonical horizon tower. -/
def closureTower : HorizonTower where
  π := closureProjection
  nested := by
    intro h₁ h₂ hle x
    rw [closureProjection_apply, closureProjection_apply]
    exact coherenceTower.nested h₁ h₂ hle x
  nested_ge := by
    intro h₁ h₂ hle x
    rw [closureProjection_apply, closureProjection_apply]
    exact coherenceTower.nested_ge h₁ h₂ hle x

/-- The closure-realized tower agrees pointwise with the canonical coherence
tower. -/
theorem closureTower_apply (h : Nat) (x : State) :
    (closureTower.π h).toFun x = (coherenceTower.π h).toFun x := by
  exact closureProjection_apply h x

/-- On closure grades, the true boundary lowers odd layers and annihilates even
layers. -/
def closureBoundaryFromCounting (x : State) : State :=
  stateFromClosureCoordinates
    { g0 := (closureCoordinates x).g1
      g1 := SignedCount.zero
      g2 := (closureCoordinates x).g3
      g3 := SignedCount.zero }

/-- The rebuilt full boundary is exactly the closure-grade lowering map. -/
theorem closureBoundary_realizes_trueBoundary (x : State) :
    closureBoundaryFromCounting x = trueBoundary x := by
  apply State.ext <;> rfl

/-- The closure-grade lowering map closes on itself. -/
theorem closureBoundary_closes (x : State) :
    closureBoundaryFromCounting (closureBoundaryFromCounting x) = State.zero := by
  rw [closureBoundary_realizes_trueBoundary, closureBoundary_realizes_trueBoundary]
  exact fullBoundary_closes x

/-- The closure-realized tower satisfies the exact Pythagorean split. -/
def closureEnergyTower : EnergyHorizonTower where
  toHorizonTower := closureTower
  pythagorean_split := by
    intro h x
    have hproj :
        (closureTower.π h).toFun x = (coherenceTower.π h).toFun x := closureTower_apply h x
    have hshadow :
        shadowProj closureTower h x = shadowProj coherenceTower h x := by
      unfold shadowProj
      rw [hproj]
    rw [hproj, hshadow]
    exact coherenceEnergyTower.pythagorean_split h x

/-- The closure-realized tower is faithful after the stable dimension becomes
fully visible. -/
def closureFaithfulTower : FaithfulEnergyTower where
  toEnergyHorizonTower := closureEnergyTower
  tail_energy_eventually_zero := by
    intro x h₀
    refine ⟨4, ?_⟩
    change State.energy (shadowProj closureTower (h₀ + 4) x) = 0
    have hshadow :
        shadowProj closureTower (h₀ + 4) x = shadowProj coherenceTower (h₀ + 4) x := by
      unfold shadowProj
      rw [closureTower_apply]
    rw [hshadow, coherenceShadow_after_four]
    rfl

/-- Closure-realized HFT-1 with no nilpotency premise. -/
theorem HFT1_closure_exact (h : Nat) (x : State) :
    observedBoundary closureTower h (observedBoundary closureTower h x) =
      State.negate (boundaryDefect closureTower h x) := by
  exact HFT1_boundary_exact closureTower h x

/-- Closure-realized finite HFT-2 with no extra tower hypotheses. -/
theorem HFT2_closure_finite
    (x : State) (h₀ : Nat) (hs : List Nat) (hmono : HorizonChain h₀ hs) :
    State.energy (shadowProj closureTower h₀ x) =
      telescopingEnergyChain closureEnergyTower x h₀ hs := by
  exact HFT2_finite_energy closureEnergyTower x h₀ hs hmono

/-- Closure-realized faithful HFT-2 with no extra tower hypotheses. -/
theorem HFT2_closure_stabilized
    (x : State) (h₀ : Nat) :
    ∃ N, ∀ k,
      State.energy (shadowProj closureTower h₀ x) =
        prefixIncrementEnergy closureEnergyTower x h₀ (N + k) := by
  exact HFT2_faithful_stabilized closureFaithfulTower x h₀

end CoherenceCalculus
