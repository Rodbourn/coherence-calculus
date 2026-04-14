import CoherenceCalculus.Foundation.FaithfulTowerCore

/-!
# Foundation.CoherenceTowerCore

Canonical coherence tower on the rebuilt four-grade state space.

Horizon `h` sees exactly those coordinates whose grade index lies strictly below
`h`. Since the rebuilt state has only four coordinates, the tower becomes the
identity from horizon `4` onward. This gives exact energy splitting and exact
faithfulness by construction.
-/

namespace CoherenceCalculus

/-- Keep a signed count if the horizon sees it; otherwise replace it by zero. -/
def keepBelow (visible : Bool) (z : SignedCount) : SignedCount :=
  if visible then z else SignedCount.zero

theorem keepBelow_add (visible : Bool) (a b : SignedCount) :
    keepBelow visible (SignedCount.addCount a b) =
      SignedCount.addCount (keepBelow visible a) (keepBelow visible b) := by
  cases visible with
  | false =>
      change SignedCount.zero =
        SignedCount.addCount SignedCount.zero SignedCount.zero
      exact (SignedCount.zero_addCount SignedCount.zero).symm
  | true =>
      rfl

theorem keepBelow_zero (visible : Bool) :
    keepBelow visible SignedCount.zero = SignedCount.zero := by
  cases visible <;> rfl

theorem keepBelow_idem (visible : Bool) (z : SignedCount) :
    keepBelow visible (keepBelow visible z) = keepBelow visible z := by
  cases visible <;> rfl

theorem keepBelow_nested {b₁ b₂ : Bool}
    (hvis : b₁ = true → b₂ = true) (z : SignedCount) :
    keepBelow b₁ (keepBelow b₂ z) = keepBelow b₁ z := by
  cases b₁ <;> cases b₂
  · rfl
  · rfl
  · cases (hvis rfl)
  · rfl

theorem keepBelow_nested_ge {b₁ b₂ : Bool}
    (hvis : b₂ = true → b₁ = true) (z : SignedCount) :
    keepBelow b₁ (keepBelow b₂ z) = keepBelow b₂ z := by
  cases b₁ <;> cases b₂
  · rfl
  · cases (hvis rfl)
  · rfl
  · rfl

/-- Canonical coherence projection at horizon `h`. -/
def coherenceProjectionFun (h : Nat) (x : State) : State :=
  ⟨keepBelow (decide (0 < h)) x.c0,
   keepBelow (decide (1 < h)) x.c1,
   keepBelow (decide (2 < h)) x.c2,
   keepBelow (decide (3 < h)) x.c3⟩

/-- The canonical coherence projection packaged as a projection. -/
def coherenceProjection (h : Nat) : Projection where
  toFun := coherenceProjectionFun h
  map_add := by
    intro x y
    apply State.ext
    · exact keepBelow_add (decide (0 < h)) x.c0 y.c0
    · exact keepBelow_add (decide (1 < h)) x.c1 y.c1
    · exact keepBelow_add (decide (2 < h)) x.c2 y.c2
    · exact keepBelow_add (decide (3 < h)) x.c3 y.c3
  map_zero := by
    apply State.ext
    · exact keepBelow_zero (decide (0 < h))
    · exact keepBelow_zero (decide (1 < h))
    · exact keepBelow_zero (decide (2 < h))
    · exact keepBelow_zero (decide (3 < h))
  idem := by
    intro x
    apply State.ext
    · exact keepBelow_idem (decide (0 < h)) x.c0
    · exact keepBelow_idem (decide (1 < h)) x.c1
    · exact keepBelow_idem (decide (2 < h)) x.c2
    · exact keepBelow_idem (decide (3 < h)) x.c3

/-- Canonical coherence horizon tower. -/
def coherenceTower : HorizonTower where
  π := coherenceProjection
  nested := by
    intro h₁ h₂ hle x
    apply State.ext
    · exact keepBelow_nested (fun hp => by
        have hp' : 0 < h₁ := of_decide_eq_true hp
        exact decide_eq_true (Nat.lt_of_lt_of_le hp' hle)) x.c0
    · exact keepBelow_nested (fun hp => by
        have hp' : 1 < h₁ := of_decide_eq_true hp
        exact decide_eq_true (Nat.lt_of_lt_of_le hp' hle)) x.c1
    · exact keepBelow_nested (fun hp => by
        have hp' : 2 < h₁ := of_decide_eq_true hp
        exact decide_eq_true (Nat.lt_of_lt_of_le hp' hle)) x.c2
    · exact keepBelow_nested (fun hp => by
        have hp' : 3 < h₁ := of_decide_eq_true hp
        exact decide_eq_true (Nat.lt_of_lt_of_le hp' hle)) x.c3
  nested_ge := by
    intro h₁ h₂ hle x
    apply State.ext
    · exact keepBelow_nested_ge (fun hq => by
        have hq' : 0 < h₂ := of_decide_eq_true hq
        exact decide_eq_true (Nat.lt_of_lt_of_le hq' hle)) x.c0
    · exact keepBelow_nested_ge (fun hq => by
        have hq' : 1 < h₂ := of_decide_eq_true hq
        exact decide_eq_true (Nat.lt_of_lt_of_le hq' hle)) x.c1
    · exact keepBelow_nested_ge (fun hq => by
        have hq' : 2 < h₂ := of_decide_eq_true hq
        exact decide_eq_true (Nat.lt_of_lt_of_le hq' hle)) x.c2
    · exact keepBelow_nested_ge (fun hq => by
        have hq' : 3 < h₂ := of_decide_eq_true hq
        exact decide_eq_true (Nat.lt_of_lt_of_le hq' hle)) x.c3

/-- From horizon `4` onward, coherence projection is the identity. -/
theorem coherenceProjection_after_four (h : Nat) (x : State) :
    coherenceProjectionFun (h + 4) x = x := by
  have h0 : decide (0 < h + 4) = true := by
    apply decide_eq_true
    show 0 < Nat.succ (Nat.succ (Nat.succ (Nat.succ h)))
    exact Nat.zero_lt_succ _
  have h1 : decide (1 < h + 4) = true := by
    apply decide_eq_true
    show Nat.succ 0 < Nat.succ (Nat.succ (Nat.succ (Nat.succ h)))
    exact Nat.succ_lt_succ (Nat.zero_lt_succ _)
  have h2 : decide (2 < h + 4) = true := by
    apply decide_eq_true
    show Nat.succ (Nat.succ 0) < Nat.succ (Nat.succ (Nat.succ (Nat.succ h)))
    exact Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))
  have h3 : decide (3 < h + 4) = true := by
    apply decide_eq_true
    show Nat.succ (Nat.succ (Nat.succ 0)) < Nat.succ (Nat.succ (Nat.succ (Nat.succ h)))
    exact Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _)))
  apply State.ext
  · rw [coherenceProjectionFun, h0]
    rfl
  · rw [coherenceProjectionFun, h1]
    rfl
  · rw [coherenceProjectionFun, h2]
    rfl
  · rw [coherenceProjectionFun, h3]
    rfl

/-- The tower projection at horizon `0` is zero. -/
theorem coherenceProjection_zero (x : State) :
    (coherenceTower.π 0).toFun x = State.zero := by
  rfl

/-- The tower projection at horizon `1` keeps only the first coordinate. -/
theorem coherenceProjection_one (x : State) :
    (coherenceTower.π 1).toFun x =
      ⟨x.c0, SignedCount.zero, SignedCount.zero, SignedCount.zero⟩ := by
  rfl

/-- The tower projection at horizon `2` keeps the first two coordinates. -/
theorem coherenceProjection_two (x : State) :
    (coherenceTower.π 2).toFun x =
      ⟨x.c0, x.c1, SignedCount.zero, SignedCount.zero⟩ := by
  rfl

/-- The tower projection at horizon `3` keeps the first three coordinates. -/
theorem coherenceProjection_three (x : State) :
    (coherenceTower.π 3).toFun x =
      ⟨x.c0, x.c1, x.c2, SignedCount.zero⟩ := by
  rfl

/-- The tower projection is the identity from horizon `4` onward. -/
theorem coherenceProjection_tower_after_four (h : Nat) (x : State) :
    (coherenceTower.π (h + 4)).toFun x = x := by
  change coherenceProjectionFun (h + 4) x = x
  exact coherenceProjection_after_four h x

/-- Horizon `0` sees nothing. -/
theorem coherenceShadow_zero (x : State) :
    shadowProj coherenceTower 0 x = x := by
  change State.sub x State.zero = x
  exact State.sub_zero x

/-- Horizon `1` leaves exactly the last three coordinates in shadow. -/
theorem coherenceShadow_one (x : State) :
    shadowProj coherenceTower 1 x =
      ⟨SignedCount.zero, x.c1, x.c2, x.c3⟩ := by
  apply State.ext
  · exact SignedCount.subCount_self x.c0
  · exact subCount_zero x.c1
  · exact subCount_zero x.c2
  · exact subCount_zero x.c3

/-- Horizon `2` leaves exactly the last two coordinates in shadow. -/
theorem coherenceShadow_two (x : State) :
    shadowProj coherenceTower 2 x =
      ⟨SignedCount.zero, SignedCount.zero, x.c2, x.c3⟩ := by
  apply State.ext
  · exact SignedCount.subCount_self x.c0
  · exact SignedCount.subCount_self x.c1
  · exact subCount_zero x.c2
  · exact subCount_zero x.c3

/-- Horizon `3` leaves exactly the last coordinate in shadow. -/
theorem coherenceShadow_three (x : State) :
    shadowProj coherenceTower 3 x =
      ⟨SignedCount.zero, SignedCount.zero, SignedCount.zero, x.c3⟩ := by
  apply State.ext
  · exact SignedCount.subCount_self x.c0
  · exact SignedCount.subCount_self x.c1
  · exact SignedCount.subCount_self x.c2
  · exact subCount_zero x.c3

/-- From horizon `4` onward, the coherence shadow vanishes. -/
theorem coherenceShadow_after_four (h : Nat) (x : State) :
    shadowProj coherenceTower (h + 4) x = State.zero := by
  change State.sub x (coherenceProjectionFun (h + 4) x) = State.zero
  rw [coherenceProjection_after_four]
  exact State.sub_self x

theorem signedCount_energy_zero :
    SignedCount.energy SignedCount.zero = 0 := by
  rfl

theorem four_term_split_one (a b c d : Nat) :
    ((((a + 0) + 0) + 0) + (((0 + b) + c) + d)) =
      (((a + b) + c) + d) := by
  calc
    ((((a + 0) + 0) + 0) + (((0 + b) + c) + d))
      = ((a + 0) + (((0 + b) + c) + d)) := by
          rw [add_zero_counting ((a + 0) + 0)]
    _ = a + (((0 + b) + c) + d) := by
          rw [add_zero_counting a]
    _ = a + ((b + c) + d) := by
          rw [zero_add_counting b]
    _ = (a + (b + c)) + d := by
          rw [← add_assoc_counting a (b + c) d]
    _ = ((a + b) + c) + d := by
          rw [← add_assoc_counting a b c]

theorem four_term_split_two (a b c d : Nat) :
    ((((a + b) + 0) + 0) + (((0 + 0) + c) + d)) =
      (((a + b) + c) + d) := by
  calc
    ((((a + b) + 0) + 0) + (((0 + 0) + c) + d))
      = (((a + b) + 0) + (((0 + 0) + c) + d)) := by
          rw [add_zero_counting ((a + b) + 0)]
    _ = ((a + b) + (((0 + 0) + c) + d)) := by
          rw [add_zero_counting (a + b)]
    _ = (a + b) + ((0 + c) + d) := by
          rw [zero_add_counting 0]
    _ = (a + b) + (c + d) := by
          rw [zero_add_counting c]
    _ = ((a + b) + c) + d := by
          rw [← add_assoc_counting (a + b) c d]

theorem four_term_split_three (a b c d : Nat) :
    ((((a + b) + c) + 0) + (((0 + 0) + 0) + d)) =
      (((a + b) + c) + d) := by
  calc
    ((((a + b) + c) + 0) + (((0 + 0) + 0) + d))
      = (((a + b) + c) + (((0 + 0) + 0) + d)) := by
          rw [add_zero_counting (((a + b) + c))]
    _ = (((a + b) + c) + ((0 + 0) + d)) := by
          rw [zero_add_counting 0]
    _ = (((a + b) + c) + (0 + d)) := by
          rw [zero_add_counting 0]
    _ = (((a + b) + c) + d) := by
          rw [zero_add_counting d]

/-- The canonical coherence tower satisfies exact Pythagorean splitting. -/
def coherenceEnergyTower : EnergyHorizonTower where
  toHorizonTower := coherenceTower
  pythagorean_split := by
    intro h x
    cases h with
    | zero =>
        rw [coherenceProjection_zero, coherenceShadow_zero]
        have hz : State.energy State.zero = 0 := by
          rfl
        rw [hz, zero_add_counting]
    | succ h =>
        cases h with
        | zero =>
            rw [coherenceProjection_one, coherenceShadow_one]
            change
              (((SignedCount.energy x.c0 + SignedCount.energy x.c1) +
                  SignedCount.energy x.c2) + SignedCount.energy x.c3) =
                ((((SignedCount.energy x.c0 + 0) + 0) + 0) +
                  (((0 + SignedCount.energy x.c1) + SignedCount.energy x.c2) +
                    SignedCount.energy x.c3))
            exact (four_term_split_one
              (SignedCount.energy x.c0)
              (SignedCount.energy x.c1)
              (SignedCount.energy x.c2)
              (SignedCount.energy x.c3)).symm
        | succ h =>
            cases h with
            | zero =>
                rw [coherenceProjection_two, coherenceShadow_two]
                change
                  (((SignedCount.energy x.c0 + SignedCount.energy x.c1) +
                      SignedCount.energy x.c2) + SignedCount.energy x.c3) =
                    ((((SignedCount.energy x.c0 + SignedCount.energy x.c1) + 0) + 0) +
                      (((0 + 0) + SignedCount.energy x.c2) + SignedCount.energy x.c3))
                exact (four_term_split_two
                  (SignedCount.energy x.c0)
                  (SignedCount.energy x.c1)
                  (SignedCount.energy x.c2)
                  (SignedCount.energy x.c3)).symm
            | succ h =>
                cases h with
                | zero =>
                    rw [coherenceProjection_three, coherenceShadow_three]
                    change
                      (((SignedCount.energy x.c0 + SignedCount.energy x.c1) +
                          SignedCount.energy x.c2) + SignedCount.energy x.c3) =
                        ((((SignedCount.energy x.c0 + SignedCount.energy x.c1) +
                            SignedCount.energy x.c2) + 0) +
                          (((0 + 0) + 0) + SignedCount.energy x.c3))
                    exact (four_term_split_three
                      (SignedCount.energy x.c0)
                      (SignedCount.energy x.c1)
                      (SignedCount.energy x.c2)
                      (SignedCount.energy x.c3)).symm
                | succ h =>
                    rw [coherenceProjection_tower_after_four, coherenceShadow_after_four h]
                    have hz : State.energy State.zero = 0 := by
                      rfl
                    rw [hz, add_zero_counting]

/-- The canonical coherence tower is faithful: after four additional refinement
steps, the tail vanishes identically. -/
def coherenceFaithfulTower : FaithfulEnergyTower where
  toEnergyHorizonTower := coherenceEnergyTower
  tail_energy_eventually_zero := by
    intro x h₀
    refine ⟨4, ?_⟩
    change State.energy (shadowProj coherenceTower (h₀ + 4) x) = 0
    rw [coherenceShadow_after_four h₀ x]
    rfl

/-- Coherence-calculus finite HFT-2 with no extra tower hypotheses. -/
theorem HFT2_coherence_finite
    (x : State) (h₀ : Nat) (hs : List Nat) (hmono : HorizonChain h₀ hs) :
    State.energy (shadowProj coherenceTower h₀ x) =
      telescopingEnergyChain coherenceEnergyTower x h₀ hs := by
  simpa [coherenceEnergyTower, coherenceTower] using
    HFT2_finite_energy coherenceEnergyTower x h₀ hs hmono

/-- Coherence-calculus faithful HFT-2 with no extra tower hypotheses. -/
theorem HFT2_coherence_stabilized
    (x : State) (h₀ : Nat) :
    ∃ N, ∀ k,
      State.energy (shadowProj coherenceTower h₀ x) =
        prefixIncrementEnergy coherenceEnergyTower x h₀ (N + k) := by
  simpa [coherenceFaithfulTower, coherenceEnergyTower, coherenceTower] using
    HFT2_faithful_stabilized coherenceFaithfulTower x h₀

end CoherenceCalculus
