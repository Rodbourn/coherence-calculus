import CoherenceCalculus.Foundation.SummationCore

/-!
# Foundation.FaithfulTowerCore

Faithful-tail stabilization for the rebuilt HFT-2 layer.

Rather than introducing full analytic series machinery, this module encodes the
faithful limit as eventual vanishing of tail energy. This is enough to show that
the consecutive prefix sums in HFT-2 stabilize exactly.
-/

namespace CoherenceCalculus

/-- A faithful energy tower is one whose shadow energy eventually vanishes along
every horizon tail. -/
structure FaithfulEnergyTower extends EnergyHorizonTower where
  tail_energy_eventually_zero : ∀ x h₀,
    ∃ N, State.energy (shadowProj toHorizonTower (h₀ + N) x) = 0

/-- If the tail energy at a horizon is zero, every later prefix increment sum
from that horizon is zero. -/
theorem zero_tail_prefix_zero
    (T : EnergyHorizonTower) (x : State) (h₀ n : Nat)
    (hz : State.energy (shadowProj T.toHorizonTower h₀ x) = 0) :
    prefixIncrementEnergy T x h₀ n = 0 := by
  have htel := HFT2_prefix_energy T x h₀ n
  rw [hz] at htel
  exact add_eq_zero_left_counting htel.symm

/-- If the tail energy at a horizon is zero, then all later tail energies are
also zero. -/
theorem zero_tail_persists
    (T : EnergyHorizonTower) (x : State) (h₀ n : Nat)
    (hz : State.energy (shadowProj T.toHorizonTower h₀ x) = 0) :
    State.energy (shadowProj T.toHorizonTower (h₀ + n) x) = 0 := by
  have htel := HFT2_prefix_energy T x h₀ n
  rw [hz] at htel
  exact add_eq_zero_right_counting htel.symm

/-- Faithful HFT-2 in exact finite-prefix form: some prefix already captures the
entire initial shadow energy. -/
theorem HFT2_faithful_prefix_exact
    (T : FaithfulEnergyTower) (x : State) (h₀ : Nat) :
    ∃ N, State.energy (shadowProj T.toHorizonTower h₀ x) =
      prefixIncrementEnergy T.toEnergyHorizonTower x h₀ N := by
  obtain ⟨N, hN⟩ := T.tail_energy_eventually_zero x h₀
  refine ⟨N, ?_⟩
  have htel := HFT2_prefix_energy T.toEnergyHorizonTower x h₀ N
  rw [hN, add_zero_counting] at htel
  exact htel

/-- Faithful HFT-2 stabilization: once the tail vanishes, all longer prefix sums
agree with the same exact total. This is the discrete stabilized form of the
infinite telescoping identity. -/
theorem HFT2_faithful_stabilized
    (T : FaithfulEnergyTower) (x : State) (h₀ : Nat) :
    ∃ N, ∀ k,
      State.energy (shadowProj T.toHorizonTower h₀ x) =
        prefixIncrementEnergy T.toEnergyHorizonTower x h₀ (N + k) := by
  obtain ⟨N, hN⟩ := T.tail_energy_eventually_zero x h₀
  refine ⟨N, ?_⟩
  intro k
  have hbase : State.energy (shadowProj T.toHorizonTower h₀ x) =
      prefixIncrementEnergy T.toEnergyHorizonTower x h₀ N := by
    have htel := HFT2_prefix_energy T.toEnergyHorizonTower x h₀ N
    rw [hN, add_zero_counting] at htel
    exact htel
  have htailZero :
      prefixIncrementEnergy T.toEnergyHorizonTower x (h₀ + N) k = 0 := by
    exact zero_tail_prefix_zero T.toEnergyHorizonTower x (h₀ + N) k hN
  calc
    State.energy (shadowProj T.toHorizonTower h₀ x)
        = prefixIncrementEnergy T.toEnergyHorizonTower x h₀ N := hbase
    _ = prefixIncrementEnergy T.toEnergyHorizonTower x h₀ N + 0 := by
          rw [add_zero_counting]
    _ = prefixIncrementEnergy T.toEnergyHorizonTower x h₀ N +
          prefixIncrementEnergy T.toEnergyHorizonTower x (h₀ + N) k := by
          rw [htailZero]
    _ = prefixIncrementEnergy T.toEnergyHorizonTower x h₀ (N + k) := by
          rw [← prefixIncrementEnergy_append]

end CoherenceCalculus
