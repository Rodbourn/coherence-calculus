import CoherenceCalculus.Foundation.HFT2Core

/-!
# Foundation.SummationCore

Canonical consecutive-prefix sums for horizon increment energies.

This module reorganizes the finite telescoping theorem into a standard prefix
form indexed by a starting horizon and a prefix length.
-/

namespace CoherenceCalculus

/-- One-step returned residual flux: the energy released from the shadow between
two consecutive horizons. -/
def returnedResidualFlux (T : EnergyHorizonTower) (x : State) (h : Nat) : Nat :=
  State.energy (incrementBetween T.toHorizonTower h (h + 1) x)

/-- Unrecovered residual stock: the shadow energy still hidden beyond horizon
`h`. -/
def unrecoveredResidualStock (T : EnergyHorizonTower) (x : State) (h : Nat) : Nat :=
  State.energy (shadowProj T.toHorizonTower h x)

/-- Consecutive prefix sum of increment energies starting at horizon `h₀`. -/
def prefixIncrementEnergy (T : EnergyHorizonTower) (x : State) : Nat → Nat → Nat
  | _, 0 => 0
  | h₀, n + 1 =>
      State.energy (incrementBetween T.toHorizonTower h₀ (h₀ + 1) x) +
      prefixIncrementEnergy T x (h₀ + 1) n

/-- Prefix energy over zero steps is zero. -/
theorem prefixIncrementEnergy_zero (T : EnergyHorizonTower) (x : State) (h₀ : Nat) :
    prefixIncrementEnergy T x h₀ 0 = 0 := rfl

/-- Successor step for the consecutive prefix energy sum. -/
theorem prefixIncrementEnergy_succ (T : EnergyHorizonTower) (x : State) (h₀ n : Nat) :
    prefixIncrementEnergy T x h₀ (n + 1) =
      State.energy (incrementBetween T.toHorizonTower h₀ (h₀ + 1) x) +
      prefixIncrementEnergy T x (h₀ + 1) n := rfl

/-- One-step residual accounting: the unrecovered residual stock at horizon `h`
splits exactly into returned flux across the next refinement step plus the
remaining stock at horizon `h + 1`. -/
theorem unrecoveredResidualStock_step
    (T : EnergyHorizonTower) (x : State) (h : Nat) :
    unrecoveredResidualStock T x h =
      returnedResidualFlux T x h +
      unrecoveredResidualStock T x (h + 1) := by
  unfold unrecoveredResidualStock returnedResidualFlux
  exact pair_telescope_energy T h (h + 1) (Nat.le_succ h) x

/-- Unrecovered residual stock is monotone under refinement: moving to a finer
horizon cannot increase the residual stock that remains hidden. -/
theorem unrecoveredResidualStock_monotone
    (T : EnergyHorizonTower) (x : State) (h : Nat) :
    unrecoveredResidualStock T x (h + 1) ≤ unrecoveredResidualStock T x h := by
  rw [unrecoveredResidualStock_step T x h]
  exact Nat.le_add_left _ _

/-- Consecutive prefix version of finite HFT-2. -/
theorem HFT2_prefix_energy (T : EnergyHorizonTower) (x : State) (h₀ n : Nat) :
    State.energy (shadowProj T.toHorizonTower h₀ x) =
      prefixIncrementEnergy T x h₀ n +
      State.energy (shadowProj T.toHorizonTower (h₀ + n) x) := by
  induction n generalizing h₀ with
  | zero =>
      rw [prefixIncrementEnergy_zero, add_zero_counting]
      rw [zero_add_counting]
  | succ n ih =>
      have hidx : (h₀ + 1) + n = h₀ + (n + 1) := by
        rw [add_assoc_counting h₀ 1 n, add_comm_counting 1 n]
      calc
        State.energy (shadowProj T.toHorizonTower h₀ x)
            =
          State.energy (incrementBetween T.toHorizonTower h₀ (h₀ + 1) x) +
          State.energy (shadowProj T.toHorizonTower (h₀ + 1) x) := by
              exact pair_telescope_energy T h₀ (h₀ + 1) (Nat.le_succ h₀) x
        _ =
          State.energy (incrementBetween T.toHorizonTower h₀ (h₀ + 1) x) +
          (prefixIncrementEnergy T x (h₀ + 1) n +
            State.energy (shadowProj T.toHorizonTower ((h₀ + 1) + n) x)) := by
              rw [ih]
        _ =
          (State.energy (incrementBetween T.toHorizonTower h₀ (h₀ + 1) x) +
            prefixIncrementEnergy T x (h₀ + 1) n) +
          State.energy (shadowProj T.toHorizonTower ((h₀ + 1) + n) x) := by
              rw [← add_assoc_counting]
        _ =
          prefixIncrementEnergy T x h₀ (n + 1) +
          State.energy (shadowProj T.toHorizonTower ((h₀ + 1) + n) x) := by
              rw [prefixIncrementEnergy]
        _ =
          prefixIncrementEnergy T x h₀ (n + 1) +
          State.energy (shadowProj T.toHorizonTower (h₀ + (n + 1)) x) := by
              rw [hidx]

/-- Over any finite refinement interval, the initial unrecovered residual stock
splits exactly into the accumulated returned flux and the terminal unrecovered
stock. -/
theorem unrecoveredResidualStock_prefix
    (T : EnergyHorizonTower) (x : State) (h₀ n : Nat) :
    unrecoveredResidualStock T x h₀ =
      prefixIncrementEnergy T x h₀ n +
      unrecoveredResidualStock T x (h₀ + n) := by
  unfold unrecoveredResidualStock
  exact HFT2_prefix_energy T x h₀ n

/-- Prefix sums split across concatenated consecutive blocks. -/
theorem prefixIncrementEnergy_append
    (T : EnergyHorizonTower) (x : State) (h₀ n m : Nat) :
    prefixIncrementEnergy T x h₀ (n + m) =
      prefixIncrementEnergy T x h₀ n +
      prefixIncrementEnergy T x (h₀ + n) m := by
  induction n generalizing h₀ with
  | zero =>
      rw [zero_add_counting, prefixIncrementEnergy_zero, add_zero_counting]
      rw [zero_add_counting]
  | succ n ih =>
      have hidx : (h₀ + 1) + n = h₀ + (n + 1) := by
        rw [add_assoc_counting h₀ 1 n, add_comm_counting 1 n]
      calc
        prefixIncrementEnergy T x h₀ ((n + 1) + m)
            =
          State.energy (incrementBetween T.toHorizonTower h₀ (h₀ + 1) x) +
          prefixIncrementEnergy T x (h₀ + 1) (n + m) := by
              rw [Nat.succ_add, prefixIncrementEnergy_succ]
        _ =
          State.energy (incrementBetween T.toHorizonTower h₀ (h₀ + 1) x) +
          (prefixIncrementEnergy T x (h₀ + 1) n +
            prefixIncrementEnergy T x ((h₀ + 1) + n) m) := by
              rw [ih]
        _ =
          (State.energy (incrementBetween T.toHorizonTower h₀ (h₀ + 1) x) +
            prefixIncrementEnergy T x (h₀ + 1) n) +
          prefixIncrementEnergy T x ((h₀ + 1) + n) m := by
              rw [← add_assoc_counting]
        _ =
          prefixIncrementEnergy T x h₀ (n + 1) +
          prefixIncrementEnergy T x ((h₀ + 1) + n) m := by
              rw [prefixIncrementEnergy_succ]
        _ =
          prefixIncrementEnergy T x h₀ (n + 1) +
          prefixIncrementEnergy T x (h₀ + (n + 1)) m := by
              rw [hidx]

end CoherenceCalculus
