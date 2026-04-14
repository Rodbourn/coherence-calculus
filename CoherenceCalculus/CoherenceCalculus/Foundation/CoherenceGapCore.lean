import CoherenceCalculus.Foundation.ConstraintCompilerCore
import CoherenceCalculus.Foundation.PairingCore

/-!
# Foundation.CoherenceGapCore

Observable coherence-gap statements on the rebuilt pairing/defect layer.

The manuscript's spectral language is represented here by explicit lower-bound
and kernel hypotheses on the concrete defect-energy form. This keeps the active
surface honest and bedrock-clean while still isolating the exact mechanism:
positive defect energy on the observable sector forces a gap.
-/

namespace CoherenceCalculus

/-- Finite product over `Fin n`, rebuilt by explicit recursion on `n`. -/
def finNatProd (n : Nat) (f : Fin n → Nat) : Nat :=
  match n with
  | 0 => 1
  | k + 1 =>
      finNatProd k (fun i => f ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩) *
      f ⟨k, Nat.lt_succ_self k⟩

/-- The defect-energy operator associated to a leakage map and a chosen
energy-adjoint witness. -/
def defectEnergyOp
    (T : HorizonTower) (h : Nat) (A Astar : AddMap) : AddMap :=
  defectEnergyOperator T h A Astar

/-- Observable lower-bound predicate for the defect-energy operator. -/
def gap_detection_ratio
    (T : HorizonTower) (h : Nat) (A Astar : AddMap) (μ : Nat) : Prop :=
  ∀ x : State,
    μ + State.pair ((T.π h).toFun x) ((T.π h).toFun x) ≤
      State.pair x (defectEnergyOp T h A Astar x)

private theorem nat_eq_zero_of_square_eq_zero (n : Nat) (h : n * n = 0) : n = 0 := by
  cases n with
  | zero =>
      rfl
  | succ k =>
      change (k + 1) * k + (k + 1) = 0 at h
      have hsucc : k + 1 = 0 := add_eq_zero_right_counting h
      exact False.elim (succ_not_zero_counting k hsucc)

private theorem signedCount_eq_zero_of_energy_eq_zero
    (z : SignedCount) (h : SignedCount.energy z = 0) : z = SignedCount.zero := by
  unfold SignedCount.energy at h
  have hpos_sq : z.pos * z.pos = 0 := add_eq_zero_left_counting h
  have hneg_sq : z.neg * z.neg = 0 := add_eq_zero_right_counting h
  have hpos : z.pos = 0 := nat_eq_zero_of_square_eq_zero z.pos hpos_sq
  have hneg : z.neg = 0 := nat_eq_zero_of_square_eq_zero z.neg hneg_sq
  exact SignedCount.ext hpos hneg

private theorem state_eq_zero_of_energy_eq_zero
    (x : State) (h : State.energy x = 0) : x = State.zero := by
  unfold State.energy at h
  have h012 : SignedCount.energy x.c0 + SignedCount.energy x.c1 + SignedCount.energy x.c2 = 0 :=
    add_eq_zero_left_counting h
  have h01 : SignedCount.energy x.c0 + SignedCount.energy x.c1 = 0 :=
    add_eq_zero_left_counting h012
  have hc0 : SignedCount.energy x.c0 = 0 := add_eq_zero_left_counting h01
  have hc1 : SignedCount.energy x.c1 = 0 := add_eq_zero_right_counting h01
  have hc2 : SignedCount.energy x.c2 = 0 := add_eq_zero_right_counting h012
  have hc3 : SignedCount.energy x.c3 = 0 := add_eq_zero_right_counting h
  apply State.ext
  · exact signedCount_eq_zero_of_energy_eq_zero x.c0 hc0
  · exact signedCount_eq_zero_of_energy_eq_zero x.c1 hc1
  · exact signedCount_eq_zero_of_energy_eq_zero x.c2 hc2
  · exact signedCount_eq_zero_of_energy_eq_zero x.c3 hc3

/-- A uniform observable lower bound on the defect-energy operator restricts to
the same lower bound on observable states. -/
theorem coherence_gap_theorem
    (T : HorizonTower) (h : Nat) (A Astar : AddMap) (μ : Nat)
    (hgap : gap_detection_ratio T h A Astar μ)
    (x : State) (hx : (T.π h).toFun x = x) :
    μ + State.pair x x ≤ State.pair x (defectEnergyOp T h A Astar x) := by
  unfold gap_detection_ratio at hgap
  calc
    μ + State.pair x x
        = μ + State.pair ((T.π h).toFun x) ((T.π h).toFun x) := by
            rw [hx]
    _ ≤ State.pair x (defectEnergyOp T h A Astar x) := hgap x

/-- Trivial observable kernel of the leakage map forces injectivity of the
defect-energy operator on the observable sector. -/
theorem kernel_gap_injective_statement
    (T : HorizonTower) (h : Nat) (A Astar : AddMap)
    (hadj : HasEnergyAdjoint (AddMap.leakageMap T h A) Astar)
    (hker :
      ∀ x : State,
        (T.π h).toFun x = x →
        AddMap.leakageMap T h A x = State.zero →
        x = State.zero)
    (x : State) (hx : (T.π h).toFun x = x)
    (hzero : State.pair x (defectEnergyOp T h A Astar x) = 0) :
    x = State.zero := by
  have hform :
      defectEnergy T h A x =
        State.pair x (defectEnergyOp T h A Astar x) := by
    change defectEnergy T h A x =
      State.pair x (defectEnergyOperator T h A Astar x)
    exact defectEnergy_operator_form T h A Astar x hadj
  have hdefect : defectEnergy T h A x = 0 := by
    calc
      defectEnergy T h A x
          = State.pair x (defectEnergyOp T h A Astar x) := hform
      _ = 0 := hzero
  have hleak_energy : State.energy (AddMap.leakageMap T h A x) = 0 := by
    rw [AddMap.leakageMap_apply]
    unfold defectEnergy at hdefect
    exact hdefect
  have hleak_zero : AddMap.leakageMap T h A x = State.zero := by
    exact state_eq_zero_of_energy_eq_zero (AddMap.leakageMap T h A x) hleak_energy
  exact hker x hx hleak_zero

/-- Finite shadow-transport invariant family on the observable sector of the
defect-energy operator. The active rebuild keeps the spectral data explicit as
finite natural-valued invariants. -/
structure shadow_transport_invariants
    (T : HorizonTower) (h : Nat) (A Astar : AddMap) where
  rank : Nat
  spectrum : Fin rank → Nat
  moments : Nat → Nat
  determinantPoly : Nat → Nat
  zeroOperator : Prop
  zeroLeakage : Prop
  zero_spectrum_iff_zeroOperator :
    (∀ i : Fin rank, spectrum i = 0) ↔ zeroOperator
  zeroOperator_iff_zeroLeakage :
    zeroOperator ↔ zeroLeakage
  moments_formula :
    ∀ k : Nat,
      moments k =
        Compiler.finNatSum rank (fun i => Nat.pow (spectrum i) k)
  determinant_formula :
    ∀ t : Nat,
      determinantPoly t =
        finNatProd rank (fun i => 1 + t * spectrum i)

/-- The finite shadow-transport package is exactly the explicit invariant data:
nonnegative spectrum, zero-spectrum detection, and finite moment/determinant
reconstruction formulas. -/
theorem shadow_transport_package
    {T : HorizonTower} {h : Nat} {A Astar : AddMap}
    (data : shadow_transport_invariants T h A Astar) :
    (∀ i : Fin data.rank, 0 ≤ data.spectrum i) ∧
      (((∀ i : Fin data.rank, data.spectrum i = 0) ↔ data.zeroOperator) ∧
        (data.zeroOperator ↔ data.zeroLeakage)) ∧
      (∀ k : Nat,
        data.moments k =
          Compiler.finNatSum data.rank (fun i => Nat.pow (data.spectrum i) k)) ∧
      (∀ t : Nat,
        data.determinantPoly t =
          finNatProd data.rank (fun i => 1 + t * data.spectrum i)) := by
  refine ⟨?_, ?_, data.moments_formula, data.determinant_formula⟩
  · intro i
    exact Nat.zero_le (data.spectrum i)
  · exact ⟨data.zero_spectrum_iff_zeroOperator, data.zeroOperator_iff_zeroLeakage⟩

/-- Explicit symmetry-block factorization of the shadow-transport invariant
family along an isotypic decomposition. -/
structure shadow_transport_block_factorization
    (T : HorizonTower) (h : Nat) (A Astar : AddMap)
    (G : Compiler.FinGroup) (rep : Compiler.UnitaryRep G) where
  decomp : Compiler.IsotypicDecomposition G rep
  whole : shadow_transport_invariants T h A Astar
  blockFamily :
    Fin decomp.numIrreps → shadow_transport_invariants T h A Astar
  moments_sum :
    ∀ k : Nat,
      whole.moments k =
        Compiler.finNatSum decomp.numIrreps (fun rho => (blockFamily rho).moments k)
  determinant_prod :
    ∀ t : Nat,
      whole.determinantPoly t =
        finNatProd decomp.numIrreps (fun rho => (blockFamily rho).determinantPoly t)

/-- The shadow-transport invariant family factorizes across the explicit
symmetry blocks supplied by the current isotypic decomposition. -/
theorem shadow_transport_factorization
    {T : HorizonTower} {h : Nat} {A Astar : AddMap}
    {G : Compiler.FinGroup} {rep : Compiler.UnitaryRep G}
    (data : shadow_transport_block_factorization T h A Astar G rep) :
    (∀ k : Nat,
      data.whole.moments k =
        Compiler.finNatSum data.decomp.numIrreps
          (fun rho => (data.blockFamily rho).moments k)) ∧
      (∀ t : Nat,
        data.whole.determinantPoly t =
          finNatProd data.decomp.numIrreps
            (fun rho => (data.blockFamily rho).determinantPoly t)) := by
  exact ⟨data.moments_sum, data.determinant_prod⟩

end CoherenceCalculus
