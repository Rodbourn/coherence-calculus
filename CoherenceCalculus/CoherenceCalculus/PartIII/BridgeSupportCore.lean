/-!
# PartIII.BridgeSupportCore

Minimal support layer for the constructive Part III bridge.

This file is intentionally root-free: it packages only eventual exact equality,
its induced limit interface, and singleton forcing at the bare type level. The
bridge-specific mathematics is developed in the downstream Part III cores on
top of these support declarations.
-/

namespace CoherenceCalculus

/-- Endomaps on a type, used throughout the Part III bridge packaging. -/
abbrev Endo (X : Type) : Type := X → X

/-- Explicit witness that a sequence is eventually exactly equal to a target. -/
structure BridgeEventuallyEqData {X : Type} (f : Nat → X) (target : X) where
  cutoff : Nat
  stable : ∀ h : Nat, cutoff ≤ h → f h = target

/-- Native Part III convergence notion: exact equality from some stage onward. -/
def BridgeEventuallyEq {X : Type} (f : Nat → X) (target : X) : Prop :=
  ∃ cutoff : Nat, ∀ h : Nat, cutoff ≤ h → f h = target

theorem BridgeEventuallyEqData.eventually {X : Type} {f : Nat → X} {target : X}
    (data : BridgeEventuallyEqData f target) : BridgeEventuallyEq f target := by
  exact ⟨data.cutoff, data.stable⟩

theorem bridgeEventuallyEq_of_data {X : Type} {f : Nat → X} {target : X}
    (data : BridgeEventuallyEqData f target) : BridgeEventuallyEq f target :=
  data.eventually

/-- Eventual exact equality has unique limit. -/
theorem bridgeEventuallyEq_unique {X : Type} {f : Nat → X} {x y : X}
    (hx : BridgeEventuallyEq f x) (hy : BridgeEventuallyEq f y) :
    x = y := by
  rcases hx with ⟨Nx, hx⟩
  rcases hy with ⟨Ny, hy⟩
  have hx' : f (Nx + Ny) = x := hx (Nx + Ny) (Nat.le_add_right Nx Ny)
  have hy' : f (Nx + Ny) = y := hy (Nx + Ny) (Nat.le_add_left Ny Nx)
  calc
    x = f (Nx + Ny) := hx'.symm
    _ = y := hy'

/-- Pointwise equality preserves eventual exact equality. -/
theorem bridgeEventuallyEq_congr {X : Type} {f g : Nat → X} {x : X}
    (hfg : ∀ n : Nat, f n = g n) (hx : BridgeEventuallyEq f x) :
    BridgeEventuallyEq g x := by
  rcases hx with ⟨cutoff, hcutoff⟩
  refine ⟨cutoff, ?_⟩
  intro h hh
  calc
    g h = f h := (hfg h).symm
    _ = x := hcutoff h hh

/-- Eventual exact equality is stable under pointwise maps. -/
theorem bridgeEventuallyEq_map {X Y : Type} (S : X → Y)
    {f : Nat → X} {x : X} (hx : BridgeEventuallyEq f x) :
    BridgeEventuallyEq (fun h => S (f h)) (S x) := by
  rcases hx with ⟨cutoff, hcutoff⟩
  refine ⟨cutoff, ?_⟩
  intro h hh
  change S (f h) = S x
  rw [hcutoff h hh]

/-- Constructive left-additive gap witness for `m ≤ n`. -/
theorem nat_exists_eq_add_of_le {m n : Nat} (h : m ≤ n) :
    ∃ k : Nat, n = k + m := by
  induction h with
  | refl =>
      exact ⟨0, by rw [Nat.zero_add]⟩
  | @step n h ih =>
      rcases ih with ⟨k, hk⟩
      refine ⟨Nat.succ k, ?_⟩
      calc
        Nat.succ n = Nat.succ (k + m) := by rw [hk]
        _ = Nat.succ k + m := by rw [Nat.succ_add]

/-- Constructive right-additive gap witness for `m ≤ n`. -/
theorem nat_exists_eq_right_add_of_le {m n : Nat} (h : m ≤ n) :
    ∃ k : Nat, n = m + k := by
  induction h with
  | refl =>
      exact ⟨0, by rw [Nat.add_zero]⟩
  | @step n h ih =>
      rcases ih with ⟨k, hk⟩
      refine ⟨Nat.succ k, ?_⟩
      calc
        Nat.succ n = Nat.succ (m + k) := by rw [hk]
        _ = m + Nat.succ k := by rw [Nat.add_succ]

/-- A sequence that is constant from a right shift onward is eventually exact. -/
theorem bridgeEventuallyEq_of_shift {X : Type}
    (f : Nat → X) (target : X) (cutoff : Nat)
    (hshift : ∀ k : Nat, f (k + cutoff) = target) :
    BridgeEventuallyEq f target := by
  refine ⟨cutoff, ?_⟩
  intro h hh
  obtain ⟨k, hk⟩ := nat_exists_eq_add_of_le hh
  rw [hk]
  exact hshift k

/-- Limit interface induced by eventual exact equality. -/
structure LimitInterface (X : Type) where
  tendsTo : (Nat → X) → X → Prop
  unique :
    ∀ {f : Nat → X} {x y : X}, tendsTo f x → tendsTo f y → x = y
  congr :
    ∀ {f g : Nat → X} {x : X},
      (∀ n : Nat, f n = g n) → tendsTo f x → tendsTo g x
  map :
    ∀ (S : X → X) {f : Nat → X} {x : X},
      tendsTo f x → tendsTo (fun n => S (f n)) (S x)

/-- Native Part III limit interface built from eventual exact equality. -/
def bridgeEventualLimitInterface (X : Type) : LimitInterface X where
  tendsTo := BridgeEventuallyEq
  unique := by
    intro f x y hx hy
    exact bridgeEventuallyEq_unique hx hy
  congr := by
    intro f g x hfg hx
    exact bridgeEventuallyEq_congr hfg hx
  map := by
    intro S f x hx
    exact bridgeEventuallyEq_map S hx

/-- Singleton forcing for an explicitly admissible target. -/
def ForcedSingleton {X : Type} (admissible : X → Prop) (target : X) : Prop :=
  admissible target ∧ ∀ other : X, admissible other → other = target

theorem forcedSingleton_intro {X : Type} (admissible : X → Prop) (target : X)
    (hmem : admissible target)
    (hunique : ∀ other : X, admissible other → other = target) :
    ForcedSingleton admissible target := by
  exact ⟨hmem, hunique⟩

end CoherenceCalculus
