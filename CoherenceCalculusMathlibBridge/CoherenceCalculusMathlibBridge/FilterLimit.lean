import CoherenceCalculus.PartIII.BridgeSupportCore
import CoherenceCalculusMathlibBridge.Contract
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

namespace CoherenceCalculusMathlibBridge

open CoherenceCalculus

/--
Low-level mathlib-backed limit predicate for Part III.

This does not use topological convergence. It uses eventual constancy at
`Filter.atTop`, which is strong enough to satisfy the current abstract
`LimitInterface` map law for arbitrary functions.
-/
def EventuallyEqAtTop {X : Type _} (f : Nat → X) (target : X) : Prop :=
  ∀ᶠ n in Filter.atTop, f n = target

theorem eventuallyEqAtTop_unique
    {X : Type _} {f : Nat → X} {x y : X}
    (hx : EventuallyEqAtTop f x) (hy : EventuallyEqAtTop f y) :
    x = y := by
  rw [EventuallyEqAtTop, Filter.eventually_atTop] at hx hy
  rcases hx with ⟨cx, hcx⟩
  rcases hy with ⟨cy, hcy⟩
  exact (hcx (max cx cy) (Nat.le_max_left _ _)).symm.trans
    (hcy (max cx cy) (Nat.le_max_right _ _))

/-- The Part III `LimitInterface` interpreted through mathlib filters. -/
def filterLimitInterface (X : Type _) : CoherenceCalculus.LimitInterface X where
  tendsTo := EventuallyEqAtTop
  unique := by
    intro f x y hx hy
    exact eventuallyEqAtTop_unique hx hy
  congr := by
    intro f g x hfg hf
    exact hf.mono (fun n hn => by
      calc
        g n = f n := (hfg n).symm
        _ = x := hn)
  map := by
    intro S f x hf
    exact hf.mono (fun n hn => congrArg S hn)

theorem bridgeEventuallyEq_iff_filter
    {X : Type _} {f : Nat → X} {target : X} :
    CoherenceCalculus.BridgeEventuallyEq f target ↔
      (filterLimitInterface X).tendsTo f target := by
  constructor
  · intro h
    change EventuallyEqAtTop f target
    simpa [EventuallyEqAtTop, Filter.eventually_atTop] using h
  · intro h
    change EventuallyEqAtTop f target at h
    simpa [EventuallyEqAtTop, Filter.eventually_atTop] using h

theorem eventuallyEqData_to_filter
    {X : Type _} {f : Nat → X} {target : X}
    (data : CoherenceCalculus.BridgeEventuallyEqData f target) :
    (filterLimitInterface X).tendsTo f target := by
  exact bridgeEventuallyEq_iff_filter.mp data.eventually

/-- Detached contract wrapper for the low-level filter-backed limit interface. -/
def filterLimitContract (X : Type _) : LimitContract X where
  limits := filterLimitInterface X

end CoherenceCalculusMathlibBridge
