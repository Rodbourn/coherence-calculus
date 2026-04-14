import CoherenceCalculus.Foundation.TransportOrderSelectionCore

/-!
# Foundation.TransportOrderFiniteCore

Explicit finite certificate core for transport-order selection.

This module packages the transport-order minimization story in the same
certificate-first style already used by the design-objective layer:

- each candidate carries an explicit exact transport-order certificate
- a finite family is listed explicitly
- a minimizer certificate chooses a least-order candidate

These blocks are intended to support later manuscript-facing wrappers without
requiring hidden least-element search over abstract admissible classes.
-/

namespace CoherenceCalculus

/-- An explicit candidate together with a certified exact tower transport
order. -/
structure ExactTransportOrderCandidate (T : HorizonTower) where
  op : AddMap
  order : Nat
  order_witness : towerTransportOrderAtMost T op order
  order_minimal : ∀ m : Nat, towerTransportOrderAtMost T op m → order ≤ m

/-- Explicit finite family of exact transport-order candidates. -/
structure FiniteTransportOrderFamily (T : HorizonTower) where
  size : Nat
  candidate : Fin (Nat.succ size) → ExactTransportOrderCandidate T

/-- A minimizing index for the exact transport-order values in a finite family.
-/
def transportOrderMinimizesAt {T : HorizonTower}
    (family : FiniteTransportOrderFamily T)
    (best : Fin (Nat.succ family.size)) : Prop :=
  ∀ i : Fin (Nat.succ family.size),
    (family.candidate best).order ≤ (family.candidate i).order

/-- Explicit certificate that a listed candidate realizes the least exact
transport order in the finite family. -/
structure MinimalTransportOrderCertificate {T : HorizonTower}
    (family : FiniteTransportOrderFamily T) where
  best : Fin (Nat.succ family.size)
  minimal : transportOrderMinimizesAt family best

/-- The selected exact candidate from a finite minimizer certificate. -/
def selectedTransportCandidate {T : HorizonTower}
    (family : FiniteTransportOrderFamily T)
    (cert : MinimalTransportOrderCertificate family) :
    ExactTransportOrderCandidate T :=
  family.candidate cert.best

/-- The distinguished exact transport order selected by the minimizer
certificate. -/
def distinguishedFiniteTransportOrder {T : HorizonTower}
    (family : FiniteTransportOrderFamily T)
    (cert : MinimalTransportOrderCertificate family) : Nat :=
  (selectedTransportCandidate family cert).order

/-- The selected exact candidate carries the distinguished exact transport
order. -/
theorem selectedTransportCandidate_has_distinguished_order
    {T : HorizonTower}
    (family : FiniteTransportOrderFamily T)
    (cert : MinimalTransportOrderCertificate family) :
    (selectedTransportCandidate family cert).order =
      distinguishedFiniteTransportOrder family cert := by
  rfl

/-- The selected exact candidate satisfies the distinguished transport-order
bound. -/
theorem selectedTransportCandidate_witness
    {T : HorizonTower}
    (family : FiniteTransportOrderFamily T)
    (cert : MinimalTransportOrderCertificate family) :
    towerTransportOrderAtMost
      T
      (selectedTransportCandidate family cert).op
      (distinguishedFiniteTransportOrder family cert) := by
  exact (selectedTransportCandidate family cert).order_witness

/-- The distinguished exact transport order is bounded above by every listed
exact candidate order. -/
theorem distinguishedFiniteTransportOrder_le
    {T : HorizonTower}
    (family : FiniteTransportOrderFamily T)
    (cert : MinimalTransportOrderCertificate family)
    (i : Fin (Nat.succ family.size)) :
    distinguishedFiniteTransportOrder family cert ≤
      (family.candidate i).order := by
  exact cert.minimal i

/-- The exact least-order subclass of a finite family. -/
def finiteMinimalTransportSubclass {T : HorizonTower}
    (family : FiniteTransportOrderFamily T)
    (cert : MinimalTransportOrderCertificate family)
    (i : Fin (Nat.succ family.size)) : Prop :=
  (family.candidate i).order = distinguishedFiniteTransportOrder family cert

/-- The selected exact candidate lies in the exact least-order subclass. -/
theorem selectedTransportCandidate_mem_finiteMinimalTransportSubclass
    {T : HorizonTower}
    (family : FiniteTransportOrderFamily T)
    (cert : MinimalTransportOrderCertificate family) :
    finiteMinimalTransportSubclass family cert cert.best := by
  rfl

/-- The selected exact candidate remains minimal among all explicit transport
order bounds for the listed family. -/
theorem distinguishedFiniteTransportOrder_le_any_bound
    {T : HorizonTower}
    (family : FiniteTransportOrderFamily T)
    (cert : MinimalTransportOrderCertificate family)
    (i : Fin (Nat.succ family.size)) (m : Nat)
    (hm : towerTransportOrderAtMost T (family.candidate i).op m) :
    distinguishedFiniteTransportOrder family cert ≤ m := by
  have hselected_i :
      distinguishedFiniteTransportOrder family cert ≤ (family.candidate i).order := by
    exact cert.minimal i
  have hi_m : (family.candidate i).order ≤ m := by
    exact (family.candidate i).order_minimal m hm
  exact Nat.le_trans hselected_i hi_m

/-- If one listed exact candidate has order at most `1`, then the distinguished
exact transport order is at most `1`. -/
theorem distinguishedFiniteTransportOrder_le_one_of_exists_le_one
    {T : HorizonTower}
    (family : FiniteTransportOrderFamily T)
    (cert : MinimalTransportOrderCertificate family)
    (hone : ∃ i : Fin (Nat.succ family.size), (family.candidate i).order ≤ 1) :
    distinguishedFiniteTransportOrder family cert ≤ 1 := by
  rcases hone with ⟨i, hi⟩
  exact Nat.le_trans (cert.minimal i) hi

/-- If no listed exact candidate has order `0`, then the distinguished exact
transport order is not `0`. -/
theorem distinguishedFiniteTransportOrder_ne_zero_of_all_ne_zero
    {T : HorizonTower}
    (family : FiniteTransportOrderFamily T)
    (cert : MinimalTransportOrderCertificate family)
    (hzero : ∀ i : Fin (Nat.succ family.size), (family.candidate i).order ≠ 0) :
    distinguishedFiniteTransportOrder family cert ≠ 0 := by
  exact hzero cert.best

/-- A positive distinguished exact transport order bounded above by `1` is
forced to equal `1`. -/
theorem distinguishedFiniteTransportOrder_eq_one_of_le_one_of_pos
    {T : HorizonTower}
    (family : FiniteTransportOrderFamily T)
    (cert : MinimalTransportOrderCertificate family)
    (hle : distinguishedFiniteTransportOrder family cert ≤ 1)
    (hpos : 0 < distinguishedFiniteTransportOrder family cert) :
    distinguishedFiniteTransportOrder family cert = 1 := by
  cases hdist : distinguishedFiniteTransportOrder family cert with
  | zero =>
      have hpos_zero : 0 < 0 := by
        rw [hdist] at hpos
        exact hpos
      exact (Nat.not_lt_zero 0 hpos_zero).elim
  | succ n =>
      cases n with
      | zero =>
          rfl
      | succ n =>
          have htwo : 2 ≤ distinguishedFiniteTransportOrder family cert := by
            rw [hdist]
            exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))
          have htwo_le_one : 2 ≤ 1 := Nat.le_trans htwo hle
          exact (Nat.not_succ_le_self 1 htwo_le_one).elim

/-- Every finite exact transport-order family induces a transport-order filtered
family by forgetting the explicit least-order certificates. -/
def toTransportOrderFilteredFamily {T : HorizonTower}
    (family : FiniteTransportOrderFamily T) :
    TransportOrderFilteredFamily (Fin (Nat.succ family.size)) T where
  candidate := fun i => (family.candidate i).op
  admissible := fun _ => True
  finite_order := by
    intro i _
    exact ⟨(family.candidate i).order, (family.candidate i).order_witness⟩

/-- A finite minimizer certificate upgrades to a distinguished admissible
transport-order class on the induced filtered family. -/
def distinguishedClassOfMinimalCertificate {T : HorizonTower}
    (family : FiniteTransportOrderFamily T)
    (cert : MinimalTransportOrderCertificate family) :
    distinguishedTransportOrderClass (toTransportOrderFilteredFamily family) where
  order := distinguishedFiniteTransportOrder family cert
  witness := by
    refine ⟨cert.best, trivial, ?_⟩
    exact (family.candidate cert.best).order_witness
  minimal := by
    intro m hm
    rcases hm with ⟨i, _, hi⟩
    exact distinguishedFiniteTransportOrder_le_any_bound family cert i m hi

/-- If one listed exact candidate has order at most `1` and none have order
`0`, then the distinguished exact transport order is exactly `1`. -/
theorem finite_order_one_forcing
    {T : HorizonTower}
    (family : FiniteTransportOrderFamily T)
    (cert : MinimalTransportOrderCertificate family)
    (hone : ∃ i : Fin (Nat.succ family.size), (family.candidate i).order ≤ 1)
    (hzero : ∀ i : Fin (Nat.succ family.size), (family.candidate i).order ≠ 0) :
    distinguishedFiniteTransportOrder family cert = 1 := by
  rcases hone with ⟨i, hi⟩
  have hle : distinguishedFiniteTransportOrder family cert ≤ 1 := by
    exact Nat.le_trans (cert.minimal i) hi
  have hnot0 : distinguishedFiniteTransportOrder family cert ≠ 0 := by
    exact hzero cert.best
  cases hdist : distinguishedFiniteTransportOrder family cert with
  | zero =>
      exact (hnot0 hdist).elim
  | succ n =>
      cases n with
      | zero =>
          rfl
      | succ n =>
          have htwo : 2 ≤ distinguishedFiniteTransportOrder family cert := by
            rw [hdist]
            exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))
          have htwo_le_one : 2 ≤ 1 := Nat.le_trans htwo hle
          exact (Nat.not_succ_le_self 1 htwo_le_one).elim

end CoherenceCalculus
