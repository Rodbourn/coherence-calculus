import CoherenceCalculus.Foundation.TowerCalculusCore

/-!
# Foundation.TransportOrderSelectionCore

Transport-order selection interfaces rebuilt directly on the active tower
calculus.

At this stage the certified surface records the exact structural data used in
the manuscript's transport-order selection discussion:

- admissible families equipped with finite tower-order witnesses
- a packaged distinguished minimal-order class
- the induced minimal admissible subclass
- the order-one forcing criterion once such a distinguished class has been
  supplied explicitly

This avoids introducing any hidden classical minimization principle while still
keeping the transport-order interface manuscript-facing and bedrock-clean.
-/

namespace CoherenceCalculus

/-- A candidate family is transport-order filtered when every admissible
candidate carries an explicit finite tower transport-order witness. -/
structure TransportOrderFilteredFamily (Index : Type) (T : HorizonTower) where
  candidate : Index → AddMap
  admissible : Index → Prop
  finite_order :
    ∀ i : Index, admissible i →
      ∃ m : Nat, towerTransportOrderAtMost T (candidate i) m

/-- `m` is an admissible transport-order bound if some admissible candidate
realizes it. -/
def admissibleTransportOrder
    {Index : Type} {T : HorizonTower}
    (F : TransportOrderFilteredFamily Index T) (m : Nat) : Prop :=
  ∃ i : Index, F.admissible i ∧ towerTransportOrderAtMost T (F.candidate i) m

/-- A distinguished admissible transport-order class is explicit data: an order
bound realized by some admissible candidate and minimal among all admissible
order bounds. -/
structure distinguishedTransportOrderClass
    {Index : Type} {T : HorizonTower}
    (F : TransportOrderFilteredFamily Index T) where
  order : Nat
  witness : admissibleTransportOrder F order
  minimal : ∀ m : Nat, admissibleTransportOrder F m → order ≤ m

/-- The minimal admissible transport subclass attached to a distinguished class
consists exactly of the admissible candidates realizing its order. -/
def minimalAdmissibleTransportSubclass
    {Index : Type} {T : HorizonTower}
    (F : TransportOrderFilteredFamily Index T)
    (d : distinguishedTransportOrderClass F) (i : Index) : Prop :=
  F.admissible i ∧ towerTransportOrderAtMost T (F.candidate i) d.order

/-- A predicate is singleton modulo a relation if all of its points are related
to one distinguished representative. -/
def SingletonModulo
    {Index : Type} (P : Index → Prop) (r : Index → Index → Prop) : Prop :=
  ∃ i₀ : Index, P i₀ ∧ ∀ i : Index, P i → r i i₀

/-- The transport order is forced modulo `r` when all minimal admissible
candidates are `r`-equivalent. -/
def transportOrderForced
    {Index : Type} {T : HorizonTower}
    (F : TransportOrderFilteredFamily Index T)
    (d : distinguishedTransportOrderClass F)
    (r : Index → Index → Prop) : Prop :=
  ∀ i j : Index,
    minimalAdmissibleTransportSubclass F d i →
      minimalAdmissibleTransportSubclass F d j →
        r i j

/-- The minimal admissible transport subclass is canonical by construction, and
singleton-modulo equivalence forces the transport order. -/
theorem minimal_admissible_transport_order
    {Index : Type} {T : HorizonTower}
    (F : TransportOrderFilteredFamily Index T)
    (d : distinguishedTransportOrderClass F) :
    (∀ i : Index,
      minimalAdmissibleTransportSubclass F d i ↔
        F.admissible i ∧ towerTransportOrderAtMost T (F.candidate i) d.order) ∧
      (∀ r : Index → Index → Prop,
        Equivalence r →
          SingletonModulo (minimalAdmissibleTransportSubclass F d) r →
            transportOrderForced F d r) := by
  refine ⟨?_, ?_⟩
  · intro i
    rfl
  · intro r hr hsingle i j hi hj
    rcases hsingle with ⟨i₀, _hi₀, hi₀⟩
    exact hr.trans (hi₀ i hi) (hr.symm (hi₀ j hj))

/-- If a distinguished admissible transport-order class is bounded by `1` and
no admissible candidate has order `0`, then the distinguished class is exactly
`1`. Singleton-modulo equivalence then forces the one-step class. -/
theorem order_one_forcing_criterion
    {Index : Type} {T : HorizonTower}
    (F : TransportOrderFilteredFamily Index T)
    (d : distinguishedTransportOrderClass F)
    (hone : admissibleTransportOrder F 1)
    (hzero : ¬ admissibleTransportOrder F 0) :
    d.order = 1 ∧
      (∀ r : Index → Index → Prop,
        Equivalence r →
          SingletonModulo (minimalAdmissibleTransportSubclass F d) r →
            transportOrderForced F d r) := by
  have hle : d.order ≤ 1 := d.minimal 1 hone
  have hnot0 : d.order ≠ 0 := by
    intro hzeroEq
    apply hzero
    simpa [hzeroEq] using d.witness
  have heq : d.order = 1 := by
    cases horder : d.order with
    | zero =>
        exact (hnot0 horder).elim
    | succ n =>
        cases n with
        | zero =>
            rfl
        | succ n =>
            have htwo : 2 ≤ d.order := by
              simp [horder]
            have htwo_le_one : 2 ≤ 1 := Nat.le_trans htwo hle
            exact (Nat.not_succ_le_self 1 htwo_le_one).elim
  refine ⟨heq, ?_⟩
  intro r hr hsingle i j hi hj
  rcases hsingle with ⟨i₀, _hi₀, hi₀⟩
  exact hr.trans (hi₀ i hi) (hr.symm (hi₀ j hj))

end CoherenceCalculus
