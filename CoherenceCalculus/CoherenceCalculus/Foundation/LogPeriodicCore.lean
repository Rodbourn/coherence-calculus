import CoherenceCalculus.Foundation.OperatorCore

/-!
# Foundation.LogPeriodicCore

Minimal log-periodic horizon scaffolding rebuilt on the active projection and
operator spine.

This keeps only the manuscript-facing structural content needed on the current
certified surface:
- log-indexed horizon towers
- three-level telescoping for log-scale differences
- the dyadic special case
- defect simplification for states already represented at a base log-scale
-/

namespace CoherenceCalculus

/-- A log-scale horizon tower is a horizon tower equipped with a strictly
increasing finite list of scale indices. -/
structure LogScaleHorizonTower (n : Nat) where
  tower : HorizonTower
  ell : Fin n → Nat
  increasing : ∀ (i j : Fin n), i.val < j.val → ell i < ell j

namespace LogScaleHorizonTower

variable {n : Nat}

/-- Projection at the `i`-th log-scale slot. -/
def lsPi (L : LogScaleHorizonTower n) (i : Fin n) : Projection :=
  L.tower.π (L.ell i)

end LogScaleHorizonTower

private theorem state_sub_telescope (a b c : State) :
    State.add (State.sub b a) (State.sub c b) = State.sub c a := by
  apply (State.sub_eq_right_of_add_left ?_).symm
  calc
    State.add a (State.add (State.sub b a) (State.sub c b))
        = State.add (State.add a (State.sub b a)) (State.sub c b) := by
            rw [State.add_assoc]
    _ = State.add b (State.sub c b) := by
          rw [State.add_sub_cancel_left]
    _ = c := by
          rw [State.add_sub_cancel_left]

/-- Three consecutive log-scale increments telescope to the endpoint difference. -/
theorem log_telescope_3
    {n : Nat} (L : LogScaleHorizonTower n) (i j k : Fin n)
    (_hij : i.val < j.val) (_hjk : j.val < k.val) (x : State) :
    State.add
      (State.sub ((L.lsPi j).toFun x) ((L.lsPi i).toFun x))
      (State.sub ((L.lsPi k).toFun x) ((L.lsPi j).toFun x)) =
      State.sub ((L.lsPi k).toFun x) ((L.lsPi i).toFun x) := by
  exact state_sub_telescope ((L.lsPi i).toFun x) ((L.lsPi j).toFun x) ((L.lsPi k).toFun x)

/-- Dyadic log-scale towers are uniformly spaced log-scale towers. -/
structure DyadicTower (n : Nat) extends LogScaleHorizonTower n where
  base : Nat
  spacing : Nat
  spacing_pos : 0 < spacing
  uniform : ∀ i : Fin n, ell i = base + i.val * spacing

namespace DyadicTower

variable {n : Nat}

/-- The dyadic special case inherits the same three-level telescoping law. -/
theorem dyadic_telescoping
    (D : DyadicTower n) (i j k : Fin n)
    (hij : i.val < j.val) (hjk : j.val < k.val) (x : State) :
    State.add
      (State.sub ((D.toLogScaleHorizonTower.lsPi j).toFun x)
        ((D.toLogScaleHorizonTower.lsPi i).toFun x))
      (State.sub ((D.toLogScaleHorizonTower.lsPi k).toFun x)
        ((D.toLogScaleHorizonTower.lsPi j).toFun x)) =
      State.sub ((D.toLogScaleHorizonTower.lsPi k).toFun x)
        ((D.toLogScaleHorizonTower.lsPi i).toFun x) := by
  exact log_telescope_3 D.toLogScaleHorizonTower i j k hij hjk x

end DyadicTower

private theorem representable_fixed
    {n : Nat} (L : LogScaleHorizonTower n) (i₀ i : Fin n)
    (hle : i₀.val ≤ i.val) (x : State)
    (hx : (L.lsPi i₀).toFun x = x) :
    (L.lsPi i).toFun x = x := by
  have hEll : L.ell i₀ ≤ L.ell i := by
    cases Nat.lt_or_eq_of_le hle with
    | inl hlt =>
        exact Nat.le_of_lt (L.increasing i₀ i hlt)
    | inr heq =>
        cases i₀
        cases i
        cases heq
        exact Nat.le_refl _
  calc
    (L.lsPi i).toFun x = (L.lsPi i).toFun ((L.lsPi i₀).toFun x) := by rw [hx]
    _ = (L.lsPi i₀).toFun x := by
          exact L.tower.nested_ge (L.ell i) (L.ell i₀) hEll x
    _ = x := hx

/-- For states already represented at a base log-scale, leakage at any finer
log-scale is exactly the shadow of the operator image. -/
theorem log_defect_monotonicity
    {n : Nat} (L : LogScaleHorizonTower n) (i₀ i : Fin n)
    (hle : i₀.val ≤ i.val) (A : AddMap) (x : State)
    (hx : (L.lsPi i₀).toFun x = x) :
    AddMap.leakageMap L.tower (L.ell i) A x =
      shadowProj L.tower (L.ell i) (A x) := by
  rw [AddMap.leakageMap_apply]
  unfold leakageOp
  change shadowProj L.tower (L.ell i) (A ((L.lsPi i).toFun x)) =
    shadowProj L.tower (L.ell i) (A x)
  rw [representable_fixed L i₀ i hle x hx]

end CoherenceCalculus
