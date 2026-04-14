import CoherenceCalculus.Foundation.HFTCore

/-!
# Foundation.CharacteristicTransportCore

Minimal Chapter 7 transport interfaces on the rebuilt signed-count spine.

The manuscript's smooth transport language is represented here by explicit
interface data:

- one conservative transport law with Eulerian / Lagrangian / characteristic
  presentations
- the associated characteristic flux object
- a finite cellular conservative current on an explicit support
- a characteristic horizon realization above the active HFT-1 boundary spine

This keeps the active surface honest while avoiding any hidden import of
continuum analysis.
-/

namespace CoherenceCalculus

/-- Explicit datum relating the three manuscript presentations of one
conservative transport law. -/
structure ConservativeTransportDatum (Observer Label : Type) where
  eulerianResidual : Observer → SignedCount
  lagrangianResidual : Label → SignedCount
  characteristicResidual : Label → SignedCount
  eulerian_lagrangian :
    (∀ x : Observer, eulerianResidual x = SignedCount.zero) ↔
      (∀ a : Label, lagrangianResidual a = SignedCount.zero)
  eulerian_characteristic :
    (∀ x : Observer, eulerianResidual x = SignedCount.zero) ↔
      (∀ a : Label, characteristicResidual a = SignedCount.zero)

/-- Eulerian presentation of the conservative transport law. -/
def EulerianPresentation {Observer Label : Type}
    (data : ConservativeTransportDatum Observer Label) : Prop :=
  ∀ x : Observer, data.eulerianResidual x = SignedCount.zero

/-- Lagrangian presentation of the same transport law. -/
def LagrangianPresentation {Observer Label : Type}
    (data : ConservativeTransportDatum Observer Label) : Prop :=
  ∀ a : Label, data.lagrangianResidual a = SignedCount.zero

/-- Characteristic presentation of the same transport law. -/
def CharacteristicPresentation {Observer Label : Type}
    (data : ConservativeTransportDatum Observer Label) : Prop :=
  ∀ a : Label, data.characteristicResidual a = SignedCount.zero

/-- The three realized presentations are equivalent once the bridge datum is
fixed. -/
theorem observer_triad {Observer Label : Type}
    (data : ConservativeTransportDatum Observer Label) :
    EulerianPresentation data ↔
      LagrangianPresentation data ∧ CharacteristicPresentation data := by
  constructor
  · intro he
    exact ⟨data.eulerian_lagrangian.mp he, data.eulerian_characteristic.mp he⟩
  · intro h
    exact data.eulerian_lagrangian.mpr h.1

/-- A characteristic flux form is an explicit signed-count flux profile on the
realized transport domain. -/
abbrev CharacteristicFluxForm (Point : Type) : Type := Point → SignedCount

/-- Recursive finite sum of signed counts. -/
def signedCountListSum : List SignedCount → SignedCount
  | [] => SignedCount.zero
  | z :: zs => SignedCount.addCount z (signedCountListSum zs)

/-- Signed-count sum of a finite observable family. -/
def signedMapSum {α : Type} (f : α → SignedCount) (xs : List α) : SignedCount :=
  signedCountListSum (List.map f xs)

/-- Explicit witness for the flux differential identity attached to a
characteristic flux form. -/
structure CharacteristicFluxDatum (Observer Label Point : Type) where
  transport : ConservativeTransportDatum Observer Label
  flux : CharacteristicFluxForm Point
  differential : Observer → SignedCount
  differential_eq : ∀ x : Observer, differential x = transport.eulerianResidual x

/-- The packaged flux differential is exactly the Eulerian transport residual. -/
theorem flux_differential {Observer Label Point : Type}
    (data : CharacteristicFluxDatum Observer Label Point) (x : Observer) :
    data.differential x = data.transport.eulerianResidual x :=
  data.differential_eq x

/-- Explicit cut data for a conservative flux balance. -/
structure CutConservationDatum (Cut : Type) where
  flux : Cut → SignedCount
  initialCut : List Cut
  finalCut : List Cut
  sideCut : List Cut
  side_vanishes : ∀ σ : Cut, σ ∈ sideCut → flux σ = SignedCount.zero
  boundary_balance :
    signedMapSum flux finalCut =
      SignedCount.addCount (signedMapSum flux initialCut) (signedMapSum flux sideCut)

private theorem signedMapSum_eq_zero_of_mem_zero {α : Type}
    (f : α → SignedCount) (xs : List α)
    (hzero : ∀ x : α, x ∈ xs → f x = SignedCount.zero) :
    signedMapSum f xs = SignedCount.zero := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      dsimp [signedMapSum, signedCountListSum]
      rw [hzero x List.mem_cons_self, SignedCount.zero_addCount]
      apply ih
      intro y hy
      exact hzero y (List.mem_cons_of_mem x hy)

/-- Vanishing side flux reduces the Stokes balance to equality of the two
transverse cuts. -/
theorem cut_conservation {Cut : Type} (data : CutConservationDatum Cut) :
    signedMapSum data.flux data.finalCut = signedMapSum data.flux data.initialCut := by
  have hside : signedMapSum data.flux data.sideCut = SignedCount.zero := by
    exact signedMapSum_eq_zero_of_mem_zero data.flux data.sideCut data.side_vanishes
  rw [data.boundary_balance, hside, SignedCount.addCount_zero]

/-- Explicit finite integration-by-parts witness on the rebuilt signed-count
surface. -/
structure CharacteristicIBPDatum (Bulk Boundary : Type) where
  leftBulk : Bulk → SignedCount
  rightBulk : Bulk → SignedCount
  bulkCells : List Bulk
  boundaryFlux : Boundary → SignedCount
  boundaryCells : List Boundary
  ibp_balance :
    signedMapSum (fun x => SignedCount.addCount (leftBulk x) (rightBulk x)) bulkCells =
      signedMapSum boundaryFlux boundaryCells

private theorem signedMapSum_add {α : Type}
    (f g : α → SignedCount) (xs : List α) :
    signedMapSum (fun x => SignedCount.addCount (f x) (g x)) xs =
      SignedCount.addCount (signedMapSum f xs) (signedMapSum g xs) := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      dsimp [signedMapSum, signedCountListSum]
      change
        SignedCount.addCount (SignedCount.addCount (f x) (g x))
            (signedMapSum (fun y => SignedCount.addCount (f y) (g y)) xs) =
          SignedCount.addCount
            (SignedCount.addCount (f x) (signedMapSum f xs))
            (SignedCount.addCount (g x) (signedMapSum g xs))
      rw [ih]
      calc
        SignedCount.addCount (SignedCount.addCount (f x) (g x))
            (SignedCount.addCount (signedMapSum f xs) (signedMapSum g xs))
            =
            SignedCount.addCount (f x)
              (SignedCount.addCount (g x)
                (SignedCount.addCount (signedMapSum f xs) (signedMapSum g xs))) := by
                  rw [addCount_assoc]
        _ =
            SignedCount.addCount (f x)
              (SignedCount.addCount (signedMapSum f xs)
                (SignedCount.addCount (g x) (signedMapSum g xs))) := by
                  have hmid :
                      SignedCount.addCount (g x)
                        (SignedCount.addCount (signedMapSum f xs) (signedMapSum g xs)) =
                        SignedCount.addCount (signedMapSum f xs)
                          (SignedCount.addCount (g x) (signedMapSum g xs)) := by
                            calc
                              SignedCount.addCount (g x)
                                  (SignedCount.addCount (signedMapSum f xs) (signedMapSum g xs))
                                  =
                                  SignedCount.addCount
                                    (SignedCount.addCount (g x) (signedMapSum f xs))
                                    (signedMapSum g xs) := by
                                      rw [← addCount_assoc]
                              _ =
                                  SignedCount.addCount
                                    (SignedCount.addCount (signedMapSum f xs) (g x))
                                    (signedMapSum g xs) := by
                                      rw [addCount_comm (g x) (signedMapSum f xs)]
                              _ =
                                  SignedCount.addCount (signedMapSum f xs)
                                    (SignedCount.addCount (g x) (signedMapSum g xs)) := by
                                      rw [addCount_assoc]
                  exact congrArg (SignedCount.addCount (f x)) hmid
        _ =
            SignedCount.addCount (SignedCount.addCount (f x) (signedMapSum f xs))
              (SignedCount.addCount (g x) (signedMapSum g xs)) := by
                  rw [← addCount_assoc]

/-- Characteristic integration by parts on an explicitly supplied finite bulk /
boundary witness. -/
theorem characteristic_ibp {Bulk Boundary : Type}
    (data : CharacteristicIBPDatum Bulk Boundary) :
    signedMapSum (fun x => SignedCount.addCount (data.leftBulk x) (data.rightBulk x)) data.bulkCells =
      signedMapSum data.boundaryFlux data.boundaryCells :=
  data.ibp_balance

/-- If the first bulk contribution vanishes pointwise, the characteristic
integration-by-parts identity reduces to a pure boundary term. -/
theorem characteristic_boundary_reduction {Bulk Boundary : Type}
    (data : CharacteristicIBPDatum Bulk Boundary)
    (hleft : ∀ x : Bulk, x ∈ data.bulkCells → data.leftBulk x = SignedCount.zero) :
    signedMapSum data.rightBulk data.bulkCells =
      signedMapSum data.boundaryFlux data.boundaryCells := by
  have hsum_left : signedMapSum data.leftBulk data.bulkCells = SignedCount.zero := by
    exact signedMapSum_eq_zero_of_mem_zero data.leftBulk data.bulkCells hleft
  calc
    signedMapSum data.rightBulk data.bulkCells
        = SignedCount.addCount (signedMapSum data.leftBulk data.bulkCells)
            (signedMapSum data.rightBulk data.bulkCells) := by
              rw [hsum_left, SignedCount.zero_addCount]
    _ = signedMapSum (fun x => SignedCount.addCount (data.leftBulk x) (data.rightBulk x)) data.bulkCells := by
          symm
          exact signedMapSum_add data.leftBulk data.rightBulk data.bulkCells
    _ = signedMapSum data.boundaryFlux data.boundaryCells := data.ibp_balance

/-- Finite cellular conservative current on an explicit `2`-cell support. -/
structure CellularConservativeCurrent (Edge Face : Type) where
  current : Edge → SignedCount
  coboundary : Face → SignedCount
  support : List Face
  conservative : ∀ σ : Face, σ ∈ support → coboundary σ = SignedCount.zero

/-- Explicit cellular cut data attached to a conservative current. -/
structure CellularCutDatum (Edge Face : Type) where
  currentData : CellularConservativeCurrent Edge Face
  lowerCycle : List Edge
  upperCycle : List Edge
  boundary_balance :
    signedMapSum currentData.current upperCycle =
      SignedCount.addCount
        (signedMapSum currentData.current lowerCycle)
        (signedMapSum currentData.coboundary currentData.support)

/-- A cellular conservative current has equal signed-count flux on any two
cycles differing by the boundary of its support. -/
theorem cellular_cut_conservation {Edge Face : Type}
    (data : CellularCutDatum Edge Face) :
    signedMapSum data.currentData.current data.upperCycle =
      signedMapSum data.currentData.current data.lowerCycle := by
  have hzero : signedMapSum data.currentData.coboundary data.currentData.support = SignedCount.zero := by
    exact signedMapSum_eq_zero_of_mem_zero
      data.currentData.coboundary data.currentData.support data.currentData.conservative
  rw [data.boundary_balance, hzero, SignedCount.addCount_zero]

/-- Characteristic horizon realizations are the rebuilt Chapter 7 data:
the active horizon tower together with a transport family preserving both the
canonical boundary and every horizon cut. -/
structure CharacteristicHorizonRealization (Time : Type) where
  tower : HorizonTower
  U : Time → AddMap
  boundary_comm : ∀ t : Time, ∀ x : State, U t (trueBoundary x) = trueBoundary (U t x)
  horizon_comm :
    ∀ t : Time, ∀ h : Nat, ∀ x : State, U t ((tower.π h).toFun x) = (tower.π h).toFun (U t x)

private theorem map_sub (A : AddMap) (x y : State) :
    A (State.sub x y) = State.sub (A x) (A y) := by
  rw [State.sub_eq_add_negate, A.map_add, AddMap.map_negate, State.sub_eq_add_negate]

private theorem transport_shadow {Time : Type}
    (R : CharacteristicHorizonRealization Time) (t : Time) (h : Nat) (x : State) :
    R.U t (shadowProj R.tower h x) = shadowProj R.tower h (R.U t x) := by
  unfold shadowProj
  rw [map_sub (R.U t) x ((R.tower.π h).toFun x), R.horizon_comm t h x]

private theorem transport_observedBoundary {Time : Type}
    (R : CharacteristicHorizonRealization Time) (t : Time) (h : Nat) (x : State) :
    R.U t (observedBoundary R.tower h x) = observedBoundary R.tower h (R.U t x) := by
  unfold observedBoundary observedOp
  calc
    R.U t ((R.tower.π h).toFun (trueBoundary ((R.tower.π h).toFun x)))
        = (R.tower.π h).toFun (R.U t (trueBoundary ((R.tower.π h).toFun x))) := by
            exact R.horizon_comm t h (trueBoundary ((R.tower.π h).toFun x))
    _ = (R.tower.π h).toFun (trueBoundary (R.U t ((R.tower.π h).toFun x))) := by
          rw [R.boundary_comm t ((R.tower.π h).toFun x)]
    _ = (R.tower.π h).toFun (trueBoundary ((R.tower.π h).toFun (R.U t x))) := by
          rw [R.horizon_comm t h x]
    _ = observedBoundary R.tower h (R.U t x) := by
          rfl

private theorem transport_boundaryLeakage {Time : Type}
    (R : CharacteristicHorizonRealization Time) (t : Time) (h : Nat) (x : State) :
    R.U t (boundaryLeakage R.tower h x) = boundaryLeakage R.tower h (R.U t x) := by
  unfold boundaryLeakage leakageOp
  calc
    R.U t (shadowProj R.tower h (trueBoundary ((R.tower.π h).toFun x)))
        = shadowProj R.tower h (R.U t (trueBoundary ((R.tower.π h).toFun x))) := by
            exact transport_shadow R t h (trueBoundary ((R.tower.π h).toFun x))
    _ = shadowProj R.tower h (trueBoundary (R.U t ((R.tower.π h).toFun x))) := by
          rw [R.boundary_comm t ((R.tower.π h).toFun x)]
    _ = shadowProj R.tower h (trueBoundary ((R.tower.π h).toFun (R.U t x))) := by
          rw [R.horizon_comm t h x]
    _ = boundaryLeakage R.tower h (R.U t x) := by
          rfl

private theorem transport_boundaryReturn {Time : Type}
    (R : CharacteristicHorizonRealization Time) (t : Time) (h : Nat) (x : State) :
    R.U t (boundaryReturn R.tower h x) = boundaryReturn R.tower h (R.U t x) := by
  unfold boundaryReturn returnOp
  calc
    R.U t ((R.tower.π h).toFun (trueBoundary (shadowProj R.tower h x)))
        = (R.tower.π h).toFun (R.U t (trueBoundary (shadowProj R.tower h x))) := by
            exact R.horizon_comm t h (trueBoundary (shadowProj R.tower h x))
    _ = (R.tower.π h).toFun (trueBoundary (R.U t (shadowProj R.tower h x))) := by
          rw [R.boundary_comm t (shadowProj R.tower h x)]
    _ = (R.tower.π h).toFun (trueBoundary (shadowProj R.tower h (R.U t x))) := by
          rw [transport_shadow R t h x]
    _ = boundaryReturn R.tower h (R.U t x) := by
          rfl

private theorem transport_boundaryDefect {Time : Type}
    (R : CharacteristicHorizonRealization Time) (t : Time) (h : Nat) (x : State) :
    R.U t (boundaryDefect R.tower h x) = boundaryDefect R.tower h (R.U t x) := by
  calc
    R.U t (boundaryDefect R.tower h x)
        = R.U t (boundaryReturn R.tower h (boundaryLeakage R.tower h x)) := by
            rfl
    _ = boundaryReturn R.tower h (R.U t (boundaryLeakage R.tower h x)) := by
          exact transport_boundaryReturn R t h (boundaryLeakage R.tower h x)
    _ = boundaryReturn R.tower h (boundaryLeakage R.tower h (R.U t x)) := by
          rw [transport_boundaryLeakage R t h x]
    _ = boundaryDefect R.tower h (R.U t x) := by
          rfl

/-- For an observed state, the full boundary splits into the observed boundary
and its leakage through the horizon, and HFT-1 identifies the square of the
observed boundary with the negated defect. -/
theorem through_horizon_decomposition {Time : Type}
    (R : CharacteristicHorizonRealization Time) (h : Nat) (u : State)
    (hu : (R.tower.π h).toFun u = u) :
    trueBoundary u = State.add (observedBoundary R.tower h u) (boundaryLeakage R.tower h u) ∧
      observedBoundary R.tower h (observedBoundary R.tower h u) =
        State.negate (boundaryDefect R.tower h u) := by
  constructor
  · have hsplit :
        trueBoundary ((R.tower.π h).toFun u) =
          State.add (observedBoundary R.tower h u) (boundaryLeakage R.tower h u) := by
      simpa [observedBoundary, boundaryLeakage] using
        (observed_leakage_split R.tower h trueBoundary u).symm
    calc
      trueBoundary u = trueBoundary ((R.tower.π h).toFun u) := by
        exact congrArg trueBoundary hu.symm
      _ = State.add (observedBoundary R.tower h u) (boundaryLeakage R.tower h u) := hsplit
  · exact HFT1_boundary_exact R.tower h u

/-- Every characteristic horizon realization satisfies the active HFT-1 law, and
its observed boundary / defect are transported equivariantly by the chosen
conservative evolution. -/
theorem characteristic_realization {Time : Type}
    (R : CharacteristicHorizonRealization Time) (t : Time) (h : Nat) (x : State) :
    observedBoundary R.tower h (observedBoundary R.tower h x) =
      State.negate (boundaryDefect R.tower h x) ∧
      R.U t (observedBoundary R.tower h x) = observedBoundary R.tower h (R.U t x) ∧
      R.U t (boundaryDefect R.tower h x) = boundaryDefect R.tower h (R.U t x) := by
  refine ⟨HFT1_boundary_exact R.tower h x, transport_observedBoundary R t h x,
    transport_boundaryDefect R t h x⟩

/-- Any characteristic horizon realization inherits the active Part I boundary
calculus unchanged. -/
theorem transfer_part_one {Time : Type}
    (R : CharacteristicHorizonRealization Time) :
    (∀ x : State, trueBoundary (trueBoundary x) = State.zero) ∧
      (∀ h : Nat, ∀ x : State,
        observedBoundary R.tower h (observedBoundary R.tower h x) =
          State.negate (boundaryDefect R.tower h x)) := by
  refine ⟨fullBoundary_closes, ?_⟩
  intro h x
  exact HFT1_boundary_exact R.tower h x

end CoherenceCalculus
