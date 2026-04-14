import CoherenceCalculus.Foundation.ProjectionCalculusCore
import CoherenceCalculus.Foundation.PairingCore
import CoherenceCalculus.Foundation.TowerCalculusCore

/-!
# Foundation.ResolventInterfaceCore

Interface-level resolvent facts on the rebuilt additive state space.

This module does not reintroduce the archived `LinOp`/spectral layer. Instead it
packages the manuscript's resolvent-facing names directly on:

- rebuilt projections `Projection`
- additive endomaps `AddMap`
- explicit Schur corrections `schurComplement`
- explicit energy-adjoint hypotheses via `HasEnergyAdjoint`
- explicit transport hypotheses for functoriality

The goal is to keep the active Part I surface aligned with the manuscript while
remaining fully inside the bedrock-clean rebuilt foundation chain.
-/

namespace CoherenceCalculus

namespace AddMap

/-- Additive endomaps preserve rebuilt state subtraction. -/
theorem map_sub (A : AddMap) (x y : State) :
    A (State.sub x y) = State.sub (A x) (A y) := by
  rw [State.sub_eq_add_negate, A.map_add, map_negate, State.sub_eq_add_negate]

end AddMap

/-- Explicit perturbation data for a Schur split. -/
structure PerturbationData (P : Projection) (A E : AddMap) where
  perturbed : AddMap := AddMap.add A E
  baseShadowResolvent : HasResolvent (blockQQ P A)
  perturbedShadowResolvent : HasResolvent (blockQQ P perturbed)

/-- Pointwise Schur-correction difference between a base operator and its
perturbation. -/
def schurPerturbationDiff
    (P : Projection) (A E : AddMap) (pd : PerturbationData P A E) (x : State) :
    State :=
  State.sub
    (schurComplement P pd.perturbed pd.perturbedShadowResolvent.inverse x)
    (schurComplement P A pd.baseShadowResolvent.inverse x)

/-- The Schur correction still factors as transport in, internal propagation,
and transport out; this is the exact algebraic content used later for norm
bounds. -/
theorem schur_factorization_bound (P : Projection) (A Rqq : AddMap) (x : State) :
    schurComplement P A Rqq x = blockPQ P A (Rqq (blockQP P A x)) := by
  exact schur_factorization P A Rqq x

/-- The manuscript's self-adjoint transport relation, expressed in the rebuilt
energy-pairing language. -/
theorem selfadjoint_block_relation
    (P : Projection) (A : AddMap)
    (hadj : HasEnergyAdjoint (blockPQ P A) (blockQP P A))
    (x y : State) :
    State.pair (blockPQ P A x) y = State.pair x (blockQP P A y) := by
  exact hadj x y

/-- The leading Schur correction is energy-self-adjoint whenever the transport
blocks are mutual energy adjoints. -/
theorem schur_selfadjoint_leading
    (P : Projection) (A : AddMap)
    (hadjPQ : HasEnergyAdjoint (blockPQ P A) (blockQP P A))
    (hadjQP : HasEnergyAdjoint (blockQP P A) (blockPQ P A))
    (x y : State) :
    State.pair (schurComplement P A AddMap.id x) y =
      State.pair x (schurComplement P A AddMap.id y) := by
  unfold schurComplement
  change
    State.pair (blockPQ P A (AddMap.id (blockQP P A x))) y =
      State.pair x (blockPQ P A (AddMap.id (blockQP P A y)))
  change
    State.pair (blockPQ P A (blockQP P A x)) y =
      State.pair x (blockPQ P A (blockQP P A y))
  calc
    State.pair (blockPQ P A (blockQP P A x)) y
        = State.pair (blockQP P A x) (blockQP P A y) := by
            exact hadjPQ (blockQP P A x) y
    _ = State.pair x (blockPQ P A (blockQP P A y)) := by
          exact hadjQP x (blockQP P A y)

/-- Horizon specialization is just the generic Schur correction evaluated at the
canonical projection cut of the horizon tower. -/
theorem horizon_schur_via_spec
    (T : HorizonTower) (h : Nat) (A Rqq : AddMap) (x : State) :
    schurComplement (HorizonSpecialization T h).proj A Rqq x =
      schurComplement (T.π h) A Rqq x := by
  rfl

private theorem projectionShadow_transport
    (P P' : Projection) (U : AddMap)
    (hproj : ∀ x, P' (U x) = U (P x))
    (x : State) :
    projectionShadow P' (U x) = U (projectionShadow P x) := by
  unfold projectionShadow
  rw [AddMap.map_sub U x (P x), hproj x]

/-- Exact transport functoriality of the split transform under any additive
state transport that intertwines the projection, operator, and chosen
shadow propagator. This is the rebuilt analogue of unitary-conjugacy
invariance. -/
theorem split_functoriality
    (P P' : Projection) (A A' Rqq Rqq' U : AddMap)
    (hproj : ∀ x, P' (U x) = U (P x))
    (hop : ∀ x, A' (U x) = U (A x))
    (hres : ∀ x, Rqq' (U x) = U (Rqq x))
    (x : State) :
    schurComplement P' A' Rqq' (U x) = U (schurComplement P A Rqq x) ∧
      effectiveOp P' A' Rqq' (U x) = U (effectiveOp P A Rqq x) := by
  have hPP : ∀ y, blockPP P' A' (U y) = U (blockPP P A y) := by
    intro y
    change P' (A' (P' (U y))) = U (P (A (P y)))
    rw [hproj y, hop (P y), hproj (A (P y))]
  have hPQ : ∀ y, blockPQ P' A' (U y) = U (blockPQ P A y) := by
    intro y
    change P' (A' (projectionShadow P' (U y))) =
      U (P (A (projectionShadow P y)))
    rw [projectionShadow_transport P P' U hproj y]
    rw [hop (projectionShadow P y)]
    rw [hproj (A (projectionShadow P y))]
  have hQP : ∀ y, blockQP P' A' (U y) = U (blockQP P A y) := by
    intro y
    change projectionShadow P' (A' (P' (U y))) =
      U (projectionShadow P (A (P y)))
    rw [hproj y, hop (P y)]
    exact projectionShadow_transport P P' U hproj (A (P y))
  have hschur :
      schurComplement P' A' Rqq' (U x) = U (schurComplement P A Rqq x) := by
    change blockPQ P' A' (Rqq' (blockQP P' A' (U x))) =
      U (blockPQ P A (Rqq (blockQP P A x)))
    rw [hQP x, hres (blockQP P A x), hPQ (Rqq (blockQP P A x))]
  constructor
  · exact hschur
  · unfold effectiveOp
    change State.add (blockPP P' A' (U x)) (schurComplement P' A' Rqq' (U x)) =
      U (State.add (blockPP P A x) (schurComplement P A Rqq x))
    rw [hPP x, hschur]
    exact (U.map_add (blockPP P A x) (schurComplement P A Rqq x)).symm

/-- Explicit algebraic associativity criterion for nested Schur elimination:
if eliminating a finer split preserves the coarse transport blocks, then the
coarse Schur correction is unchanged. -/
theorem nestedSchurAssociativity
    (np : NestedProjections) (A Rcoarse Rfine : AddMap)
    (htransportIn :
      ∀ x, blockPQ np.coarse (effectiveOp np.fine A Rfine) x = blockPQ np.coarse A x)
    (htransportOut :
      ∀ x, blockQP np.coarse (effectiveOp np.fine A Rfine) x = blockQP np.coarse A x)
    (x : State) :
    schurComplement np.coarse A Rcoarse x =
      schurComplement np.coarse (effectiveOp np.fine A Rfine) Rcoarse x := by
  calc
    schurComplement np.coarse A Rcoarse x
        = blockPQ np.coarse A (Rcoarse (blockQP np.coarse A x)) := by
            rfl
    _ = blockPQ np.coarse (effectiveOp np.fine A Rfine)
          (Rcoarse (blockQP np.coarse A x)) := by
            symm
            exact htransportIn (Rcoarse (blockQP np.coarse A x))
    _ = blockPQ np.coarse (effectiveOp np.fine A Rfine)
          (Rcoarse (blockQP np.coarse (effectiveOp np.fine A Rfine) x)) := by
            have harg :
                Rcoarse (blockQP np.coarse A x) =
                  Rcoarse (blockQP np.coarse (effectiveOp np.fine A Rfine) x) := by
              exact congrArg Rcoarse (htransportOut x).symm
            rw [harg]
    _ = schurComplement np.coarse (effectiveOp np.fine A Rfine) Rcoarse x := by
          rfl

/-- Multiplicative determinant data on the rebuilt additive operator layer. -/
structure MultiplicativeDet where
  det : AddMap → Nat
  det_comp : ∀ A B : AddMap, det (AddMap.comp A B) = det A * det B

/-- Explicit witness that an operator admits a two-factor Schur determinant
factorization against a chosen observable/shadow split. -/
structure SchurDetFactorizationData
    (P : Projection) (A Rqq : AddMap) (d : MultiplicativeDet) where
  shadowFactor : AddMap
  observableFactor : AddMap
  factorization : A = AddMap.comp shadowFactor observableFactor
  shadow_det : d.det shadowFactor = d.det (blockQQ P A)
  observable_det : d.det observableFactor = d.det (effectiveOp P A Rqq)

/-- Determinant factorization for any explicitly supplied Schur split
factorization witness. -/
theorem det_factorization
    (P : Projection) (A Rqq : AddMap) (d : MultiplicativeDet)
    (data : SchurDetFactorizationData P A Rqq d) :
    d.det A = d.det (blockQQ P A) * d.det (effectiveOp P A Rqq) := by
  cases data with
  | mk shadowFactor observableFactor factorization shadow_det observable_det =>
      cases factorization
      calc
        d.det (AddMap.comp shadowFactor observableFactor)
            = d.det shadowFactor * d.det observableFactor := by
                exact d.det_comp shadowFactor observableFactor
        _ = d.det (blockQQ P (AddMap.comp shadowFactor observableFactor)) *
              d.det observableFactor := by
                rw [shadow_det]
        _ = d.det (blockQQ P (AddMap.comp shadowFactor observableFactor)) *
              d.det (effectiveOp P (AddMap.comp shadowFactor observableFactor) Rqq) := by
                rw [observable_det]

/-- Determinant ratio identity, stated without division in the rebuilt additive
setting. -/
theorem det_ratio
    (P : Projection) (A Rqq : AddMap) (d : MultiplicativeDet)
    (data : SchurDetFactorizationData P A Rqq d) :
    d.det (blockQQ P A) * d.det (effectiveOp P A Rqq) = d.det A := by
  exact (det_factorization P A Rqq d data).symm

/-- First-variation structure of the Schur correction once the block and
resolvent variations have been supplied explicitly. -/
theorem schur_complement_variation_structure
    (δPQ PQ Rqq δRqq QP δQP : AddMap) (x : State) :
    AddMap.add
      (AddMap.comp δPQ (AddMap.comp Rqq QP))
      (AddMap.add
        (AddMap.comp PQ (AddMap.comp δRqq QP))
        (AddMap.comp PQ (AddMap.comp Rqq δQP))) x
      =
    State.add
      (δPQ (Rqq (QP x)))
      (State.add (PQ (δRqq (QP x))) (PQ (Rqq (δQP x)))) := by
  rfl

/-- Explicit eventual-equality witness on the rebuilt state space. -/
structure EventuallyEqData (f : Nat → State) (target : State) where
  cutoff : Nat
  stable : ∀ h : Nat, cutoff ≤ h → f h = target

namespace AddMap

/-- Recursive additive-map powers for iterated shadow transport. -/
def pow (A : AddMap) : Nat → AddMap
  | 0 => id
  | n + 1 => comp A (pow A n)

end AddMap

/-- Tower transport-order bounds multiply linearly under explicit additive-map
powers. -/
theorem towerTransportOrder_pow
    (T : HorizonTower) (arith : TowerOrderArithmeticDatum T)
    {A : AddMap} {r : Nat}
    (hA : towerTransportOrderAtMost T A r) :
    ∀ n : Nat, towerTransportOrderAtMost T (AddMap.pow A n) (n * r)
  | 0 => by
      rw [Nat.zero_mul]
      exact towerTransportOrder_id T
  | n + 1 => by
      have hpow : towerTransportOrderAtMost T (AddMap.pow A n) (n * r) :=
        towerTransportOrder_pow T arith hA n
      have hcomp : towerTransportOrderAtMost T (AddMap.pow A (n + 1)) (r + n * r) :=
        arith.comp_rule hA hpow
      have hbound : r + n * r ≤ (n + 1) * r := by
        calc
          r + n * r = n * r + r := by
            exact Nat.add_comm r (n * r)
          _ = (n + 1) * r := by
            exact (Nat.succ_mul n r).symm
          _ ≤ (n + 1) * r := by
            exact Nat.le_refl ((n + 1) * r)
      exact towerTransportOrderAtMost_mono T hcomp hbound

/-- General projection-level Schur transport jet. The zeroth term is the
observable block, and every higher term is one observable-to-shadow transport,
an internal shadow excursion, and a shadow-to-observable return. -/
def schur_transport_jet (P : Projection) (A : AddMap) : Nat → AddMap
  | 0 => blockPP P A
  | n + 1 =>
      AddMap.comp (blockPQ P A)
        (AddMap.comp (AddMap.pow (blockQQ P A) n) (blockQP P A))

/-- Every Schur transport-jet coefficient inherits an explicit tower
transport-order bound from the underlying operator. -/
theorem schur_transport_jet_coefficient_order
    (T : HorizonTower) (arith : TowerOrderArithmeticDatum T)
    (A : AddMap) {r h : Nat}
    (hA : towerTransportOrderAtMost T A r) :
    ∀ n : Nat,
      towerTransportOrderAtMost T (schur_transport_jet (T.π h) A n) ((n + 1) * r)
  | 0 => by
      change towerTransportOrderAtMost T (blockPP (T.π h) A) ((0 + 1) * r)
      rw [Nat.zero_add, Nat.one_mul]
      exact towerTransportOrder_blockPP T arith h hA
  | n + 1 => by
      unfold schur_transport_jet
      have hPQ : towerTransportOrderAtMost T (blockPQ (T.π h) A) r :=
        towerTransportOrder_blockPQ T arith h hA
      have hQQ : towerTransportOrderAtMost T (blockQQ (T.π h) A) r :=
        towerTransportOrder_blockQQ T arith h hA
      have hQQpow :
          towerTransportOrderAtMost T (AddMap.pow (blockQQ (T.π h) A) n) (n * r) :=
        towerTransportOrder_pow T arith hQQ n
      have hQP : towerTransportOrderAtMost T (blockQP (T.π h) A) r :=
        towerTransportOrder_blockQP T arith h hA
      have hinner :
          towerTransportOrderAtMost T
            (AddMap.comp (AddMap.pow (blockQQ (T.π h) A) n) (blockQP (T.π h) A))
            (n * r + r) :=
        arith.comp_rule hQQpow hQP
      have houter :
          towerTransportOrderAtMost T
            (AddMap.comp (blockPQ (T.π h) A)
              (AddMap.comp (AddMap.pow (blockQQ (T.π h) A) n) (blockQP (T.π h) A)))
            (r + (n * r + r)) :=
        arith.comp_rule hPQ hinner
      have hbound : r + (n * r + r) ≤ ((n + 1) + 1) * r := by
        calc
          r + (n * r + r) = (r + n * r) + r := by
            exact (Nat.add_assoc r (n * r) r).symm
          _ = (n * r + r) + r := by
            rw [Nat.add_comm r (n * r)]
          _ = ((n + 1) * r) + r := by
            rw [Nat.succ_mul]
          _ = ((n + 1) + 1) * r := by
            exact (Nat.succ_mul (n + 1) r).symm
          _ ≤ ((n + 1) + 1) * r := by
            exact Nat.le_refl (((n + 1) + 1) * r)
      exact towerTransportOrderAtMost_mono T houter hbound

/-- Constructive order profile of the Schur transport jet. The zeroth
coefficient keeps the base order, each higher coefficient grows linearly with
its excursion length, and therefore the jet carries an explicit finite-order
profile at every horizon. -/
theorem schur_transport_jet_order
    (T : HorizonTower) (arith : TowerOrderArithmeticDatum T)
    (A : AddMap) {r h : Nat}
    (hA : towerTransportOrderAtMost T A r) :
    towerTransportOrderAtMost T (schur_transport_jet (T.π h) A 0) r ∧
      (∀ n : Nat,
        towerTransportOrderAtMost T
          (schur_transport_jet (T.π h) A (n + 1))
          ((n + 2) * r)) ∧
      (∀ n : Nat,
        towerTransportOrderAtMost T
          (schur_transport_jet (T.π h) A n)
          ((n + 1) * r)) := by
  have hcoeff := schur_transport_jet_coefficient_order T arith A (h := h) hA
  refine ⟨?_, ?_, ?_⟩
  · exact towerTransportOrder_blockPP T arith h hA
  · intro n
    change towerTransportOrderAtMost T
      (schur_transport_jet (T.π h) A (Nat.succ n))
      ((Nat.succ n + 1) * r)
    exact hcoeff (Nat.succ n)
  · intro n
    exact hcoeff n

/-- Exact Schur tower data across a horizon tower. -/
structure ExactSchurTowerGeneralData (T : HorizonTower) (A : AddMap) where
  shadowResolvent : ∀ h : Nat, HasResolvent (blockQQ (T.π h) A)

/-- Exact Schur tower obtained by evaluating the effective observable operator
at each horizon using the supplied shadow resolvent witness. -/
def exact_schur_tower_general
    (T : HorizonTower) (A : AddMap) (data : ExactSchurTowerGeneralData T A) :
    Nat → AddMap :=
  fun h => effectiveOp (T.π h) A (data.shadowResolvent h).inverse

/-- Cross-horizon Schur coherence: coarse effective data is recovered by
performing the coarse split transform on any finer effective representative,
using the same coarse shadow propagator. -/
def schur_coherent_family_general
    (T : HorizonTower) (R : Nat → AddMap) (family : Nat → AddMap) : Prop :=
  ∀ h k : Nat, h ≤ k → ∀ x : State,
    family h x = effectiveOp (T.π h) (family k) (R h) x

private def eventuallyEq_add
    {f g : Nat → State} {x y : State}
    (hf : EventuallyEqData f x)
    (hg : EventuallyEqData g y) :
    EventuallyEqData (fun h => State.add (f h) (g h)) (State.add x y) := by
  refine ⟨Nat.max hf.cutoff hg.cutoff, ?_⟩
  intro h hh
  have hhf : hf.cutoff ≤ h := Nat.le_trans (Nat.le_max_left hf.cutoff hg.cutoff) hh
  have hhg : hg.cutoff ≤ h := Nat.le_trans (Nat.le_max_right hf.cutoff hg.cutoff) hh
  calc
    State.add (f h) (g h)
        = State.add x (g h) := by rw [hf.stable h hhf]
    _ = State.add x y := by rw [hg.stable h hhg]

private def horizonNestedProjections
    (T : HorizonTower) (h k : Nat) (hle : h ≤ k) : NestedProjections where
  coarse := T.π h
  fine := T.π k
  nested := by
    intro x
    exact nested_proj_comp T h k hle x
  nested_ge := by
    intro x
    exact nested_proj_comp_ge T k h hle x

/-- Exact Schur towers are Schur-coherent whenever the once-eliminated finer
operator preserves the coarse observable block and coarse transport blocks. -/
theorem exact_schur_coherence_general
    (T : HorizonTower) (A : AddMap) (data : ExactSchurTowerGeneralData T A)
    (hblockPP :
      ∀ h k : Nat, ∀ _hle : h ≤ k, ∀ x : State,
        blockPP (T.π h) (exact_schur_tower_general T A data k) x =
          blockPP (T.π h) A x)
    (htransportIn :
      ∀ h k : Nat, ∀ _hle : h ≤ k, ∀ x : State,
        blockPQ (T.π h) (exact_schur_tower_general T A data k) x =
          blockPQ (T.π h) A x)
    (htransportOut :
      ∀ h k : Nat, ∀ _hle : h ≤ k, ∀ x : State,
        blockQP (T.π h) (exact_schur_tower_general T A data k) x =
          blockQP (T.π h) A x) :
    schur_coherent_family_general T
      (fun h => (data.shadowResolvent h).inverse)
      (exact_schur_tower_general T A data) := by
  intro h k hle x
  let tower : Nat → AddMap := exact_schur_tower_general T A data
  have hschur :
      schurComplement (T.π h) A ((data.shadowResolvent h).inverse) x =
        schurComplement (T.π h) (tower k) ((data.shadowResolvent h).inverse) x := by
    simpa [tower, exact_schur_tower_general] using
      nestedSchurAssociativity
        (horizonNestedProjections T h k hle)
        A
        ((data.shadowResolvent h).inverse)
        ((data.shadowResolvent k).inverse)
        (htransportIn h k hle)
        (htransportOut h k hle)
        x
  calc
    exact_schur_tower_general T A data h x
        = State.add
            (blockPP (T.π h) A x)
            (schurComplement (T.π h) A ((data.shadowResolvent h).inverse) x) := by
              rfl
    _ = State.add
          (blockPP (T.π h) (tower k) x)
          (schurComplement (T.π h) (tower k) ((data.shadowResolvent h).inverse) x) := by
            rw [hschur, hblockPP h k hle x]
    _ = effectiveOp (T.π h) (tower k) ((data.shadowResolvent h).inverse) x := by
          rfl

/-- Strong recovery of the underlying additive map from an exact Schur tower is
reduced to eventual recovery of the observable block together with eventual
vanishing of the Schur correction. -/
theorem schur_tower_strong_recovery_general
    (T : HorizonTower) (A : AddMap) (data : ExactSchurTowerGeneralData T A)
    (hobs :
      ∀ x : State,
        ∃ cutoff : Nat,
          ∀ h : Nat, cutoff ≤ h → blockPP (T.π h) A x = A x)
    (hschur :
      ∀ x : State,
        ∃ cutoff : Nat,
          ∀ h : Nat, cutoff ≤ h →
            schurComplement (T.π h) A ((data.shadowResolvent h).inverse) x = State.zero) :
    ∀ x : State,
      ∃ cutoff : Nat,
        ∀ h : Nat, cutoff ≤ h → exact_schur_tower_general T A data h x = A x := by
  intro x
  rcases hobs x with ⟨obsCutoff, hobsStable⟩
  rcases hschur x with ⟨schurCutoff, hschurStable⟩
  refine ⟨obsCutoff + schurCutoff, ?_⟩
  intro h hh
  have hhobs : obsCutoff ≤ h := Nat.le_trans (Nat.le_add_right obsCutoff schurCutoff) hh
  have hhschur : schurCutoff ≤ h := Nat.le_trans (Nat.le_add_left schurCutoff obsCutoff) hh
  have hobs_h : blockPP (T.π h) A x = A x := hobsStable h hhobs
  have hschur_h :
      schurComplement (T.π h) A ((data.shadowResolvent h).inverse) x = State.zero :=
    hschurStable h hhschur
  dsimp [exact_schur_tower_general, effectiveOp]
  calc
    State.add (blockPP (T.π h) A x)
        (schurComplement (T.π h) A ((data.shadowResolvent h).inverse) x)
        = State.add (A x)
            (schurComplement (T.π h) A ((data.shadowResolvent h).inverse) x) := by
              rw [hobs_h]
    _ = State.add (A x) State.zero := by
          rw [hschur_h]
    _ = A x := by
          rw [State.add_zero]

/-- Selected corrections acting on the observed sector only recover the same
eventual operator whenever the exact Schur tower recovers the base operator and
the selected corrections vanish on observed inputs. -/
theorem selected_schur_recovery_general
    (T : HorizonTower) (A : AddMap) (data : ExactSchurTowerGeneralData T A)
    (C : Nat → AddMap)
    (hexact :
      ∀ x : State,
        ∃ cutoff : Nat,
          ∀ h : Nat, cutoff ≤ h → exact_schur_tower_general T A data h x = A x)
    (hselected :
      ∀ x : State,
        ∃ cutoff : Nat,
          ∀ h : Nat, cutoff ≤ h → C h ((T.π h) x) = State.zero) :
    ∀ x : State,
      ∃ cutoff : Nat,
        ∀ h : Nat, cutoff ≤ h →
          AddMap.add
            (exact_schur_tower_general T A data h)
            (AddMap.comp (C h) (AddMap.ofProjection (T.π h))) x
          = A x := by
  intro x
  rcases hexact x with ⟨exactCutoff, hexactStable⟩
  rcases hselected x with ⟨selectedCutoff, hselectedStable⟩
  refine ⟨exactCutoff + selectedCutoff, ?_⟩
  intro h hh
  have hhexact : exactCutoff ≤ h := Nat.le_trans (Nat.le_add_right exactCutoff selectedCutoff) hh
  have hhselected : selectedCutoff ≤ h := Nat.le_trans (Nat.le_add_left selectedCutoff exactCutoff) hh
  have hexact_h : exact_schur_tower_general T A data h x = A x := hexactStable h hhexact
  have hselected_h : C h ((T.π h) x) = State.zero := hselectedStable h hhselected
  calc
    AddMap.add
        (exact_schur_tower_general T A data h)
        (AddMap.comp (C h) (AddMap.ofProjection (T.π h))) x
        = State.add
            (exact_schur_tower_general T A data h x)
            (C h ((T.π h) x)) := by
              rfl
    _ = State.add (A x) (C h ((T.π h) x)) := by
          rw [hexact_h]
    _ = State.add (A x) State.zero := by
          rw [hselected_h]
    _ = A x := by
          rw [State.add_zero]

/-- Exact nonlinear `P/Q` split of a state map along a projection. -/
def nonlinear_pq_split
    (P : Projection) (F : State → State) (p q : State) : State × State :=
  (P (F (State.add p q)), projectionShadow P (F (State.add p q)))

/-- Exact nonlinear observed law induced by a chosen shadow selector. -/
def nonlinear_effective_law
    (P : Projection) (F : State → State) (Psi : State → State) (p : State) : State :=
  (nonlinear_pq_split P F p (Psi p)).1

/-- Exact shadow-elimination data: a chosen graph together with exact shadow
vanishing and uniqueness. -/
structure NonlinearShadowEliminationData (P : Projection) (F : State → State) where
  shadowSelector : State → State
  shadow_vanishes :
    ∀ p : State,
      (nonlinear_pq_split P F p (shadowSelector p)).2 = State.zero
  shadow_unique :
    ∀ p q : State,
      (nonlinear_pq_split P F p q).2 = State.zero → q = shadowSelector p

/-- Exact nonlinear shadow elimination: solving the shadow component by a
chosen graph reduces the full equation to the observed effective law, and every
full solution reconstructs uniquely from that graph. -/
theorem nonlinear_shadow_elimination
    (P : Projection) (F : State → State)
    (data : NonlinearShadowEliminationData P F) :
    (∀ p : State,
      nonlinear_effective_law P F data.shadowSelector p = State.zero →
        F (State.add p (data.shadowSelector p)) = State.zero) ∧
    (∀ p q : State,
      F (State.add p q) = State.zero →
        nonlinear_effective_law P F data.shadowSelector p = State.zero ∧
          q = data.shadowSelector p) := by
  constructor
  · intro p hp
    have hsplit := shadow_plus_proj_identity P (F (State.add p (data.shadowSelector p)))
    have hp' :
        P (F (State.add p (data.shadowSelector p))) = State.zero := by
      simpa [nonlinear_effective_law, nonlinear_pq_split] using hp
    have hshadow :
        projectionShadow P (F (State.add p (data.shadowSelector p))) = State.zero := by
      simpa [nonlinear_pq_split] using data.shadow_vanishes p
    rw [hp', hshadow, State.zero_add] at hsplit
    exact hsplit.symm
  · intro p q hfull
    have hshadow :
        (nonlinear_pq_split P F p q).2 = State.zero := by
      unfold nonlinear_pq_split
      rw [hfull, projectionShadow_zero]
    have hq : q = data.shadowSelector p := data.shadow_unique p q hshadow
    refine ⟨?_, hq⟩
    unfold nonlinear_effective_law nonlinear_pq_split
    rw [← hq, hfull, P.map_zero]

/-- Semilinear state map with explicit linear part, nonlinear correction, and
source term. -/
def semilinear_shadow_map
    (L : AddMap) (N : State → State) (f : State) : State → State :=
  fun u => State.sub (State.add (L u) (N u)) f

/-- Constructive semilinear shadow elimination is exactly the nonlinear shadow
elimination theorem specialized to the semilinear state map. -/
theorem semilinear_shadow_elimination
    (P : Projection) (L : AddMap) (N : State → State) (f : State)
    (data : NonlinearShadowEliminationData P (semilinear_shadow_map L N f)) :
    (∀ p : State,
      nonlinear_effective_law P (semilinear_shadow_map L N f) data.shadowSelector p =
        State.zero →
        semilinear_shadow_map L N f (State.add p (data.shadowSelector p)) = State.zero) ∧
    (∀ p q : State,
      semilinear_shadow_map L N f (State.add p q) = State.zero →
        nonlinear_effective_law P (semilinear_shadow_map L N f) data.shadowSelector p =
          State.zero ∧
          q = data.shadowSelector p) := by
  exact nonlinear_shadow_elimination P (semilinear_shadow_map L N f) data

/-- Linear shadow elimination is the zero-nonlinearity specialization of the
semilinear interface. -/
theorem linear_shadow_specialization
    (P : Projection) (L : AddMap) (f : State)
    (data :
      NonlinearShadowEliminationData
        P
        (semilinear_shadow_map L (fun _ => State.zero) f)) :
    (∀ p : State,
      nonlinear_effective_law
          P
          (semilinear_shadow_map L (fun _ => State.zero) f)
          data.shadowSelector
          p =
        State.zero →
        semilinear_shadow_map L (fun _ => State.zero) f
          (State.add p (data.shadowSelector p)) = State.zero) ∧
    (∀ p q : State,
      semilinear_shadow_map L (fun _ => State.zero) f (State.add p q) = State.zero →
        nonlinear_effective_law
            P
            (semilinear_shadow_map L (fun _ => State.zero) f)
            data.shadowSelector
            p =
          State.zero ∧
          q = data.shadowSelector p) := by
  exact semilinear_shadow_elimination P L (fun _ => State.zero) f data

/-- Energy-Lipschitz control for a selected shadow graph on the rebuilt state
space. -/
def ShadowLipschitzWith (L : Nat) (Psi : State → State) : Prop :=
  ∀ p₁ p₂ : State,
    State.energy (State.sub (Psi p₁) (Psi p₂)) ≤
      L * State.energy (State.sub p₁ p₂)

/-- Global shadow-elimination data: an exact nonlinear elimination graph
together with an explicit global Lipschitz bound on the shadow selector. -/
structure GlobalMonotoneShadowData (P : Projection) (F : State → State) where
  elimination : NonlinearShadowEliminationData P F
  lipschitzConst : Nat
  shadow_lipschitz :
    ShadowLipschitzWith lipschitzConst elimination.shadowSelector

/-- Once a global shadow graph and its Lipschitz control have been supplied
explicitly, the reduced observed law is exact and the shadow selector is
globally controlled on the rebuilt energy scale. -/
theorem global_monotone_shadow
    (P : Projection) (F : State → State)
    (data : GlobalMonotoneShadowData P F) :
    (∀ p : State,
      nonlinear_effective_law P F data.elimination.shadowSelector p = State.zero →
        F (State.add p (data.elimination.shadowSelector p)) = State.zero) ∧
    (∀ p q : State,
      F (State.add p q) = State.zero →
        nonlinear_effective_law P F data.elimination.shadowSelector p = State.zero ∧
          q = data.elimination.shadowSelector p) ∧
    ShadowLipschitzWith data.lipschitzConst data.elimination.shadowSelector := by
  rcases nonlinear_shadow_elimination P F data.elimination with ⟨hforward, hbackward⟩
  exact ⟨hforward, hbackward, data.shadow_lipschitz⟩

/-- Local regular-shadow data: an exact elimination graph together with an
explicit inverse for the vertical derivative and the resulting derivative
formula for the local shadow selector. -/
structure RegularSingularShadowData (P : Projection) (F : State → State) where
  elimination : NonlinearShadowEliminationData P F
  verticalDerivative : State → AddMap
  verticalInverse : State → AddMap
  horizontalDerivative : State → AddMap
  shadowDerivative : State → AddMap
  vertical_left_inverse :
    ∀ p : State, ∀ x : State,
      AddMap.comp (verticalInverse p) (verticalDerivative p) x = x
  vertical_right_inverse :
    ∀ p : State, ∀ x : State,
      AddMap.comp (verticalDerivative p) (verticalInverse p) x = x
  derivative_formula :
    ∀ p : State,
      shadowDerivative p =
        AddMap.sub AddMap.zero
          (AddMap.comp (verticalInverse p) (horizontalDerivative p))

/-- Regular shadow charts provide exact local elimination together with the
explicit inverse and derivative formula that distinguish the regular regime
from the singular one. -/
theorem regular_singular_shadow
    (P : Projection) (F : State → State)
    (data : RegularSingularShadowData P F) :
    (∀ p : State,
      nonlinear_effective_law P F data.elimination.shadowSelector p = State.zero →
        F (State.add p (data.elimination.shadowSelector p)) = State.zero) ∧
    (∀ p q : State,
      F (State.add p q) = State.zero →
        nonlinear_effective_law P F data.elimination.shadowSelector p = State.zero ∧
          q = data.elimination.shadowSelector p) ∧
    (∀ p x : State,
      AddMap.comp (data.verticalInverse p) (data.verticalDerivative p) x = x ∧
        AddMap.comp (data.verticalDerivative p) (data.verticalInverse p) x = x) ∧
    (∀ p : State,
      data.shadowDerivative p =
        AddMap.sub AddMap.zero
          (AddMap.comp (data.verticalInverse p) (data.horizontalDerivative p))) := by
  rcases nonlinear_shadow_elimination P F data.elimination with ⟨hforward, hbackward⟩
  refine ⟨hforward, hbackward, ?_, data.derivative_formula⟩
  intro p x
  exact ⟨data.vertical_left_inverse p x, data.vertical_right_inverse p x⟩

/-- Gauge-sliced shadow data packages an exact shadow graph together with a
chosen slice and uniqueness of slice representatives for shadow-zero states. -/
structure GaugeSlicedShadowData (P : Projection) (F : State → State) where
  elimination : NonlinearShadowEliminationData P F
  isSlice : State → Prop
  selector_in_slice : ∀ p : State, isSlice (elimination.shadowSelector p)
  slice_unique :
    ∀ p q : State,
      isSlice q →
        (nonlinear_pq_split P F p q).2 = State.zero →
          q = elimination.shadowSelector p

/-- On a chosen gauge slice, shadow elimination reduces the full law to the
observed effective law with a unique slice representative. -/
theorem gauge_sliced_shadow
    (P : Projection) (F : State → State)
    (data : GaugeSlicedShadowData P F) :
    (∀ p : State, data.isSlice (data.elimination.shadowSelector p)) ∧
    (∀ p q : State,
      data.isSlice q →
        (nonlinear_pq_split P F p q).2 = State.zero →
          q = data.elimination.shadowSelector p) ∧
    (∀ p : State,
      nonlinear_effective_law P F data.elimination.shadowSelector p = State.zero →
        F (State.add p (data.elimination.shadowSelector p)) = State.zero) ∧
    (∀ p q : State,
      data.isSlice q →
        F (State.add p q) = State.zero →
          nonlinear_effective_law P F data.elimination.shadowSelector p = State.zero ∧
            q = data.elimination.shadowSelector p) := by
  rcases nonlinear_shadow_elimination P F data.elimination with ⟨hforward, hbackward⟩
  refine ⟨data.selector_in_slice, data.slice_unique, hforward, ?_⟩
  intro p q hslice hfull
  have hshadow :
      (nonlinear_pq_split P F p q).2 = State.zero := by
    unfold nonlinear_pq_split
    rw [hfull, projectionShadow_zero]
  have hq : q = data.elimination.shadowSelector p := data.slice_unique p q hslice hshadow
  have hreduced := hbackward p q hfull
  exact ⟨hreduced.1, hq⟩

end CoherenceCalculus
