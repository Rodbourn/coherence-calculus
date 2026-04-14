import CoherenceCalculus.PartIII.ClassicalLimitCore
import CoherenceCalculusMathlibBridge.Contract
import CoherenceCalculusMathlibBridge.FilterLimit
import Mathlib.LinearAlgebra.Projection

namespace CoherenceCalculusMathlibBridge

open CoherenceCalculus

abbrev LinearEndo (R M : Type _)
    [Semiring R] [AddCommMonoid M] [Module R M] : Type _ :=
  M →ₗ[R] M

/--
Lowest detached bridge band: linear projection towers over a mathlib module.

This sits below the Hilbert-facing layer and is intended to be the first broad
compatibility target for Parts I and II.
-/
structure AbstractLinearProjectionTower (R M : Type _)
    [Semiring R] [AddCommMonoid M] [Module R M] where
  projection : Nat → LinearEndo R M
  faithful : ∀ x : M, EventuallyEqAtTop (fun n => projection n x) x
  nested : Prop
  complemented : Prop

def AbstractLinearProjectionTower.toTower
    {R M : Type _}
    [Semiring R] [AddCommMonoid M] [Module R M]
    (tower : AbstractLinearProjectionTower R M) :
    Nat → Endo M :=
  fun n x => tower.projection n x

theorem AbstractLinearProjectionTower.faithfulObservationLimit
    {R M : Type _}
    [Semiring R] [AddCommMonoid M] [Module R M]
    (tower : AbstractLinearProjectionTower R M) :
    FaithfulObservationLimit (filterLimitInterface M) tower.toTower := by
  intro x
  exact tower.faithful x

def AbstractLinearProjectionTower.toObservationContract
    {R M : Type _}
    [Semiring R] [AddCommMonoid M] [Module R M]
    (tower : AbstractLinearProjectionTower R M) :
    ObservationContract M where
  limits := filterLimitInterface M
  tower := tower.toTower
  faithful := tower.faithfulObservationLimit

structure AbstractLinearRecovery (R M : Type _)
    [Semiring R] [AddCommMonoid M] [Module R M] where
  tower : AbstractLinearProjectionTower R M
  domain : M → Prop
  operator : LinearEndo R M
  observed : Nat → LinearEndo R M
  defect : Nat → LinearEndo R M
  domain_stable :
    ∀ n : Nat, ∀ x : M, domain x → domain (tower.projection n x)
  defect_vanishes :
    ∀ x : M, domain x → EventuallyEqAtTop (fun n => defect n x) 0
  observed_recovers :
    ∀ x : M, domain x → EventuallyEqAtTop (fun n => observed n x) (operator x)

def AbstractLinearRecovery.toFaithfulOperatorRecoveryData
    {R M : Type _}
    [Semiring R] [AddCommMonoid M] [Module R M]
    (data : AbstractLinearRecovery R M) :
    FaithfulOperatorRecoveryData M where
  limits := filterLimitInterface M
  tower := data.tower.toTower
  domain := data.domain
  zero := 0
  operator := fun x => data.operator x
  observed := fun n x => data.observed n x
  defect := fun n x => data.defect n x
  faithful := data.tower.faithfulObservationLimit
  domain_stable := data.domain_stable
  defect_vanishes := data.defect_vanishes
  observed_recovers := data.observed_recovers

def AbstractLinearRecovery.toRecoveryContract
    {R M : Type _}
    [Semiring R] [AddCommMonoid M] [Module R M]
    (data : AbstractLinearRecovery R M) :
    RecoveryContract M :=
  data.toFaithfulOperatorRecoveryData

/--
First detached theorem battery: once a calculus tower is realized as mathlib
linear maps, standard linear identities are immediately available on the
exported calculus operators.
-/
theorem AbstractLinearProjectionTower.projection_map_add
    {R M : Type _}
    [Semiring R] [AddCommMonoid M] [Module R M]
    (tower : AbstractLinearProjectionTower R M)
    (n : Nat) (x y : M) :
    tower.projection n (x + y) = tower.projection n x + tower.projection n y := by
  exact (tower.projection n).map_add x y

theorem AbstractLinearProjectionTower.projection_map_smul
    {R M : Type _}
    [Semiring R] [AddCommMonoid M] [Module R M]
    (tower : AbstractLinearProjectionTower R M)
    (n : Nat) (a : R) (x : M) :
    tower.projection n (a • x) = a • tower.projection n x := by
  exact (tower.projection n).map_smulₛₗ a x

theorem AbstractLinearProjectionTower.toTower_map_add
    {R M : Type _}
    [Semiring R] [AddCommMonoid M] [Module R M]
    (tower : AbstractLinearProjectionTower R M)
    (n : Nat) (x y : M) :
    tower.toTower n (x + y) = tower.toTower n x + tower.toTower n y := by
  show tower.projection n (x + y) = tower.projection n x + tower.projection n y
  exact tower.projection_map_add n x y

theorem AbstractLinearProjectionTower.toTower_map_smul
    {R M : Type _}
    [Semiring R] [AddCommMonoid M] [Module R M]
    (tower : AbstractLinearProjectionTower R M)
    (n : Nat) (a : R) (x : M) :
    tower.toTower n (a • x) = a • tower.toTower n x := by
  show tower.projection n (a • x) = a • tower.projection n x
  exact tower.projection_map_smul n a x

theorem AbstractLinearRecovery.operator_map_add
    {R M : Type _}
    [Semiring R] [AddCommMonoid M] [Module R M]
    (data : AbstractLinearRecovery R M)
    (x y : M) :
    data.operator (x + y) = data.operator x + data.operator y := by
  exact data.operator.map_add x y

theorem AbstractLinearRecovery.observed_map_add
    {R M : Type _}
    [Semiring R] [AddCommMonoid M] [Module R M]
    (data : AbstractLinearRecovery R M)
    (n : Nat) (x y : M) :
    data.observed n (x + y) = data.observed n x + data.observed n y := by
  exact (data.observed n).map_add x y

theorem AbstractLinearRecovery.defect_map_add
    {R M : Type _}
    [Semiring R] [AddCommMonoid M] [Module R M]
    (data : AbstractLinearRecovery R M)
    (n : Nat) (x y : M) :
    data.defect n (x + y) = data.defect n x + data.defect n y := by
  exact (data.defect n).map_add x y

end CoherenceCalculusMathlibBridge
