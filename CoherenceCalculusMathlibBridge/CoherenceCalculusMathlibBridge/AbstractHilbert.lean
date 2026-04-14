import CoherenceCalculus.PartIII.ClassicalLimitCore
import CoherenceCalculus.PartIII.ContinuumIdentificationCore
import CoherenceCalculusMathlibBridge.Contract
import CoherenceCalculusMathlibBridge.FilterLimit
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

open Filter

namespace CoherenceCalculusMathlibBridge

open CoherenceCalculus

abbrev BoundedEndo (𝕜 E : Type _)
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Type _ :=
  E →L[𝕜] E

/--
An abstract mathlib Hilbert-space tower that can be interpreted as a Part III
faithful observation family.

The structure is intentionally light: the certified calculus has already proved
the abstract bridge theorems, so this detached layer only needs enough data to
instantiate them inside standard mathlib operator types.
-/
structure AbstractHilbertProjectionTower (𝕜 E : Type _)
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] where
  projection : Nat → BoundedEndo 𝕜 E
  faithful : ∀ x : E, EventuallyEqAtTop (fun n => projection n x) x
  nested : Prop
  orthogonal : Prop

def AbstractHilbertProjectionTower.toTower
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (tower : AbstractHilbertProjectionTower 𝕜 E) :
    Nat → CoherenceCalculus.Endo E :=
  fun n x => tower.projection n x

theorem AbstractHilbertProjectionTower.faithfulObservationLimit
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (tower : AbstractHilbertProjectionTower 𝕜 E) :
    CoherenceCalculus.FaithfulObservationLimit
      (filterLimitInterface E) tower.toTower := by
  intro x
  exact tower.faithful x

def AbstractHilbertProjectionTower.toObservationContract
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (tower : AbstractHilbertProjectionTower 𝕜 E) :
    ObservationContract E where
  limits := filterLimitInterface E
  tower := tower.toTower
  faithful := tower.faithfulObservationLimit

/--
Hilbert-tier theorem battery: the realized calculus tower inherits the standard
continuous-linear identities and continuity facts of the underlying mathlib
operators.
-/
theorem AbstractHilbertProjectionTower.projection_map_zero
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (tower : AbstractHilbertProjectionTower 𝕜 E)
    (n : Nat) :
    tower.projection n 0 = 0 := by
  exact (tower.projection n).map_zero

theorem AbstractHilbertProjectionTower.projection_map_add
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (tower : AbstractHilbertProjectionTower 𝕜 E)
    (n : Nat) (x y : E) :
    tower.projection n (x + y) = tower.projection n x + tower.projection n y := by
  exact (tower.projection n).map_add x y

theorem AbstractHilbertProjectionTower.projection_map_smul
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (tower : AbstractHilbertProjectionTower 𝕜 E)
    (n : Nat) (a : 𝕜) (x : E) :
    tower.projection n (a • x) = a • tower.projection n x := by
  exact (tower.projection n).map_smulₛₗ a x

theorem AbstractHilbertProjectionTower.projection_continuous
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (tower : AbstractHilbertProjectionTower 𝕜 E)
    (n : Nat) :
    Continuous (tower.projection n) := by
  exact (tower.projection n).continuous

theorem AbstractHilbertProjectionTower.toTower_map_add
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (tower : AbstractHilbertProjectionTower 𝕜 E)
    (n : Nat) (x y : E) :
    tower.toTower n (x + y) = tower.toTower n x + tower.toTower n y := by
  show tower.projection n (x + y) = tower.projection n x + tower.projection n y
  exact tower.projection_map_add n x y

theorem AbstractHilbertProjectionTower.toTower_map_smul
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (tower : AbstractHilbertProjectionTower 𝕜 E)
    (n : Nat) (a : 𝕜) (x : E) :
    tower.toTower n (a • x) = a • tower.toTower n x := by
  show tower.projection n (a • x) = a • tower.projection n x
  exact tower.projection_map_smul n a x

structure AbstractHilbertRecovery (𝕜 E : Type _)
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] where
  tower : AbstractHilbertProjectionTower 𝕜 E
  domain : E → Prop
  operator : BoundedEndo 𝕜 E
  observed : Nat → BoundedEndo 𝕜 E
  defect : Nat → BoundedEndo 𝕜 E
  domain_stable :
    ∀ n : Nat, ∀ x : E, domain x → domain (tower.projection n x)
  defect_vanishes :
    ∀ x : E, domain x → EventuallyEqAtTop (fun n => defect n x) 0
  observed_recovers :
    ∀ x : E, domain x → EventuallyEqAtTop (fun n => observed n x) (operator x)

def AbstractHilbertRecovery.toFaithfulOperatorRecoveryData
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (data : AbstractHilbertRecovery 𝕜 E) :
    CoherenceCalculus.FaithfulOperatorRecoveryData E where
  limits := filterLimitInterface E
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

def AbstractHilbertRecovery.toRecoveryContract
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (data : AbstractHilbertRecovery 𝕜 E) :
    RecoveryContract E :=
  data.toFaithfulOperatorRecoveryData

theorem AbstractHilbertRecovery.operator_map_zero
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (data : AbstractHilbertRecovery 𝕜 E) :
    data.operator 0 = 0 := by
  exact data.operator.map_zero

theorem AbstractHilbertRecovery.operator_map_add
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (data : AbstractHilbertRecovery 𝕜 E)
    (x y : E) :
    data.operator (x + y) = data.operator x + data.operator y := by
  exact data.operator.map_add x y

theorem AbstractHilbertRecovery.operator_map_smul
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (data : AbstractHilbertRecovery 𝕜 E)
    (a : 𝕜) (x : E) :
    data.operator (a • x) = a • data.operator x := by
  exact data.operator.map_smulₛₗ a x

theorem AbstractHilbertRecovery.operator_continuous
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (data : AbstractHilbertRecovery 𝕜 E) :
    Continuous data.operator := by
  exact data.operator.continuous

theorem AbstractHilbertRecovery.observed_map_add
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (data : AbstractHilbertRecovery 𝕜 E)
    (n : Nat) (x y : E) :
    data.observed n (x + y) = data.observed n x + data.observed n y := by
  exact (data.observed n).map_add x y

theorem AbstractHilbertRecovery.observed_map_smul
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (data : AbstractHilbertRecovery 𝕜 E)
    (n : Nat) (a : 𝕜) (x : E) :
    data.observed n (a • x) = a • data.observed n x := by
  exact (data.observed n).map_smulₛₗ a x

theorem AbstractHilbertRecovery.observed_continuous
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (data : AbstractHilbertRecovery 𝕜 E)
    (n : Nat) :
    Continuous (data.observed n) := by
  exact (data.observed n).continuous

theorem AbstractHilbertRecovery.defect_map_add
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (data : AbstractHilbertRecovery 𝕜 E)
    (n : Nat) (x y : E) :
    data.defect n (x + y) = data.defect n x + data.defect n y := by
  exact (data.defect n).map_add x y

theorem AbstractHilbertRecovery.defect_map_smul
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (data : AbstractHilbertRecovery 𝕜 E)
    (n : Nat) (a : 𝕜) (x : E) :
    data.defect n (a • x) = a • data.defect n x := by
  exact (data.defect n).map_smulₛₗ a x

theorem AbstractHilbertRecovery.defect_continuous
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (data : AbstractHilbertRecovery 𝕜 E)
    (n : Nat) :
    Continuous (data.defect n) := by
  exact (data.defect n).continuous

structure AbstractHilbertCompletion (𝕜 E : Type _)
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] where
  family : CoherenceCalculus.DirectedHorizonFamily
  datum : CoherenceCalculus.HilbertCompletionDatum family
  budget : CoherenceCalculus.ExactHorizonErrorBudget family datum

def AbstractHilbertCompletion.toCompletionContract
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (data : AbstractHilbertCompletion 𝕜 E) :
    CompletionContract where
  family := data.family
  datum := data.datum
  budget := data.budget

structure AbstractContinuumReconstructionModel
    (𝕜 E X₀ : Type _)
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] where
  family : CoherenceCalculus.DiscreteRealizedLawFamily
  embed : X₀ → E
  sample : (n : Nat) → X₀ → family.Observed n
  reconstruct : (n : Nat) → family.Observed n → E
  reconstruct_sample :
    ∀ u : X₀,
      EventuallyEqAtTop (fun n => reconstruct n (sample n u)) (embed u)

def AbstractContinuumReconstructionModel.toDatum
    {𝕜 E X₀ : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (model : AbstractContinuumReconstructionModel 𝕜 E X₀) :
    CoherenceCalculus.ContinuumReconstructionDatum model.family X₀ E where
  limits := filterLimitInterface E
  embed := model.embed
  sample := model.sample
  reconstruct := model.reconstruct
  reconstruct_sample := model.reconstruct_sample

def AbstractContinuumReconstructionModel.toContinuumContract
    {𝕜 E X₀ : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (model : AbstractContinuumReconstructionModel 𝕜 E X₀)
    (law : X₀ → E)
    (consistent : CoherenceCalculus.AsymptoticConsistency model.family model.toDatum law) :
    ContinuumContract model.family X₀ E where
  datum := model.toDatum
  law := law
  consistent := consistent

structure AbstractLateShellModel (Parameter X : Type _) where
  interpolation : CoherenceCalculus.ContinuousHorizonInterpolation Parameter X
  blockDerivatives : CoherenceCalculus.ContinuousBlockDerivativeDatum Parameter X
  effectiveFlow : CoherenceCalculus.ContinuousEffectiveFlowData Parameter X
  flowVsTower : CoherenceCalculus.ContinuousFlowVsTowerDerivative

def AbstractLateShellModel.toLateShellContract
    {Parameter X : Type _}
    (model : AbstractLateShellModel Parameter X) :
    LateShellContract Parameter X where
  interpolation := model.interpolation
  blockDerivatives := model.blockDerivatives
  effectiveFlow := model.effectiveFlow
  flowVsTower := model.flowVsTower

structure AbstractPromotionModel (Observed Ambient Law : Type _) where
  context : CoherenceCalculus.PromotedConstitutiveContext Observed Ambient
  characteristic :
    CoherenceCalculus.CharacteristicScalePromotionData context
  admissible : CoherenceCalculus.AdmissiblePromotionData Law
  minimumEnergy : CoherenceCalculus.MinimumEnergyPromotion

def AbstractPromotionModel.toPromotionContract
    {Observed Ambient Law : Type _}
    (model : AbstractPromotionModel Observed Ambient Law) :
    PromotionContract Observed Ambient Law where
  context := model.context
  characteristic := model.characteristic
  admissible := model.admissible
  minimumEnergy := model.minimumEnergy

structure AbstractFiberedRecoveryModel (Parameter H : Type _) where
  data : CoherenceCalculus.FiberedFaithfulOperatorRecoveryData Parameter H

def AbstractFiberedRecoveryModel.toFiberedRecoveryContract
    {Parameter H : Type _}
    (model : AbstractFiberedRecoveryModel Parameter H) :
    FiberedRecoveryContract Parameter H :=
  model.data

structure AbstractFiberedPromotionModel
    (Parameter Observed Ambient Law : Type _) where
  context :
    CoherenceCalculus.FiberedPromotedConstitutiveContext Observed Ambient
  characteristic :
    CoherenceCalculus.FiberedCharacteristicScalePromotionData context
  admissible : CoherenceCalculus.FiberedAdmissiblePromotionData Parameter Law
  minimumEnergy : CoherenceCalculus.FiberedMinimumEnergyPromotion

def AbstractFiberedPromotionModel.toFiberedPromotionContract
    {Parameter Observed Ambient Law : Type _}
    (model : AbstractFiberedPromotionModel Parameter Observed Ambient Law) :
    FiberedPromotionContract Parameter Observed Ambient Law where
  context := model.context
  characteristic := model.characteristic
  admissible := model.admissible
  minimumEnergy := model.minimumEnergy

end CoherenceCalculusMathlibBridge
