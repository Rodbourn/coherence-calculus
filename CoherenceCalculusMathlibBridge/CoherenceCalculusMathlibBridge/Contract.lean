import CoherenceCalculus.PartIII

namespace CoherenceCalculusMathlibBridge

open CoherenceCalculus

/--
Stable external bridge tiers for the detached mathlib compatibility package.

These labels are architectural only. They do not add new mathematics to the
certified spine; they only organize which exported Part III interfaces a
mathlib-side realization is expected to target.
-/
inductive BridgeTier where
  | limit
  | observation
  | recovery
  | completion
  | continuum
  | lateShell
  | promotion
  | fiberedRecovery
  | fiberedPromotion
  deriving DecidableEq, Repr

/-- Minimal exported limit surface for external realizations. -/
structure LimitContract (X : Type) where
  limits : LimitInterface X

/-- Lowest bridge band: a tower together with faithful observation in the Part
III sense. -/
structure ObservationContract (H : Type) where
  limits : LimitInterface H
  tower : Nat → Endo H
  faithful : FaithfulObservationLimit limits tower

/-- Recovery band: the full Part III operator-recovery package on one ambient
carrier. -/
abbrev RecoveryContract (H : Type) := FaithfulOperatorRecoveryData H

/-- Completion band: a directed family, its completion datum, and an exact
horizon-error package. -/
structure CompletionContract where
  family : DirectedHorizonFamily
  datum : HilbertCompletionDatum family
  budget : ExactHorizonErrorBudget family datum

/-- Continuum band: discrete family, reconstruction datum, and chosen
continuum law with asymptotic consistency. -/
structure ContinuumContract
    (F : DiscreteRealizedLawFamily) (X₀ X : Type) where
  datum : ContinuumReconstructionDatum F X₀ X
  law : X₀ → X
  consistent : AsymptoticConsistency F datum law

/-- Late-shell continuum band: interpolation, block derivatives, effective
flow, and the comparison surface back to tower derivatives. -/
structure LateShellContract (Parameter X : Type) where
  interpolation : ContinuousHorizonInterpolation Parameter X
  blockDerivatives : ContinuousBlockDerivativeDatum Parameter X
  effectiveFlow : ContinuousEffectiveFlowData Parameter X
  flowVsTower : ContinuousFlowVsTowerDerivative

/-- Promotion band: promoted constitutive context together with the three
detached Part III promotion interfaces. -/
structure PromotionContract (Observed Ambient Law : Type) where
  context : PromotedConstitutiveContext Observed Ambient
  characteristic : CharacteristicScalePromotionData context
  admissible : AdmissiblePromotionData Law
  minimumEnergy : MinimumEnergyPromotion

/-- Fibered recovery band used by the word-local ray side of the derived Part
III bridge. -/
abbrev FiberedRecoveryContract (Parameter H : Type) :=
  FiberedFaithfulOperatorRecoveryData Parameter H

/-- Fibered promotion band used when the promoted law carries a parameter
fiber. -/
structure FiberedPromotionContract
    (Parameter Observed Ambient Law : Type) where
  context : FiberedPromotedConstitutiveContext Observed Ambient
  characteristic : FiberedCharacteristicScalePromotionData context
  admissible : FiberedAdmissiblePromotionData Parameter Law
  minimumEnergy : FiberedMinimumEnergyPromotion

end CoherenceCalculusMathlibBridge
