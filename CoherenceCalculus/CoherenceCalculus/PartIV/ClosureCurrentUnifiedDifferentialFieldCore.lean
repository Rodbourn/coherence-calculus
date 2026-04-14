import CoherenceCalculus.PartIV.ClosureCurrentUnifiedFieldCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentUnifiedDifferentialFieldCore

One explicit unified differential field package on the current flagship surface.

`ClosureCurrentUnifiedFieldCore` already packages the current unified field
claim: one canonical selected state-field law together with its four
recognizable flagship faces on one same selected datum.

The next honest closure is differential rather than merely law-shaped. The
detached selected cut already carries one exact continuous block-derivative
package and one exact effective-flow package on that same `State` carrier, and
the current stronger realization languages already present that same data.

This file packages those pieces into one explicit unified differential field.
It still does not claim a final spatial differential PDE. It records the
strongest current differential object actually present on the active surface.
-/

namespace ClosureCurrent

/-- One explicit unified differential field package on the current flagship
surface. -/
structure UnifiedDifferentialField
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) where
  unifiedField : UnifiedField data
  blockDatum : ContinuousBlockDerivativeDatum Nat State
  flowDatum : ContinuousEffectiveFlowData Nat State
  differentialSurface :
    SelectedDifferentialFlagshipRealizationSurface data.completionLaw.fourStateLaw
  derivativeSurface :
    SelectedDerivativeSubsamplingFlagshipSurface data.completionLaw.fourStateLaw
  variationalSurface :
    SelectedVariationalFlagshipRealizationSurface data.completionLaw.fourStateLaw
  blockDatum_eq :
    blockDatum = data.completionLaw.fourStateLaw.selectedContinuousBlockDerivativeDatum
  flowDatum_eq :
    flowDatum = data.completionLaw.fourStateLaw.selectedContinuousEffectiveFlowData
  flow_uses_blockDatum : flowDatum.blockData = blockDatum

/-- Manuscript-facing unified differential field surface of the
endpoint-complete no-stage law. -/
def UnifiedDifferentialFieldSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) : Prop :=
  Nonempty (UnifiedDifferentialField data)

/-- The endpoint-complete no-stage law already yields one explicit unified
differential field package: the unified field law on `State`, the exact
continuous block-derivative/effective-flow package on that same carrier, the
current derivative and variational realization surfaces, and the four
recognizable flagship identities on the same selected datum. -/
theorem LocalEventFourStateFlagshipLaw.unifiedDifferentialFieldSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    UnifiedDifferentialFieldSurface data := by
  have hdiff :
      SelectedDifferentialFlagshipRealizationSurface data.completionLaw.fourStateLaw :=
    data.completionLaw.fourStateLaw.selectedDifferentialFlagshipRealizationSurface
  have hderiv :
      SelectedDerivativeSubsamplingFlagshipSurface data.completionLaw.fourStateLaw :=
    data.completionLaw.fourStateLaw.selectedDerivativeSubsamplingFlagshipSurface
  have hvar :
      SelectedVariationalFlagshipRealizationSurface data.completionLaw.fourStateLaw :=
    data.completionLaw.fourStateLaw.selectedVariationalFlagshipRealizationSurface
  obtain ⟨hunifiedField⟩ := data.unifiedFieldSurface
  refine
    ⟨{ unifiedField := hunifiedField
       blockDatum := data.completionLaw.fourStateLaw.selectedContinuousBlockDerivativeDatum
       flowDatum := data.completionLaw.fourStateLaw.selectedContinuousEffectiveFlowData
       differentialSurface := hdiff
       derivativeSurface := hderiv
       variationalSurface := hvar
       blockDatum_eq := rfl
       flowDatum_eq := rfl
       flow_uses_blockDatum := rfl }⟩

/-- On the current detached flagship surface, no later stronger realization is
free to introduce a new primitive carrier law. Every admitted combined
realization already collapses pointwise to the same selected generator,
quadratic density, scalar residual, and zero set on the concrete carrier
`State`. -/
def NoNewPrimitiveCarrier
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) : Prop :=
  ∀ realization : CompositeFlagshipRealization data.completionLaw.fourStateLaw,
    ∀ x : State,
      realization.flagship.velocity x =
          data.completionLaw.fourStateLaw.selectedAutonomousScalarLaw.generator x ∧
        realization.flagship.density x =
          data.completionLaw.fourStateLaw.selectedQuadraticDensity x ∧
        realization.flagship.residual x =
          data.completionLaw.fourStateLaw.selectedAutonomousScalarLaw.residual x ∧
        (realization.flagship.solution x ↔
          data.completionLaw.fourStateLaw.selectedFieldEquation x)

/-- The endpoint-complete no-stage law leaves no new primitive carrier on the
current detached flagship surface. Any admitted stronger realization is
already a presentation of the same `State`-carried law. -/
theorem LocalEventFourStateFlagshipLaw.noNewPrimitiveCarrier
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    NoNewPrimitiveCarrier data := by
  obtain ⟨_hrealization, hop, hdensity, hresidual, hsolution⟩ :=
    data.completionLaw.fourStateLaw.selectedCompositeFlagshipRealizationSurface
  intro realization x
  rcases hop realization x with ⟨_, _, _, _, hvelocity⟩
  rcases hdensity realization x with ⟨hdensity, _, _⟩
  rcases hresidual realization x with ⟨hresidual, _, _, _, _, _, _, _⟩
  rcases hsolution realization x with ⟨hsolution, _, _, _, _⟩
  exact ⟨hvelocity, hdensity, hresidual, hsolution⟩

/-- Manuscript-facing carrier-rigidity surface of the endpoint-complete
no-stage law. The current unified differential field already lives on the
canonical carrier `State`, and all admitted stronger realization languages
collapse pointwise to that same carrier law. -/
def StateCarrierRigiditySurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) : Prop :=
  UnifiedDifferentialFieldSurface data ∧ NoNewPrimitiveCarrier data

/-- The endpoint-complete no-stage law already fixes the current flagship
surface on one concrete carrier. The remaining PDE/action step is therefore a
presentation problem for that same carrier law, not the choice of a new
primitive carrier. -/
theorem LocalEventFourStateFlagshipLaw.stateCarrierRigiditySurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    StateCarrierRigiditySurface data := by
  exact ⟨data.unifiedDifferentialFieldSurface, data.noNewPrimitiveCarrier⟩

end ClosureCurrent

end CoherenceCalculus
