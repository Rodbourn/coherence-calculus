import CoherenceCalculus.PartIV.ClosureCurrentPhysicalFieldCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumGoalCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentPhysicalEquationCore

One exact physical equation field on the current detached flagship surface.

`ClosureCurrentPhysicalFieldCore` already closes the carrier-side unification:
the endpoint-complete no-stage law yields one classwise selected-horizon
boundary field on `State`, and the recognizable flagship equations are faces of
that same field.

`ClosureCurrentContinuumLedgerCore` and `ClosureCurrentContinuumGoalCore`
already close the exact realization side on the same selected cut: the forced
selected operator admits one no-hidden-crime realization chain, and its
quadratic density is the exact goal-error ledger of the canonical adjoint-goal
certificate.

This file fuses those two already-proved surfaces. It does not add a new law,
carrier, or analytic hypothesis. It records that the current detached flagship
surface already carries one exact physical equation field on `State`: one same
classwise boundary field, one same state-field law, one same exact realized
residual, one same exact density, and the recognizable flagship faces.
-/

namespace ClosureCurrent

/-- One exact physical equation field on the current detached flagship
surface.

The package records the already-fixed classwise selected-horizon boundary
field, the exact realization ledger and adjoint-goal ledger on the same
selected law, and the recognizable phase/wave/gauge/geometric identities on
that same datum. The two final equations identify the exact realized residual
with the law generator and the exact goal error with the law density. -/
structure PhysicalEquationField
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) where
  boundaryClass : UnifiedBoundaryClass data
  ledgerSurface : SelectedLedgerSurface data.completionLaw.fourStateLaw
  goalSurface : SelectedGoalSurface data.completionLaw.fourStateLaw
  phaseIdentity :
    PhaseLane.RecognizableIdentity
      Time Carrier Law
      data.endpointWitnesses.phase.Field
      data.endpointWitnesses.phase.Scalar
  waveIdentity :
    WaveLane.RecognizableIdentity
      Time Carrier Law
      data.endpointWitnesses.wave.Field
      data.endpointWitnesses.wave.Scalar
  gaugeIdentity :
    GaugeLane.RecognizableIdentity
      Time Carrier Law
      data.endpointWitnesses.gauge.Field
      data.endpointWitnesses.gauge.Source
  geometricIdentity :
    GeometricLane.RecognizableIdentity
      Time Carrier Law
      data.endpointWitnesses.geometric.Tensor
      data.endpointWitnesses.geometric.Scalar
  law_eq :
    boundaryClass.boundaryField.transportField.differentialField.unifiedField.law =
      data.completionLaw.fourStateLaw.selectedStateFieldLaw
  realizedResidual_eq :
    ∀ x : State,
      residualReal data.completionLaw.fourStateLaw.selectedRealizationChain () x =
        boundaryClass.boundaryField.transportField.differentialField.unifiedField.law.generator x
  goalError_eq :
    ∀ x : State,
      goalError (data.completionLaw.fourStateLaw.selectedGoalCertificate x) =
        boundaryClass.boundaryField.transportField.differentialField.unifiedField.law.density x

/-- Manuscript-facing exact physical-equation surface of the endpoint-complete
no-stage law. -/
def PhysicalEquationSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) : Prop :=
  Nonempty (PhysicalEquationField data)

/-- The endpoint-complete no-stage law already yields one exact physical
equation field on the concrete carrier `State`: the classwise selected-horizon
boundary field, the exact no-hidden-crime realization chain, the exact
adjoint-goal ledger, and the recognizable flagship identities all live on one
same selected state-field law. -/
theorem LocalEventFourStateFlagshipLaw.physicalEquationSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    PhysicalEquationSurface data := by
  obtain ⟨hboundaryClass⟩ := data.unifiedBoundaryClassSurface
  have hledger : SelectedLedgerSurface data.completionLaw.fourStateLaw :=
    data.completionLaw.fourStateLaw.selectedLedgerSurface
  have hgoal : SelectedGoalSurface data.completionLaw.fourStateLaw :=
    data.completionLaw.fourStateLaw.selectedGoalSurface
  obtain ⟨_hcompletion, hphase, hwave, hgauge, hgeometric⟩ := data.surface
  obtain ⟨phaseIdentity⟩ := hphase
  obtain ⟨waveIdentity⟩ := hwave
  obtain ⟨gaugeIdentity⟩ := hgauge
  obtain ⟨geometricIdentity⟩ := hgeometric
  have hledgerSurface :
      SelectedLedgerSurface data.completionLaw.fourStateLaw := hledger
  have hgoalSurface :
      SelectedGoalSurface data.completionLaw.fourStateLaw := hgoal
  have hlawSurface :
      SelectedStateFieldLawSurface data.completionLaw.fourStateLaw :=
    hboundaryClass.boundaryField.transportField.differentialField.unifiedField.lawSurface
  obtain
    ⟨_hlaw, _hproject, _hflow, _hgenObj, _hgenAut, hgenField, _hdensObj,
      _hdensAut, _hresObj, _hresAut, _hsolObj, _hsolEq, _hpde, _haction,
      _hevolution, _hrealization⟩ := hlawSurface
  obtain
    ⟨_hexact, _hrealEq, _hcontEq, hresidualEq, _hpairEq, _hscalarEq⟩ := hledger
  obtain
    ⟨_hexactState, _halg, _hgoalPair, hgoalDensity, _hgoalSum, _hgoalScalar⟩ :=
    hgoal
  have hgenField' :
      ∀ x : State,
        hboundaryClass.boundaryField.transportField.differentialField.unifiedField.law.generator x =
          data.completionLaw.fourStateLaw.selectedFieldLaw.operator x := by
    intro x
    simpa [hboundaryClass.boundaryField.transportField.differentialField.unifiedField.law_eq]
      using hgenField x
  refine
    ⟨{ boundaryClass := hboundaryClass
       ledgerSurface := hledgerSurface
       goalSurface := hgoalSurface
       phaseIdentity := phaseIdentity
       waveIdentity := waveIdentity
       gaugeIdentity := gaugeIdentity
       geometricIdentity := geometricIdentity
       law_eq :=
         hboundaryClass.boundaryField.transportField.differentialField.unifiedField.law_eq
       realizedResidual_eq := ?_
       goalError_eq := ?_ }⟩
  · intro x
    calc
      residualReal data.completionLaw.fourStateLaw.selectedRealizationChain () x =
          data.completionLaw.fourStateLaw.selectedFieldLaw.operator x := by
            exact hresidualEq x
      _ =
          hboundaryClass.boundaryField.transportField.differentialField.unifiedField.law.generator x := by
            symm
            exact hgenField' x
  · intro x
    calc
      goalError (data.completionLaw.fourStateLaw.selectedGoalCertificate x) =
          data.completionLaw.fourStateLaw.selectedQuadraticDensity x := by
            exact hgoalDensity x
      _ =
          State.pair x (data.completionLaw.fourStateLaw.selectedFieldLaw.operator x) := by
            rfl
      _ =
          State.pair
            x
            (hboundaryClass.boundaryField.transportField.differentialField.unifiedField.law.generator x) := by
              rw [hgenField' x]
      _ =
          hboundaryClass.boundaryField.transportField.differentialField.unifiedField.law.density x := by
            symm
            exact
              hboundaryClass.boundaryField.transportField.differentialField.unifiedField.law.density_eq x

end ClosureCurrent

end CoherenceCalculus
