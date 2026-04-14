import CoherenceCalculus.PartIV.ClosureCurrentUnifiedDifferentialFieldCore
import CoherenceCalculus.PartIV.ClosureCurrentContinuumFieldCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentUnifiedTransportFieldCore

One explicit unified transport field on the current detached flagship surface.

`ClosureCurrentUnifiedDifferentialFieldCore` already packages the strongest
current differential object carried by the endpoint-complete no-stage law:
one unified `State`-valued differential field together with its exact
differential, derivative, and variational realization surfaces.

The next honest use of Parts I--III is not to enlarge the primitive carrier.
It is to read that same field back through the active boundary/transport
grammar that the selected datum already carries:

* the selected datum contains a concrete `CharacteristicHorizonRealization`;
* the same selected state-field law carries the exact conservative transport
  triad and Hamilton--Jacobi projection bridge on `State`.

This file packages those pieces into one explicit unified transport field. It
still does not claim a final spatial differential PDE. It records that the
current flagship surface already lives on one concrete carrier with one
characteristic horizon realization and one exact transport/projection grammar.
-/

namespace ClosureCurrent

/-- One explicit unified transport field on the current detached flagship
surface. The package records the same `State`-valued unified differential
field together with the characteristic horizon realization, selected horizon,
observer-side transport datum, and Hamilton--Jacobi projection bridge already
read from the same selected datum. -/
structure UnifiedTransportField
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) where
  differentialField : UnifiedDifferentialField data
  realization : CharacteristicHorizonRealization Time
  horizon : Nat
  observerTransport : ConservativeTransportDatum State State
  projectionDatum : HamiltonJacobiProjectionDatum State State
  realization_eq :
    realization =
      data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.observer.selection.realization
  horizon_eq :
    horizon =
      data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.observer.selection.horizon
  observerTransport_eq :
    observerTransport =
      data.completionLaw.fourStateLaw.selectedFieldLaw.observerTransport
  projectionDatum_eq :
    projectionDatum =
      data.completionLaw.fourStateLaw.selectedFieldLaw.projectionDatum
  partOneSurface :
    (∀ x : State, trueBoundary (trueBoundary x) = State.zero) ∧
      (∀ x : State,
        observedBoundary realization.tower horizon
            (observedBoundary realization.tower horizon x) =
          State.negate (boundaryDefect realization.tower horizon x))
  transportSurface :
    ∀ t : Time, ∀ x : State,
      realization.U t (observedBoundary realization.tower horizon x) =
          observedBoundary realization.tower horizon (realization.U t x) ∧
        realization.U t (boundaryDefect realization.tower horizon x) =
          boundaryDefect realization.tower horizon (realization.U t x)
  observerTriad :
    EulerianPresentation observerTransport ↔
      LagrangianPresentation observerTransport ∧
        CharacteristicPresentation observerTransport
  projectionSurface :
    (CharacteristicPresentation projectionDatum.observer ↔
      ∀ q : State,
        projectionDatum.dynamics.characteristicResidual q = SignedCount.zero) ∧
      (∀ q : State,
        projectionDatum.observer.characteristicResidual q =
          projectionDatum.dynamics.characteristicResidual q)

/-- Manuscript-facing unified transport-field surface of the endpoint-complete
no-stage law. -/
def UnifiedTransportFieldSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) : Prop :=
  Nonempty (UnifiedTransportField data)

/-- The endpoint-complete no-stage law already yields one explicit unified
transport field on the concrete carrier `State`: the unified differential
field, the selected datum's characteristic horizon realization and selected
horizon, and the exact observer-side transport / Hamilton--Jacobi bridge read
from that same carrier law. -/
theorem LocalEventFourStateFlagshipLaw.unifiedTransportFieldSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    UnifiedTransportFieldSurface data := by
  obtain ⟨hdifferentialField⟩ := data.unifiedDifferentialFieldSurface
  let law := data.completionLaw.fourStateLaw
  let selection := law.framed.object.bridge.selectedBridge.observer.selection
  refine
    ⟨{ differentialField := hdifferentialField
       realization := selection.realization
       horizon := selection.horizon
       observerTransport := law.selectedFieldLaw.observerTransport
       projectionDatum := law.selectedFieldLaw.projectionDatum
       realization_eq := rfl
       horizon_eq := rfl
       observerTransport_eq := rfl
       projectionDatum_eq := rfl
       partOneSurface := by
         obtain ⟨hboundary, hhorizon⟩ := transfer_part_one selection.realization
         refine ⟨hboundary, ?_⟩
         intro x
         exact hhorizon selection.horizon x
       transportSurface := by
         intro t x
         obtain ⟨_hobsSq, hobsTransport, hdefTransport⟩ :=
           characteristic_realization selection.realization t selection.horizon x
         exact ⟨hobsTransport, hdefTransport⟩
       observerTriad := by
         simpa using law.selectedFieldLaw.observerSurface
       projectionSurface := by
         simpa using law.selectedFieldLaw.projectionSurface }⟩

end ClosureCurrent

end CoherenceCalculus
