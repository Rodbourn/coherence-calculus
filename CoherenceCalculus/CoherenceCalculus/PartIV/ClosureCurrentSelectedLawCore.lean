import CoherenceCalculus.PartIV.ClosureCurrentLawFormCore
import CoherenceCalculus.PartIV.ClosureCurrentAnchorCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentSelectedLawCore

Selected-cut law surface for the detached closure-current lane.

`ClosureCurrentLawFormCore` records the compact local generator/transport/channel
equation. `ClosureCurrentAnchorCore` records the selected-observer anchor and its
transport to the full selected cut. This file combines the two.

The result is the first selected-cut reading of the detached flagship law:

* exact visibility on the selected bridge observer;
* forced continuum closure on that anchored observer;
* transport of the same closure class to the full selected cut;
* the rolewise generator/transport/channel equation on the hidden current.
-/

namespace ClosureCurrent

/-- Detached compact law form carried by the anchored selected-cut object. -/
structure AnchoredLawForm (Index Time Carrier Law : Type) where
  object : AnchoredCurrentObject Index Time Carrier Law
  transportCompatible :
    object.toObservedCurrentObject.toLocalEventObject.channelTransportCompatible

/-- The anchored law form determines the underlying local detached law form. -/
def AnchoredLawForm.toLocalEventLawForm
    {Index Time Carrier Law : Type}
    (data : AnchoredLawForm Index Time Carrier Law) :
    LocalEventLawForm Index Time Carrier Law where
  object := data.object.toObservedCurrentObject.toLocalEventObject
  transportCompatible := data.transportCompatible

/-- The hidden local generator read through the anchored law form. -/
def AnchoredLawForm.generator
    {Index Time Carrier Law : Type}
    (data : AnchoredLawForm Index Time Carrier Law) :
    PairExchangeCurrent
        data.object.currentCarrier
        data.object.Leg →
      PairExchangeCurrent
        data.object.currentCarrier
        data.object.Leg :=
  data.toLocalEventLawForm.object.generator

/-- Rolewise channel readout on the anchored law form. -/
def AnchoredLawForm.channelRead
    {Index Time Carrier Law : Type}
    (data : AnchoredLawForm Index Time Carrier Law)
    (role : VisibleCarrierRole) :
    PairExchangeCurrent data.object.currentCarrier data.object.Leg →
      data.object.visible role :=
  data.toLocalEventLawForm.object.channelRead role

/-- Rolewise visible transport on the anchored law form. -/
def AnchoredLawForm.channelTransport
    {Index Time Carrier Law : Type}
    (data : AnchoredLawForm Index Time Carrier Law)
    (role : VisibleCarrierRole) :
    data.object.visible role → data.object.visible role :=
  data.toLocalEventLawForm.object.channelTransport role

/-- Returned-defect current on the anchored law form. -/
def AnchoredLawForm.returnedDefect
    {Index Time Carrier Law : Type}
    (data : AnchoredLawForm Index Time Carrier Law) :
    PairExchangeCurrent
        data.object.currentCarrier
        data.object.Leg →
      PairExchangeCurrent
        data.object.currentCarrier
        data.object.Leg :=
  data.toLocalEventLawForm.object.returnedDefect

/-- Rolewise visible residual on the anchored law form. -/
def AnchoredLawForm.channelResidual
    {Index Time Carrier Law : Type}
    (data : AnchoredLawForm Index Time Carrier Law)
    (role : VisibleCarrierRole) :
    PairExchangeCurrent data.object.currentCarrier data.object.Leg →
      data.object.visible role :=
  data.toLocalEventLawForm.object.channelResidual role

/-- Surface theorem for the selected-cut detached law form. The compact
generator/transport/channel equation is now tied to exact anchored visibility
and full selected-cut closure transport. -/
theorem AnchoredLawForm.surface
    {Index Time Carrier Law : Type}
    (data : AnchoredLawForm Index Time Carrier Law) :
    Nonempty (PairExchangeCurrent data.object.currentCarrier data.object.Leg) ∧
      data.object.toCurrentAnchor.currentDirectReturnCompatible ∧
      data.object.toCurrentAnchor.visiblePrimitiveReadoutAutonomous ∧
      data.object.toCurrentAnchor.minimalVisibleQuotients ∧
      exactVisibleOnCut
        (data.object.bridge.selectedBridge.observer.selection.realization.tower.π
          data.object.bridge.selectedBridge.observer.selection.horizon)
        (selected_observed_law
          data.object.bridge.selectedBridge.observer.selection).op ∧
      ForcedContinuumLaw
        data.object.bridge.selectedBridge.observer.continuumClass
        data.object.physicalPrinciple.selectedLaw.selectedClosureLaw ∧
      (∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
        observer.selection = data.object.bridge.selectedBridge.observer.selection →
          data.object.physicalPrinciple.selectedLaw.endpointClosureClass =
            observer.continuumClass) ∧
      (∀ role : VisibleCarrierRole,
        ∀ current :
          PairExchangeCurrent data.object.currentCarrier data.object.Leg,
          data.channelRead role (data.generator current) =
            data.channelTransport role (data.channelRead role current)) ∧
      (∀ role : VisibleCarrierRole,
        ∀ current :
          PairExchangeCurrent data.object.currentCarrier data.object.Leg,
          data.channelResidual role current =
            data.channelRead role (data.returnedDefect current)) := by
  obtain ⟨hcurrent, hdirret, haut, hmin, hexact, hforced, htransport⟩ :=
    data.object.transportSurface
  obtain ⟨_hcurrent', _hdirret', _haut', _hmin', hlaw, hresidual⟩ :=
    data.toLocalEventLawForm.surface
  exact
    ⟨hcurrent,
      hdirret,
      haut,
      hmin,
      hexact,
      hforced,
      htransport,
      hlaw,
      hresidual⟩

end ClosureCurrent

end CoherenceCalculus
