import CoherenceCalculus.PartIV.ClosureCurrentSelectedLawCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentChannelLawCore

Channel-compatible current objects for the detached closure-current lane.

`ClosureCurrentLawFormCore` exposed the compact generator/transport/channel
equation, but still as a separate wrapper around the detached current object.
This file internalizes that exact compatibility condition one layer earlier.

The result is a sharper forcing seam:

* a detached local or anchored current object;
* rolewise exactifier/quotient transport compatibility on that object itself.

From that, the flagship law form is no longer extra wrapper data. It is forced
directly from the channel-compatible current object.
-/

namespace ClosureCurrent

/-- Rolewise channel compatibility for a detached local-event object. -/
def LocalEventObject.roleTransportCompatible
    {Index Time Carrier Law : Type}
    (data : LocalEventObject Index Time Carrier Law)
    (role : VisibleCarrierRole) : Prop :=
  ∀ current : PairExchangeCurrent data.currentCarrier data.Leg,
    data.channelRead role (data.generator current) =
      data.channelTransport role (data.channelRead role current)

/-- Channel-compatible detached local-event object. The compact law equation is
carried directly by the current object role by role. -/
structure ChannelLocalEventObject (Index Time Carrier Law : Type) where
  object : LocalEventObject Index Time Carrier Law
  transportCompatible :
    ∀ role : VisibleCarrierRole,
      object.roleTransportCompatible role

/-- The channel-compatible detached local-event object determines the detached
local law form. -/
def ChannelLocalEventObject.toLocalEventLawForm
    {Index Time Carrier Law : Type}
    (data : ChannelLocalEventObject Index Time Carrier Law) :
    LocalEventLawForm Index Time Carrier Law where
  object := data.object
  transportCompatible := by
    intro role current
    exact data.transportCompatible role current

/-- Surface theorem for the channel-compatible detached local-event object. The
flagship equation is now forced directly from the current object package. -/
theorem ChannelLocalEventObject.surface
    {Index Time Carrier Law : Type}
    (data : ChannelLocalEventObject Index Time Carrier Law) :
    Nonempty (PairExchangeCurrent data.object.currentCarrier data.object.Leg) ∧
      data.object.currentDirectReturnCompatible ∧
      data.object.visiblePrimitiveReadoutAutonomous ∧
      data.object.minimalVisibleQuotients ∧
      (∀ role : VisibleCarrierRole,
        ∀ current :
          PairExchangeCurrent data.object.currentCarrier data.object.Leg,
          data.object.channelRead role (data.object.generator current) =
            data.object.channelTransport role
              (data.object.channelRead role current)) ∧
      (∀ role : VisibleCarrierRole,
        ∀ current :
          PairExchangeCurrent data.object.currentCarrier data.object.Leg,
          data.object.channelResidual role current =
            data.object.channelRead role
              (data.object.returnedDefect current)) := by
  exact data.toLocalEventLawForm.surface

/-- Channel-compatible anchored detached current object. The selected-cut law
surface is now forced directly from the anchored current object plus the same
rolewise exactifier/quotient compatibility. -/
structure ChannelAnchoredObject (Index Time Carrier Law : Type) where
  object : AnchoredCurrentObject Index Time Carrier Law
  transportCompatible :
    ∀ role : VisibleCarrierRole,
      ∀ current : PairExchangeCurrent object.currentCarrier object.Leg,
        (object.quotient role).read (object.exactifier.exactify current) =
          (object.quotient role).evolve ((object.quotient role).read current)

/-- The channel-compatible anchored object determines the selected-cut detached
law form. -/
def ChannelAnchoredObject.toAnchoredLawForm
    {Index Time Carrier Law : Type}
    (data : ChannelAnchoredObject Index Time Carrier Law) :
    AnchoredLawForm Index Time Carrier Law where
  object := data.object
  transportCompatible := by
    intro role current
    exact data.transportCompatible role current

/-- Surface theorem for the channel-compatible anchored object. The selected-cut
detached flagship law is now forced directly from the anchored object package.
-/
theorem ChannelAnchoredObject.surface
    {Index Time Carrier Law : Type}
    (data : ChannelAnchoredObject Index Time Carrier Law) :
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
          (data.object.quotient role).read
              (data.object.exactifier.exactify current) =
            (data.object.quotient role).evolve
              ((data.object.quotient role).read current)) ∧
      (∀ role : VisibleCarrierRole,
        ∀ current :
          PairExchangeCurrent data.object.currentCarrier data.object.Leg,
          data.toAnchoredLawForm.channelResidual role current =
            data.toAnchoredLawForm.channelRead role
              (data.toAnchoredLawForm.returnedDefect current)) := by
  obtain ⟨hcurrent, hdirret, haut, hmin, hexact, hforced, htransport, hlaw, hresidual⟩ :=
    data.toAnchoredLawForm.surface
  exact
    ⟨hcurrent,
      hdirret,
      haut,
      hmin,
      hexact,
      hforced,
      htransport,
      data.transportCompatible,
      hresidual⟩

end ClosureCurrent

end CoherenceCalculus
