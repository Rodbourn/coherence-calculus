import CoherenceCalculus.PartIV.ClosureCurrentObjectCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentLawFormCore

Compact law form for the detached closure-current lane.

`ClosureCurrentObjectCore` introduced the detached pair-current object and its
visible quotient objects. This file records the first concise equation surface
for that lane:

* one local generator, namely the event exactifier;
* one visible channel readout for each present role;
* one autonomous visible transport on each readout;
* one returned-defect channel on each readout.

The central equation is the rolewise commutation law

`channelRead (generator current) = channelTransport (channelRead current)`.

This remains detached from the bedrock-certified spine. Its role is to expose
the candidate microscopic law in a compact mathematical form rather than as a
longer tower of interface packages.
-/

namespace ClosureCurrent

/-- The local generator of the detached current lane is the event exactifier. -/
def LocalEventObject.generator
    {Index Time Carrier Law : Type}
    (data : LocalEventObject Index Time Carrier Law) :
    PairExchangeCurrent data.currentCarrier data.Leg →
      PairExchangeCurrent data.currentCarrier data.Leg :=
  data.exactifier.exactify

/-- The visible returned defect on the detached current lane is read through
the event exactifier's returned-defect current. -/
def LocalEventObject.returnedDefect
    {Index Time Carrier Law : Type}
    (data : LocalEventObject Index Time Carrier Law) :
    PairExchangeCurrent data.currentCarrier data.Leg →
      PairExchangeCurrent data.currentCarrier data.Leg :=
  data.exactifier.returnedDefect

/-- Rolewise channel readout of the detached current. -/
def LocalEventObject.channelRead
    {Index Time Carrier Law : Type}
    (data : LocalEventObject Index Time Carrier Law)
    (role : VisibleCarrierRole) :
    PairExchangeCurrent data.currentCarrier data.Leg → data.visible role :=
  (data.quotient role).read

/-- Rolewise autonomous channel transport induced on the visible quotient. -/
def LocalEventObject.channelTransport
    {Index Time Carrier Law : Type}
    (data : LocalEventObject Index Time Carrier Law)
    (role : VisibleCarrierRole) :
    data.visible role → data.visible role :=
  (data.quotient role).evolve

/-- Rolewise visible residual obtained by reading the returned-defect current on
the same channel. -/
def LocalEventObject.channelResidual
    {Index Time Carrier Law : Type}
    (data : LocalEventObject Index Time Carrier Law)
    (role : VisibleCarrierRole) :
    PairExchangeCurrent data.currentCarrier data.Leg → data.visible role :=
  fun current => data.channelRead role (data.returnedDefect current)

/-- Channel transport compatibility for the detached current lane. This is the
compact generator/transport/channel equation role by role. -/
def LocalEventObject.channelTransportCompatible
    {Index Time Carrier Law : Type}
    (data : LocalEventObject Index Time Carrier Law) : Prop :=
  ∀ role : VisibleCarrierRole,
    ∀ current : PairExchangeCurrent data.currentCarrier data.Leg,
      data.channelRead role (data.generator current) =
        data.channelTransport role (data.channelRead role current)

/-- Detached compact law form for the candidate closure-current lane. This is
the smallest package that turns the object-level current into an explicit
generator/transport/channel equation. -/
structure LocalEventLawForm (Index Time Carrier Law : Type) where
  object : LocalEventObject Index Time Carrier Law
  transportCompatible : object.channelTransportCompatible

/-- The returned-defect channel is definitionally the same readout applied to
the returned-defect current. -/
theorem LocalEventObject.channelResidual_eq
    {Index Time Carrier Law : Type}
    (data : LocalEventObject Index Time Carrier Law)
    (role : VisibleCarrierRole)
    (current : PairExchangeCurrent data.currentCarrier data.Leg) :
    data.channelResidual role current =
      data.channelRead role (data.returnedDefect current) := by
  rfl

/-- Surface theorem for the compact detached law form. The pair current already
carries direct/return compatibility, autonomous minimal visible quotients, and
now also the explicit generator/transport/channel equation role by role. -/
theorem LocalEventLawForm.surface
    {Index Time Carrier Law : Type}
    (data : LocalEventLawForm Index Time Carrier Law) :
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
  obtain ⟨hcurrent, hdirret, haut, hmin, _hstock, _hrel, _hloss, _hdefect⟩ :=
    data.object.surface
  exact
    ⟨hcurrent,
      hdirret,
      haut,
      hmin,
      data.transportCompatible,
      by
        intro role current
        exact data.object.channelResidual_eq role current⟩

end ClosureCurrent

end CoherenceCalculus
