import CoherenceCalculus.PartIV.ClosureCurrentObservedObjectCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentAnchorCore

Detached selected-observer anchor for the candidate closure-current lane.

`ClosureCurrentObservedObjectCore` still packages a predicate-style observer
realization of visible quotient values. This file compresses that one step
further:

* one selected observer anchor, namely the observer already carried by the
  selected bridge;
* one common closure-class transport package on that same selected cut.

The earlier observer-realized current object is then recovered by reading each
visible quotient value at that one anchor.
-/

namespace ClosureCurrent

/-- Smallest selected-observer anchor for the detached current lane. This keeps
only the hidden current object, the visible quotient objects, and the closure
identity at the selected bridge observer itself. It does not yet transport that
closure identity to every observer on the selected cut. -/
structure CurrentAnchor (Index Time Carrier Law : Type) where
  bridge : BridgeData Index Time Carrier Law
  physicalPrinciple : PhysicalRealizationPrinciple Time Carrier Law
  sameSelectedLawAsBridge :
    physicalPrinciple.selectedLaw.selection =
      bridge.selectedBridge.observer.selection
  currentCarrier : PairExchangeCarrier
  Leg : Type
  current : PairExchangeCurrent currentCarrier Leg
  visible : VisibleCarrierRole → Type
  quotient :
    (role : VisibleCarrierRole) →
      VisibleQuotient currentCarrier Leg (visible role)
  sameAnchoredContinuumClosureClass :
    physicalPrinciple.selectedLaw.endpointClosureClass =
      bridge.selectedBridge.observer.continuumClass

/-- Direct/return compatibility is already visible on the current anchor. -/
def CurrentAnchor.currentDirectReturnCompatible
    {Index Time Carrier Law : Type}
    (data : CurrentAnchor Index Time Carrier Law) : Prop :=
  ∀ x : data.currentCarrier.Value,
    data.currentCarrier.reverse (data.currentCarrier.reverse x) = x ∧
      data.currentCarrier.stock (data.currentCarrier.reverse x) =
        data.currentCarrier.stock x

/-- Visible quotient autonomy is already visible on the current anchor. -/
def CurrentAnchor.visiblePrimitiveReadoutAutonomous
    {Index Time Carrier Law : Type}
    (data : CurrentAnchor Index Time Carrier Law) : Prop :=
  ∀ role : VisibleCarrierRole,
    (data.quotient role).autonomousReadout

/-- Minimal visible quotient structure is already visible on the current
anchor. -/
def CurrentAnchor.minimalVisibleQuotients
    {Index Time Carrier Law : Type}
    (data : CurrentAnchor Index Time Carrier Law) : Prop :=
  ∀ role : VisibleCarrierRole,
    (data.quotient role).minimalNontrivial

/-- Surface theorem for the minimal current anchor. Before any transport to the
full selected cut is added, the selected bridge observer already carries exact
visibility, forced continuum closure, direct/return compatibility, and
autonomous minimal visible quotients. -/
theorem CurrentAnchor.surface
    {Index Time Carrier Law : Type}
    (data : CurrentAnchor Index Time Carrier Law) :
    Nonempty (PairExchangeCurrent data.currentCarrier data.Leg) ∧
      data.currentDirectReturnCompatible ∧
      data.visiblePrimitiveReadoutAutonomous ∧
      data.minimalVisibleQuotients ∧
      exactVisibleOnCut
        (data.bridge.selectedBridge.observer.selection.realization.tower.π
          data.bridge.selectedBridge.observer.selection.horizon)
        (selected_observed_law data.bridge.selectedBridge.observer.selection).op ∧
      ForcedContinuumLaw
        data.bridge.selectedBridge.observer.continuumClass
        data.physicalPrinciple.selectedLaw.selectedClosureLaw := by
  have hclosure :
      ForcedContinuumLaw
        data.bridge.selectedBridge.observer.continuumClass
        data.physicalPrinciple.selectedLaw.selectedClosureLaw := by
    obtain ⟨_hsel, _hexact, hforced⟩ :=
      SelectedCut.carrierClosureReadout
        { physical := data.physicalPrinciple
          observer := data.bridge.selectedBridge.observer
          sameSelectionDatum := data.sameSelectedLawAsBridge
          sameContinuumClosureClass :=
            data.sameAnchoredContinuumClosureClass }
    exact hforced
  have hexact :
      exactVisibleOnCut
        (data.bridge.selectedBridge.observer.selection.realization.tower.π
          data.bridge.selectedBridge.observer.selection.horizon)
        (selected_observed_law data.bridge.selectedBridge.observer.selection).op := by
    simpa [data.sameSelectedLawAsBridge] using
      data.physicalPrinciple.exactVisibleSelectedLawOnLeastMotionCut
  exact
    ⟨⟨data.current⟩,
      by
        intro x
        exact
          ⟨data.currentCarrier.reverse_involutive x,
            data.currentCarrier.stock_reverse x⟩,
      by
        intro role
        exact (data.quotient role).autonomousReadout_valid,
      by
        intro role
        exact (data.quotient role).minimalNontrivial_valid,
      hexact,
      hclosure⟩

/-- Selected-cut transport above the minimal current anchor. This adds exactly
the statement that the selected-law continuum class transports to every observer
reading the same selected cut. -/
structure AnchoredCurrentTransport (Index Time Carrier Law : Type)
    extends CurrentAnchor Index Time Carrier Law where
  closureTransport :
    ClosureClassTransport
      Time Carrier Law
      bridge.selectedBridge.observer.selection
      physicalPrinciple.selectedLaw.endpointClosureClass

/-- Surface theorem for the transported current anchor. The only new output
above the minimal anchor is full selected-cut closure transport. -/
theorem AnchoredCurrentTransport.surface
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentTransport Index Time Carrier Law) :
    Nonempty (PairExchangeCurrent data.currentCarrier data.Leg) ∧
      data.toCurrentAnchor.currentDirectReturnCompatible ∧
      data.toCurrentAnchor.visiblePrimitiveReadoutAutonomous ∧
      data.toCurrentAnchor.minimalVisibleQuotients ∧
      exactVisibleOnCut
        (data.bridge.selectedBridge.observer.selection.realization.tower.π
          data.bridge.selectedBridge.observer.selection.horizon)
        (selected_observed_law data.bridge.selectedBridge.observer.selection).op ∧
      ForcedContinuumLaw
        data.bridge.selectedBridge.observer.continuumClass
        data.physicalPrinciple.selectedLaw.selectedClosureLaw ∧
      (∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
        observer.selection = data.bridge.selectedBridge.observer.selection →
          data.physicalPrinciple.selectedLaw.endpointClosureClass =
            observer.continuumClass) := by
  obtain ⟨hcurrent, hdirret, haut, hmin, hexact, hforced⟩ :=
    data.toCurrentAnchor.surface
  exact
    ⟨hcurrent,
      hdirret,
      haut,
      hmin,
      hexact,
      hforced,
      fun observer hsel => data.closureTransport.sameSelection observer hsel⟩

/-- Detached current object whose visible quotient values are read at the
selected bridge observer itself. The only remaining observer-side extra datum
is the common closure-class transport on that selected cut. -/
structure AnchoredCurrentObject (Index Time Carrier Law : Type) where
  bridge : BridgeData Index Time Carrier Law
  physicalPrinciple : PhysicalRealizationPrinciple Time Carrier Law
  sameSelectedLawAsBridge :
    physicalPrinciple.selectedLaw.selection =
      bridge.selectedBridge.observer.selection
  commonGrammar : CommonPartIVGrammar
  currentCarrier : PairExchangeCarrier
  Leg : Type
  distinguishedLeg : Leg
  firstStableBulkEventHasFourLegs : Prop
  sixPairSlots : Prop
  current : PairExchangeCurrent currentCarrier Leg
  exactifier : EventExactifier currentCarrier Leg
  visible : VisibleCarrierRole → Type
  quotient :
    (role : VisibleCarrierRole) →
      VisibleQuotient currentCarrier Leg (visible role)
  closureTransport :
    ClosureClassTransport
      Time Carrier Law
      bridge.selectedBridge.observer.selection
      physicalPrinciple.selectedLaw.endpointClosureClass
  bundleArisesIntrinsicallyOnLeastMotionCut : Prop
  noCarrierWiseVisibilityHypotheses : Prop
  firstStableBulkEventHasFourLegs_valid :
    firstStableBulkEventHasFourLegs
  sixPairSlots_valid : sixPairSlots
  hiddenCoherentLaw_valid : commonGrammar.hiddenCoherentLaw
  residualReturnFieldOnSelectedCut_valid :
    commonGrammar.residualReturnFieldOnSelectedCut
  selectedVisibleLawPhysicallyRealized_valid :
    commonGrammar.selectedVisibleLawPhysicallyRealized
  onlyReturnActsOnVisibleBundle_valid :
    commonGrammar.onlyReturnActsOnVisibleBundle
  characteristicEndpointReduction_valid :
    commonGrammar.characteristicEndpointReduction
  canonicalSectorGeneration_valid :
    commonGrammar.canonicalSectorGeneration
  symmetryRigidMinimalClosure_valid :
    commonGrammar.symmetryRigidMinimalClosure
  carrierLevelPhysicalLaw_valid :
    commonGrammar.carrierLevelPhysicalLaw
  bundleArisesIntrinsicallyOnLeastMotionCut_valid :
    bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses_valid :
    noCarrierWiseVisibilityHypotheses

/-- The anchored current object determines the transported current anchor. -/
def AnchoredCurrentObject.toAnchoredCurrentTransport
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentObject Index Time Carrier Law) :
    AnchoredCurrentTransport Index Time Carrier Law where
  toCurrentAnchor := {
    bridge := data.bridge
    physicalPrinciple := data.physicalPrinciple
    sameSelectedLawAsBridge := data.sameSelectedLawAsBridge
    currentCarrier := data.currentCarrier
    Leg := data.Leg
    current := data.current
    visible := data.visible
    quotient := data.quotient
    sameAnchoredContinuumClosureClass :=
      data.closureTransport.sameSelection data.bridge.selectedBridge.observer rfl }
  closureTransport := data.closureTransport

/-- The anchored current object refines the smaller current anchor by adding
the full selected-cut closure transport package. -/
def AnchoredCurrentObject.toCurrentAnchor
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentObject Index Time Carrier Law) :
    CurrentAnchor Index Time Carrier Law where
  bridge := data.bridge
  physicalPrinciple := data.physicalPrinciple
  sameSelectedLawAsBridge := data.sameSelectedLawAsBridge
  currentCarrier := data.currentCarrier
  Leg := data.Leg
  current := data.current
  visible := data.visible
  quotient := data.quotient
  sameAnchoredContinuumClosureClass :=
    data.closureTransport.sameSelection data.bridge.selectedBridge.observer rfl

/-- The transported anchored current object still carries the smaller anchored
surface before its closure transport is used elsewhere. -/
theorem AnchoredCurrentObject.anchorSurface
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentObject Index Time Carrier Law) :
    Nonempty (PairExchangeCurrent data.currentCarrier data.Leg) ∧
      data.toCurrentAnchor.currentDirectReturnCompatible ∧
      data.toCurrentAnchor.visiblePrimitiveReadoutAutonomous ∧
      data.toCurrentAnchor.minimalVisibleQuotients ∧
      exactVisibleOnCut
        (data.bridge.selectedBridge.observer.selection.realization.tower.π
          data.bridge.selectedBridge.observer.selection.horizon)
        (selected_observed_law data.bridge.selectedBridge.observer.selection).op ∧
      ForcedContinuumLaw
        data.bridge.selectedBridge.observer.continuumClass
        data.physicalPrinciple.selectedLaw.selectedClosureLaw := by
  exact data.toCurrentAnchor.surface

/-- The anchored current object also carries the full selected-cut closure
transport surface before the remaining bundle-intrinsicity clauses are used. -/
theorem AnchoredCurrentObject.transportSurface
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentObject Index Time Carrier Law) :
    Nonempty (PairExchangeCurrent data.currentCarrier data.Leg) ∧
      data.toCurrentAnchor.currentDirectReturnCompatible ∧
      data.toCurrentAnchor.visiblePrimitiveReadoutAutonomous ∧
      data.toCurrentAnchor.minimalVisibleQuotients ∧
      exactVisibleOnCut
        (data.bridge.selectedBridge.observer.selection.realization.tower.π
          data.bridge.selectedBridge.observer.selection.horizon)
        (selected_observed_law data.bridge.selectedBridge.observer.selection).op ∧
      ForcedContinuumLaw
        data.bridge.selectedBridge.observer.continuumClass
        data.physicalPrinciple.selectedLaw.selectedClosureLaw ∧
      (∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
        observer.selection = data.bridge.selectedBridge.observer.selection →
          data.physicalPrinciple.selectedLaw.endpointClosureClass =
            observer.continuumClass) := by
  simpa [AnchoredCurrentObject.toAnchoredCurrentTransport, AnchoredCurrentObject.toCurrentAnchor]
    using data.toAnchoredCurrentTransport.surface

/-- The anchored current object recovers the earlier observer-realized current
object by reading each visible quotient value at the selected bridge observer.
-/
def AnchoredCurrentObject.toObservedCurrentObject
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentObject Index Time Carrier Law) :
    ObservedCurrentObject Index Time Carrier Law where
  bridge := data.bridge
  physicalPrinciple := data.physicalPrinciple
  sameSelectedLawAsBridge := data.sameSelectedLawAsBridge
  commonGrammar := data.commonGrammar
  currentCarrier := data.currentCarrier
  Leg := data.Leg
  distinguishedLeg := data.distinguishedLeg
  firstStableBulkEventHasFourLegs := data.firstStableBulkEventHasFourLegs
  sixPairSlots := data.sixPairSlots
  current := data.current
  exactifier := data.exactifier
  visible := data.visible
  quotient := data.quotient
  observerRealization := {
    readsVisibleState := fun role state observer =>
      observer = data.bridge.selectedBridge.observer ∧
        state = (data.quotient role).read data.current
    sameSelection := by
      intro role state observer hstate
      rcases hstate with ⟨hobs, _hstate⟩
      calc
        observer.selection = data.bridge.selectedBridge.observer.selection := by
          rw [hobs]
        _ = data.bridge.selectedBridge.observer.selection := rfl
    sameContinuumClosureClass := by
      intro observer hselection
      exact data.closureTransport.sameSelection observer hselection }
  bundleArisesIntrinsicallyOnLeastMotionCut :=
    data.bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses :=
    data.noCarrierWiseVisibilityHypotheses
  firstStableBulkEventHasFourLegs_valid :=
    data.firstStableBulkEventHasFourLegs_valid
  sixPairSlots_valid := data.sixPairSlots_valid
  hiddenCoherentLaw_valid := data.hiddenCoherentLaw_valid
  residualReturnFieldOnSelectedCut_valid :=
    data.residualReturnFieldOnSelectedCut_valid
  selectedVisibleLawPhysicallyRealized_valid :=
    data.selectedVisibleLawPhysicallyRealized_valid
  onlyReturnActsOnVisibleBundle_valid :=
    data.onlyReturnActsOnVisibleBundle_valid
  characteristicEndpointReduction_valid :=
    data.characteristicEndpointReduction_valid
  canonicalSectorGeneration_valid :=
    data.canonicalSectorGeneration_valid
  symmetryRigidMinimalClosure_valid :=
    data.symmetryRigidMinimalClosure_valid
  carrierLevelPhysicalLaw_valid :=
    data.carrierLevelPhysicalLaw_valid
  bundleArisesIntrinsicallyOnLeastMotionCut_valid :=
    data.bundleArisesIntrinsicallyOnLeastMotionCut_valid
  noCarrierWiseVisibilityHypotheses_valid :=
    data.noCarrierWiseVisibilityHypotheses_valid

/-- Surface theorem for the anchored current object. The reduced observer side
already closes from one selected bridge observer plus common closure transport.
-/
theorem AnchoredCurrentObject.surface
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentObject Index Time Carrier Law) :
    Nonempty (PairExchangeCurrent data.currentCarrier data.Leg) ∧
      data.toObservedCurrentObject.toLocalEventObject.currentDirectReturnCompatible ∧
      data.toObservedCurrentObject.toLocalEventObject.visiblePrimitiveReadoutAutonomous ∧
      data.toObservedCurrentObject.toLocalEventObject.minimalVisibleQuotients ∧
      Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) := by
  exact data.toObservedCurrentObject.surface

/-- Anchored current object plus intrinsic sector-generation clauses. -/
structure AnchoredCurrentSectorObject (Index Time Carrier Law : Type)
    extends AnchoredCurrentObject Index Time Carrier Law where
  canonicalGeneration : SelectedBundle.CanonicalGeneration
  generatedFromIntrinsicChannelAlgebra : Prop
  minimalCompatibleRealizationsOnly : Prop
  generatedFromIntrinsicChannelAlgebra_valid :
    generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly_valid :
    minimalCompatibleRealizationsOnly

/-- The anchored current sector object recovers the earlier observer-realized
sector object. -/
def AnchoredCurrentSectorObject.toObservedCurrentSectorObject
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentSectorObject Index Time Carrier Law) :
    ObservedCurrentSectorObject Index Time Carrier Law where
  toObservedCurrentObject := data.toAnchoredCurrentObject.toObservedCurrentObject
  canonicalGeneration := data.canonicalGeneration
  generatedFromIntrinsicChannelAlgebra :=
    data.generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly :=
    data.minimalCompatibleRealizationsOnly
  generatedFromIntrinsicChannelAlgebra_valid :=
    data.generatedFromIntrinsicChannelAlgebra_valid
  minimalCompatibleRealizationsOnly_valid :=
    data.minimalCompatibleRealizationsOnly_valid

/-- Surface theorem for the anchored current sector object. -/
theorem AnchoredCurrentSectorObject.surface
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentSectorObject Index Time Carrier Law) :
    Nonempty (PairExchangeCurrent data.currentCarrier data.Leg) ∧
      data.toObservedCurrentObject.toLocalEventObject.currentDirectReturnCompatible ∧
      data.toObservedCurrentObject.toLocalEventObject.visiblePrimitiveReadoutAutonomous ∧
      data.toObservedCurrentObject.toLocalEventObject.minimalVisibleQuotients ∧
      Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  exact data.toObservedCurrentSectorObject.surface

end ClosureCurrent

end CoherenceCalculus
