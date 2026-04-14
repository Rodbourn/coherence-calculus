import CoherenceCalculus.PartIV.ClosureCurrentMicroscopicCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentEventLawCore

Detached exact-exchange and event-exactification law interfaces for the
candidate microscopic closure-current lane.

This file introduces the two-law formulation discussed in the manuscript:

* `ExactExchangeCurrentLaw` records one hidden exact exchange current on a
  common selected bundle together with the current-side grammar needed to read
  visible carrier roles from it.
* `EventExactificationLaw` adds the local event exactification / autonomy
  clauses and proves that they recover the role-indexed microscopic
  selected-bundle surface.
* `EventExactificationSectorLaw` adds the intrinsic non-dictionary
  sector-generation clauses and therefore closes the current upstream forcing
  seam.

Nothing here is claimed as part of the narrower bedrock-certified spine. The
purpose is to make the remaining theorem target explicit in the same
mathematical language as the manuscript’s detached microscopic-law candidate.
-/

namespace ClosureCurrent

/-- Detached exact exchange current law. This is the current-side half of the
microscopic-law candidate: one hidden exact exchange current on a common
selected bundle, together with the role-indexed readout and common continuum
closure transport needed to read visible carrier roles from that current. -/
structure ExactExchangeCurrentLaw (Index Time Carrier Law : Type) where
  bridge : BridgeData Index Time Carrier Law
  assembly : BundleAssemblyLaw Time Carrier Law
  sameSelectedLawAsBridge :
    assembly.physicalPrinciple.selectedLaw.selection =
      bridge.selectedBridge.observer.selection
  commonGrammar : CommonPartIVGrammar
  hiddenExactExchangeCurrent : Prop
  currentStockConserved : Prop
  currentDirectReturnCompatible : Prop
  roleReadout :
    RoleReadoutFamily
      Time Carrier Law
      bridge.selectedBridge.observer.selection
  continuumClosure :
    ClosureClassTransport
      Time Carrier Law
      bridge.selectedBridge.observer.selection
      assembly.physicalPrinciple.selectedLaw.endpointClosureClass
  hiddenExactExchangeCurrent_valid : hiddenExactExchangeCurrent
  currentStockConserved_valid : currentStockConserved
  currentDirectReturnCompatible_valid : currentDirectReturnCompatible
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

/-- The detached exact exchange current law unpacks to the current-side
grammar already used informally in Chapter 10. -/
theorem ExactExchangeCurrentLaw.surface
    {Index Time Carrier Law : Type}
    (data : ExactExchangeCurrentLaw Index Time Carrier Law) :
    data.hiddenExactExchangeCurrent ∧
      data.currentStockConserved ∧
      data.currentDirectReturnCompatible ∧
      data.commonGrammar.hiddenCoherentLaw ∧
      data.commonGrammar.residualReturnFieldOnSelectedCut ∧
      data.commonGrammar.selectedVisibleLawPhysicallyRealized ∧
      data.commonGrammar.onlyReturnActsOnVisibleBundle ∧
      data.commonGrammar.characteristicEndpointReduction ∧
      data.commonGrammar.canonicalSectorGeneration ∧
      data.commonGrammar.symmetryRigidMinimalClosure ∧
      data.commonGrammar.carrierLevelPhysicalLaw := by
  exact
    ⟨data.hiddenExactExchangeCurrent_valid,
      data.currentStockConserved_valid,
      data.currentDirectReturnCompatible_valid,
      data.hiddenCoherentLaw_valid,
      data.residualReturnFieldOnSelectedCut_valid,
      data.selectedVisibleLawPhysicallyRealized_valid,
      data.onlyReturnActsOnVisibleBundle_valid,
      data.characteristicEndpointReduction_valid,
      data.canonicalSectorGeneration_valid,
      data.symmetryRigidMinimalClosure_valid,
      data.carrierLevelPhysicalLaw_valid⟩

/-- Detached event exactification / autonomy law. This is the event-side half
of the microscopic-law candidate: local lossless exactification, relabeling
equivariance, autonomous visible readout, and returned defect as the visible
residual. -/
structure EventExactificationLaw (Index Time Carrier Law : Type)
    extends ExactExchangeCurrentLaw Index Time Carrier Law where
  relabelingEquivariant : Prop
  localLosslessExactification : Prop
  visiblePrimitiveReadoutAutonomous : Prop
  returnedDefectActsAsVisibleResidual : Prop
  bundleArisesIntrinsicallyOnLeastMotionCut : Prop
  noCarrierWiseVisibilityHypotheses : Prop
  relabelingEquivariant_valid : relabelingEquivariant
  localLosslessExactification_valid : localLosslessExactification
  visiblePrimitiveReadoutAutonomous_valid : visiblePrimitiveReadoutAutonomous
  returnedDefectActsAsVisibleResidual_valid :
    returnedDefectActsAsVisibleResidual
  bundleArisesIntrinsicallyOnLeastMotionCut_valid :
    bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses_valid :
    noCarrierWiseVisibilityHypotheses

/-- The event exactification / autonomy law yields the role-indexed
microscopic selected-bundle law. -/
def EventExactificationLaw.toMicroscopicBundleLaw
    {Index Time Carrier Law : Type}
    (data : EventExactificationLaw Index Time Carrier Law) :
    MicroscopicBundleLaw Index Time Carrier Law where
  bridge := data.bridge
  assembly := data.assembly
  sameSelectedLawAsBridge := data.sameSelectedLawAsBridge
  roles := data.roleReadout
  continuumClosure := data.continuumClosure
  bundleArisesIntrinsicallyOnLeastMotionCut :=
    data.bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses :=
    data.noCarrierWiseVisibilityHypotheses
  bundleArisesIntrinsicallyOnLeastMotionCut_valid :=
    data.bundleArisesIntrinsicallyOnLeastMotionCut_valid
  noCarrierWiseVisibilityHypotheses_valid :=
    data.noCarrierWiseVisibilityHypotheses_valid

/-- Surface theorem for the detached event exactification law: the two-law
microscopic package already recovers the role-indexed microscopic
selected-bundle surface. -/
theorem EventExactificationLaw.surface
    {Index Time Carrier Law : Type}
    (data : EventExactificationLaw Index Time Carrier Law) :
    data.hiddenExactExchangeCurrent ∧
      data.currentStockConserved ∧
      data.currentDirectReturnCompatible ∧
      data.relabelingEquivariant ∧
      data.localLosslessExactification ∧
      data.visiblePrimitiveReadoutAutonomous ∧
      data.returnedDefectActsAsVisibleResidual ∧
      data.commonGrammar.hiddenCoherentLaw ∧
      data.commonGrammar.residualReturnFieldOnSelectedCut ∧
      data.commonGrammar.selectedVisibleLawPhysicallyRealized ∧
      data.commonGrammar.onlyReturnActsOnVisibleBundle ∧
      Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      realized_generator_carries_bedrock_law data.bridge.generator ∧
      AutonomousHorizon
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator ∧
      horizonFiberInvariant
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator ∧
      (∀ role : VisibleCarrierRole,
        ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
          data.roleReadout.readsOnSelectedBundle role observer →
            (data.assembly.physicalPrinciple.selectedLaw.selection =
              observer.selection) ∧
            exactVisibleOnCut
              (observer.selection.realization.tower.π observer.selection.horizon)
              (selected_observed_law observer.selection).op ∧
            ForcedContinuumLaw
              observer.continuumClass
              data.assembly.physicalPrinciple.selectedLaw.selectedClosureLaw) := by
  obtain ⟨hcurrent, hstock, hdirret, hhidden, hreturn, hvislaw, honlyReturn,
    _hchar, _hcanon, _hsymm, _hcarrier⟩ := data.toExactExchangeCurrentLaw.surface
  obtain ⟨hbundle, hbedrock, haut, hfiber, hreadout⟩ :=
    data.toMicroscopicBundleLaw.surface
  exact
    ⟨hcurrent,
      hstock,
      hdirret,
      data.relabelingEquivariant_valid,
      data.localLosslessExactification_valid,
      data.visiblePrimitiveReadoutAutonomous_valid,
      data.returnedDefectActsAsVisibleResidual_valid,
      hhidden,
      hreturn,
      hvislaw,
      honlyReturn,
      hbundle,
      hbedrock,
      haut,
      hfiber,
      hreadout⟩

/-- Detached event exactification law together with the intrinsic
non-dictionary sector-generation clauses needed for Step 3. -/
structure EventExactificationSectorLaw (Index Time Carrier Law : Type)
    extends EventExactificationLaw Index Time Carrier Law where
  canonicalGeneration : SelectedBundle.CanonicalGeneration
  generatedFromIntrinsicChannelAlgebra : Prop
  minimalCompatibleRealizationsOnly : Prop
  generatedFromIntrinsicChannelAlgebra_valid :
    generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly_valid :
    minimalCompatibleRealizationsOnly

/-- The detached event exactification / sector law yields the role-indexed
microscopic sector law. -/
def EventExactificationSectorLaw.toMicroscopicSectorLaw
    {Index Time Carrier Law : Type}
    (data : EventExactificationSectorLaw Index Time Carrier Law) :
    MicroscopicSectorLaw Index Time Carrier Law where
  bundle := data.toEventExactificationLaw.toMicroscopicBundleLaw
  canonicalGeneration := data.canonicalGeneration
  generatedFromIntrinsicChannelAlgebra :=
    data.generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly :=
    data.minimalCompatibleRealizationsOnly
  generatedFromIntrinsicChannelAlgebra_valid :=
    data.generatedFromIntrinsicChannelAlgebra_valid
  minimalCompatibleRealizationsOnly_valid :=
    data.minimalCompatibleRealizationsOnly_valid

/-- Surface theorem for the detached event exactification / sector law: the
two-law microscopic package plus the intrinsic sector-generation clauses close
the current upstream forcing seam. -/
theorem EventExactificationSectorLaw.surface
    {Index Time Carrier Law : Type}
    (data : EventExactificationSectorLaw Index Time Carrier Law) :
    data.hiddenExactExchangeCurrent ∧
      data.currentStockConserved ∧
      data.currentDirectReturnCompatible ∧
      data.relabelingEquivariant ∧
      data.localLosslessExactification ∧
      data.visiblePrimitiveReadoutAutonomous ∧
      data.returnedDefectActsAsVisibleResidual ∧
      Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
      realized_generator_carries_bedrock_law data.bridge.generator ∧
      AutonomousHorizon
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator ∧
      horizonFiberInvariant
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator ∧
      (∀ role : VisibleCarrierRole,
        ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
          data.roleReadout.readsOnSelectedBundle role observer →
            (data.assembly.physicalPrinciple.selectedLaw.selection =
              observer.selection) ∧
            exactVisibleOnCut
              (observer.selection.realization.tower.π observer.selection.horizon)
              (selected_observed_law observer.selection).op ∧
            ForcedContinuumLaw
              observer.continuumClass
              data.assembly.physicalPrinciple.selectedLaw.selectedClosureLaw) ∧
      data.generatedFromIntrinsicChannelAlgebra ∧
      data.minimalCompatibleRealizationsOnly ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  obtain ⟨hcurrent, hstock, hdirret, hrel, hexact, hautread, hdefect,
    _hhidden, _hreturn, _hvislaw, _honlyReturn, hbundle, hbedrock, haut, hfiber,
    hreadout⟩ := data.toEventExactificationLaw.surface
  obtain ⟨_hbundle', hsector, _hbedrock', _haut', _hfiber', _hreadout',
    hgen, hmin, hprofile⟩ := data.toMicroscopicSectorLaw.surface
  exact
    ⟨hcurrent,
      hstock,
      hdirret,
      hrel,
      hexact,
      hautread,
      hdefect,
      hbundle,
      hsector,
      hbedrock,
      haut,
      hfiber,
      hreadout,
      hgen,
      hmin,
      hprofile⟩

end ClosureCurrent

end CoherenceCalculus
