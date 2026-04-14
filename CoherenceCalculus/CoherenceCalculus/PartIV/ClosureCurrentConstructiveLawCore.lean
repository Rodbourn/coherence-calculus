import CoherenceCalculus.PartIV.ClosureCurrentOriginReadoutCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentConstructiveLawCore

Self-contained constructive law above the minimal origin readout layer.

`ClosureCurrentLocalEventCore` isolates the proposition-level law
`MicroscopicClosureLaw`, but that law alone does not carry enough data to build
`OriginClosureWitness`. `OriginReadoutLaw law` isolates the exact
selected-anchor readout and transport data needed to force
`OriginClosureTarget law` above a fixed microscopic law.

This file now splits the next constructive layer into three pieces:

* `ConstructiveAnchorCurrentLaw` adds back only the exactifier and the first
  closure-stable bulk-event bookkeeping needed to read a full
  `MicroscopicClosureLaw` directly from the selected anchor itself;
* `ConstructiveCurrentLaw` adds the common selected-cut closure transport on
  top of that anchor-side current law;
* `ConstructiveMicroscopicClauses law` carries only the common grammar and the
  two bundle-intrinsicity clauses above one fixed microscopic law.

`ConstructiveMicroscopicLaw` is then the self-contained package combining those
two pieces, still strictly below the anchored current object because it forgets
the distinguished leg. The sector extension on the detached lane inherits the
same constructive origin layer and still forces `SectorClosureTarget`.
-/

namespace ClosureCurrent

/-- Smaller constructive anchor-side current law at the origin seam. This
keeps the selected-anchor current, the visible quotients, and exactly the
exactifier and slot-count bookkeeping needed to read one proposition-level
microscopic closure law. It does not yet include full selected-cut closure
transport. -/
structure ConstructiveAnchorCurrentLaw
    (Index Time Carrier Law : Type)
    extends CurrentAnchor Index Time Carrier Law where
  firstStableBulkEventHasFourLegs : Prop
  sixPairSlots : Prop
  exactifier : EventExactifier currentCarrier Leg
  firstStableBulkEventHasFourLegs_valid :
    firstStableBulkEventHasFourLegs
  sixPairSlots_valid : sixPairSlots

/-- Smaller constructive current law at the origin seam. This keeps the
selected-anchor current, the visible quotients, the common selected-cut
closure transport, and exactly the exactifier and slot-count bookkeeping
needed to read one proposition-level microscopic closure law. -/
structure ConstructiveCurrentLaw
    (Index Time Carrier Law : Type)
    extends AnchoredCurrentTransport Index Time Carrier Law where
  firstStableBulkEventHasFourLegs : Prop
  sixPairSlots : Prop
  exactifier : EventExactifier currentCarrier Leg
  firstStableBulkEventHasFourLegs_valid :
    firstStableBulkEventHasFourLegs
  sixPairSlots_valid : sixPairSlots

/-- Common grammar and intrinsicity clauses above one fixed proposition-level
microscopic closure law. These are the proposition-level clauses that remain
once the constructive current side has already been fixed. -/
structure ConstructiveMicroscopicClauses
    {Index Time Carrier Law : Type}
    (_law : MicroscopicClosureLaw Index Time Carrier Law) where
  commonGrammar : CommonPartIVGrammar
  bundleArisesIntrinsicallyOnLeastMotionCut : Prop
  noCarrierWiseVisibilityHypotheses : Prop
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

/-- Small constructive law at the origin-closure seam. This is strictly below
the anchored current object: it keeps the selected-anchor current, the visible
quotients, the exactifier, the common selected-cut closure transport, and the
grammar/intrinsicity clauses, but it does not choose a distinguished leg. -/
structure ConstructiveMicroscopicLaw
    (Index Time Carrier Law : Type)
    extends AnchoredCurrentTransport Index Time Carrier Law where
  commonGrammar : CommonPartIVGrammar
  firstStableBulkEventHasFourLegs : Prop
  sixPairSlots : Prop
  exactifier : EventExactifier currentCarrier Leg
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

/-- Sector-generating extension of the constructive microscopic law. This is
strictly below the anchored current sector object: it adds only the canonical
generation package and the two sector-generation clauses needed for Step 3. -/
structure ConstructiveSectorLaw
    (Index Time Carrier Law : Type)
    extends ConstructiveMicroscopicLaw Index Time Carrier Law where
  canonicalGeneration : SelectedBundle.CanonicalGeneration
  generatedFromIntrinsicChannelAlgebra : Prop
  minimalCompatibleRealizationsOnly : Prop
  generatedFromIntrinsicChannelAlgebra_valid :
    generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly_valid :
    minimalCompatibleRealizationsOnly

namespace ConstructiveAnchorCurrentLaw

/-- Read the proposition-level microscopic closure law from the constructive
anchor-side current law. -/
def toMicroscopicClosureLaw
    {Index Time Carrier Law : Type}
    (data : ConstructiveAnchorCurrentLaw Index Time Carrier Law) :
    MicroscopicClosureLaw Index Time Carrier Law where
  bridge := data.bridge
  physicalPrinciple := data.physicalPrinciple
  sameSelectedLawAsBridge := data.sameSelectedLawAsBridge
  hiddenExactExchangeCurrent :=
    Nonempty (PairExchangeCurrent data.currentCarrier data.Leg)
  currentLivesOnOrientedPairSlots :=
    ∀ a b : data.Leg,
      data.current.value b a =
        data.currentCarrier.reverse (data.current.value a b)
  firstStableBulkEventCarriesSixSlotCurrent :=
    data.firstStableBulkEventHasFourLegs ∧ data.sixPairSlots
  currentStockConserved := data.exactifier.stockPreserved
  currentDirectReturnCompatible := data.toCurrentAnchor.currentDirectReturnCompatible
  relabelingEquivariant := data.exactifier.relabelingEquivariant
  localLosslessExactification := data.exactifier.localLossless
  visiblePrimitiveReadoutAutonomous :=
    data.toCurrentAnchor.visiblePrimitiveReadoutAutonomous
  returnedDefectActsAsVisibleResidual :=
    data.exactifier.returnedDefectVisibleResidual
  hiddenExactExchangeCurrent_valid := ⟨data.current⟩
  currentLivesOnOrientedPairSlots_valid := data.current.swap_reverse
  firstStableBulkEventCarriesSixSlotCurrent_valid :=
    ⟨data.firstStableBulkEventHasFourLegs_valid, data.sixPairSlots_valid⟩
  currentStockConserved_valid := data.exactifier.stockPreserved_valid
  currentDirectReturnCompatible_valid := by
    intro x
    exact
      ⟨data.currentCarrier.reverse_involutive x,
        data.currentCarrier.stock_reverse x⟩
  relabelingEquivariant_valid := data.exactifier.relabelingEquivariant_valid
  localLosslessExactification_valid := data.exactifier.localLossless_valid
  visiblePrimitiveReadoutAutonomous_valid := by
    intro role
    exact (data.quotient role).autonomousReadout_valid
  returnedDefectActsAsVisibleResidual_valid :=
    data.exactifier.returnedDefectVisibleResidual_valid

/-- Forget the exactifier and slot-count bookkeeping and read the smaller
selected-anchor current layer that already suffices for the anchor side of
origin closure. -/
def toOriginReadoutAnchor
    {Index Time Carrier Law : Type}
    (data : ConstructiveAnchorCurrentLaw Index Time Carrier Law) :
    OriginReadoutAnchor data.toMicroscopicClosureLaw where
  currentCarrier := data.currentCarrier
  Leg := data.Leg
  current := data.current
  visible := data.visible
  quotient := data.quotient

/-- The constructive anchor-side current law already realizes the
selected-anchor current target for its proposition-level microscopic law. -/
theorem originReadoutAnchorTarget
    {Index Time Carrier Law : Type}
    (data : ConstructiveAnchorCurrentLaw Index Time Carrier Law) :
    OriginReadoutAnchorTarget data.toMicroscopicClosureLaw := by
  exact ⟨data.toOriginReadoutAnchor⟩

/-- Add common selected-cut closure transport and recover the larger
constructive current law. -/
def toConstructiveCurrentLaw
    {Index Time Carrier Law : Type}
    (data : ConstructiveAnchorCurrentLaw Index Time Carrier Law)
    (closureTransport :
      ClosureClassTransport
        Time Carrier Law
        data.bridge.selectedBridge.observer.selection
        data.physicalPrinciple.selectedLaw.endpointClosureClass) :
    ConstructiveCurrentLaw Index Time Carrier Law where
  toAnchoredCurrentTransport := {
    toCurrentAnchor := data.toCurrentAnchor
    closureTransport := closureTransport }
  firstStableBulkEventHasFourLegs := data.firstStableBulkEventHasFourLegs
  sixPairSlots := data.sixPairSlots
  exactifier := data.exactifier
  firstStableBulkEventHasFourLegs_valid :=
    data.firstStableBulkEventHasFourLegs_valid
  sixPairSlots_valid := data.sixPairSlots_valid

end ConstructiveAnchorCurrentLaw

/-- Exact law-level constructive anchor-current target above one
proposition-level microscopic closure law. It asks only that the law admit one
constructive anchor-side current realization on the same selected datum. -/
def ConstructiveAnchorCurrentTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) : Prop :=
  ∃ data : ConstructiveAnchorCurrentLaw Index Time Carrier Law,
    data.toMicroscopicClosureLaw = law

namespace ConstructiveAnchorCurrentLaw

/-- Any actual constructive anchor-side current law immediately realizes the
exact law-level constructive anchor-current target for its proposition-level
law. -/
theorem target
    {Index Time Carrier Law : Type}
    (data : ConstructiveAnchorCurrentLaw Index Time Carrier Law) :
    ConstructiveAnchorCurrentTarget data.toMicroscopicClosureLaw := by
  exact ⟨data, rfl⟩

end ConstructiveAnchorCurrentLaw

namespace ConstructiveCurrentLaw

/-- Read the proposition-level microscopic closure law from the constructive
current law. -/
def toMicroscopicClosureLaw
    {Index Time Carrier Law : Type}
    (data : ConstructiveCurrentLaw Index Time Carrier Law) :
    MicroscopicClosureLaw Index Time Carrier Law where
  bridge := data.bridge
  physicalPrinciple := data.physicalPrinciple
  sameSelectedLawAsBridge := data.sameSelectedLawAsBridge
  hiddenExactExchangeCurrent :=
    Nonempty (PairExchangeCurrent data.currentCarrier data.Leg)
  currentLivesOnOrientedPairSlots :=
    ∀ a b : data.Leg,
      data.current.value b a =
        data.currentCarrier.reverse (data.current.value a b)
  firstStableBulkEventCarriesSixSlotCurrent :=
    data.firstStableBulkEventHasFourLegs ∧ data.sixPairSlots
  currentStockConserved := data.exactifier.stockPreserved
  currentDirectReturnCompatible := data.toCurrentAnchor.currentDirectReturnCompatible
  relabelingEquivariant := data.exactifier.relabelingEquivariant
  localLosslessExactification := data.exactifier.localLossless
  visiblePrimitiveReadoutAutonomous :=
    data.toCurrentAnchor.visiblePrimitiveReadoutAutonomous
  returnedDefectActsAsVisibleResidual :=
    data.exactifier.returnedDefectVisibleResidual
  hiddenExactExchangeCurrent_valid := ⟨data.current⟩
  currentLivesOnOrientedPairSlots_valid := data.current.swap_reverse
  firstStableBulkEventCarriesSixSlotCurrent_valid :=
    ⟨data.firstStableBulkEventHasFourLegs_valid, data.sixPairSlots_valid⟩
  currentStockConserved_valid := data.exactifier.stockPreserved_valid
  currentDirectReturnCompatible_valid := by
    intro x
    exact
      ⟨data.currentCarrier.reverse_involutive x,
        data.currentCarrier.stock_reverse x⟩
  relabelingEquivariant_valid := data.exactifier.relabelingEquivariant_valid
  localLosslessExactification_valid := data.exactifier.localLossless_valid
  visiblePrimitiveReadoutAutonomous_valid := by
    intro role
    exact (data.quotient role).autonomousReadout_valid
  returnedDefectActsAsVisibleResidual_valid :=
    data.exactifier.returnedDefectVisibleResidual_valid

/-- Forget the exactifier and slot-count bookkeeping and read the smaller
selected-anchor transport layer that already suffices for the transport side
of origin closure. -/
def toOriginReadoutTransport
    {Index Time Carrier Law : Type}
    (data : ConstructiveCurrentLaw Index Time Carrier Law) :
    OriginReadoutTransport data.toMicroscopicClosureLaw :=
  OriginReadoutTransport.ofParts
    { currentCarrier := data.currentCarrier
      Leg := data.Leg
      current := data.current
      visible := data.visible
      quotient := data.quotient }
    data.closureTransport

/-- Forget the common selected-cut closure transport and read the smaller
constructive anchor-side current law. -/
def toConstructiveAnchorCurrentLaw
    {Index Time Carrier Law : Type}
    (data : ConstructiveCurrentLaw Index Time Carrier Law) :
    ConstructiveAnchorCurrentLaw Index Time Carrier Law where
  toCurrentAnchor := data.toCurrentAnchor
  firstStableBulkEventHasFourLegs := data.firstStableBulkEventHasFourLegs
  sixPairSlots := data.sixPairSlots
  exactifier := data.exactifier
  firstStableBulkEventHasFourLegs_valid :=
    data.firstStableBulkEventHasFourLegs_valid
  sixPairSlots_valid := data.sixPairSlots_valid

/-- The constructive current law already realizes the selected-anchor current
target for its proposition-level microscopic law. -/
theorem originReadoutAnchorTarget
    {Index Time Carrier Law : Type}
    (data : ConstructiveCurrentLaw Index Time Carrier Law) :
    OriginReadoutAnchorTarget data.toMicroscopicClosureLaw := by
  exact data.toConstructiveAnchorCurrentLaw.originReadoutAnchorTarget

/-- The constructive current law already realizes the selected-cut closure
transport target for its proposition-level microscopic law. -/
theorem originReadoutClosureTarget
    {Index Time Carrier Law : Type}
    (data : ConstructiveCurrentLaw Index Time Carrier Law) :
    OriginReadoutClosureTarget data.toMicroscopicClosureLaw := by
  exact data.toOriginReadoutTransport.closureTarget

/-- The constructive current law already realizes the selected-anchor
transport target for its proposition-level microscopic law. -/
theorem originReadoutTransportTarget
    {Index Time Carrier Law : Type}
    (data : ConstructiveCurrentLaw Index Time Carrier Law) :
    OriginReadoutTransportTarget data.toMicroscopicClosureLaw := by
  exact ⟨data.toOriginReadoutTransport⟩

/-- The constructive current law already realizes the smaller exact
anchor-current target for its proposition-level microscopic law. -/
theorem anchorCurrentTarget
    {Index Time Carrier Law : Type}
    (data : ConstructiveCurrentLaw Index Time Carrier Law) :
    ConstructiveAnchorCurrentTarget data.toMicroscopicClosureLaw := by
  exact data.toConstructiveAnchorCurrentLaw.target

end ConstructiveCurrentLaw

/-- Exact law-level constructive current target above one proposition-level
microscopic closure law. It asks only that the law admit one constructive
current realization on the same selected datum. -/
def ConstructiveCurrentTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) : Prop :=
  ∃ data : ConstructiveCurrentLaw Index Time Carrier Law,
    data.toMicroscopicClosureLaw = law

/-- Exact law-level grammar/intrinsicity target above one proposition-level
microscopic closure law. It asks only that the law admit the common grammar
and bundle-intrinsicity clauses on the same selected datum. -/
def ConstructiveMicroscopicClausesTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) : Prop :=
  Nonempty (ConstructiveMicroscopicClauses law)

namespace MicroscopicClosureLaw

/-- Law-native common Part IV grammar read directly from the public physical
principle carried by a microscopic closure law. This is not extra detached
current-side structure: it is the public temporal/coherent realization law
compressed into the clause format expected by the detached constructive lane.
-/
def lawNativeCommonGrammar
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) :
    CommonPartIVGrammar where
  hiddenCoherentLaw := law.physicalPrinciple.sameCoherentBundle
  residualReturnFieldOnSelectedCut :=
    law.physicalPrinciple.residualReturn.residualLocalizesOnUniqueInterface ∧
      law.physicalPrinciple.residualReturn.selectedLawObtainedByResidualElimination
  selectedVisibleLawPhysicallyRealized :=
    law.physicalPrinciple.observableDynamicsExactlySelectedLaw
  onlyReturnActsOnVisibleBundle :=
    law.physicalPrinciple.residualReturn.onlyReturnActs
  characteristicEndpointReduction :=
    law.physicalPrinciple.noExogenousConstitutiveCompletion ∧
      law.physicalPrinciple.apparentConstitutiveTermsAreReturnedResidual
  canonicalSectorGeneration := IsCanonicalLogicalProfile [3, 2, 1]
  symmetryRigidMinimalClosure :=
    law.physicalPrinciple.intrinsicallyClosedOnLeastMotionCut
  carrierLevelPhysicalLaw :=
    law.physicalPrinciple.observableDynamicsExactlySelectedLaw ∧
      law.physicalPrinciple.noExogenousConstitutiveCompletion

/-- The public physical principle carried by a microscopic closure law already
supplies the constructive grammar/intrinsicity clauses needed by the detached
origin-readout lane. The remaining detached seam is therefore current-side,
not grammar-side. -/
def lawNativeConstructiveMicroscopicClauses
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) :
    ConstructiveMicroscopicClauses law where
  commonGrammar := law.lawNativeCommonGrammar
  bundleArisesIntrinsicallyOnLeastMotionCut :=
    law.physicalPrinciple.sameCoherentBundle
  noCarrierWiseVisibilityHypotheses :=
    law.physicalPrinciple.noExogenousConstitutiveCompletion
  hiddenCoherentLaw_valid := law.physicalPrinciple.sameCoherentBundle_valid
  residualReturnFieldOnSelectedCut_valid := by
    exact
      ⟨law.physicalPrinciple.residualReturn.residualLocalizesOnUniqueInterface_valid,
        law.physicalPrinciple.residualReturn.selectedLawObtainedByResidualElimination_valid⟩
  selectedVisibleLawPhysicallyRealized_valid :=
    law.physicalPrinciple.observableDynamicsExactlySelectedLaw_valid
  onlyReturnActsOnVisibleBundle_valid :=
    law.physicalPrinciple.residualReturn.onlyReturnActs_valid
  characteristicEndpointReduction_valid := by
    exact
      ⟨law.physicalPrinciple.noExogenousConstitutiveCompletion_valid,
        law.physicalPrinciple.apparentConstitutiveTermsAreReturnedResidual_valid⟩
  canonicalSectorGeneration_valid := forced_intrinsic_channel_profile.2
  symmetryRigidMinimalClosure_valid :=
    law.physicalPrinciple.intrinsicallyClosedOnLeastMotionCut_valid
  carrierLevelPhysicalLaw_valid := by
    exact
      ⟨law.physicalPrinciple.observableDynamicsExactlySelectedLaw_valid,
        law.physicalPrinciple.noExogenousConstitutiveCompletion_valid⟩
  bundleArisesIntrinsicallyOnLeastMotionCut_valid :=
    law.physicalPrinciple.sameCoherentBundle_valid
  noCarrierWiseVisibilityHypotheses_valid :=
    law.physicalPrinciple.noExogenousConstitutiveCompletion_valid

/-- The detached constructive clause target is already forced by the public
physical principle carried on the microscopic law itself. -/
theorem constructiveMicroscopicClausesTargetOfPhysicalPrinciple
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) :
    ConstructiveMicroscopicClausesTarget law := by
  exact ⟨law.lawNativeConstructiveMicroscopicClauses⟩

end MicroscopicClosureLaw

namespace ConstructiveCurrentLaw

/-- Any actual constructive current law immediately realizes the exact
law-level constructive current target for its proposition-level law. -/
theorem target
    {Index Time Carrier Law : Type}
    (data : ConstructiveCurrentLaw Index Time Carrier Law) :
    ConstructiveCurrentTarget data.toMicroscopicClosureLaw := by
  exact ⟨data, rfl⟩

end ConstructiveCurrentLaw

namespace ConstructiveMicroscopicClauses

/-- Read the common grammar and bundle-intrinsicity clauses as the smaller
origin-readout clauses above the same microscopic law. -/
def toOriginReadoutClauses
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : ConstructiveMicroscopicClauses law) :
    OriginReadoutClauses law where
  commonGrammar := data.commonGrammar
  bundleArisesIntrinsicallyOnLeastMotionCut :=
    data.bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses :=
    data.noCarrierWiseVisibilityHypotheses
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

/-- Any actual constructive grammar/intrinsicity package already realizes the
origin-readout clauses target for the same microscopic law. -/
theorem originReadoutClausesTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : ConstructiveMicroscopicClauses law) :
    OriginReadoutClausesTarget law := by
  exact ⟨data.toOriginReadoutClauses⟩

/-- Any actual constructive grammar/intrinsicity package immediately realizes
the corresponding law-level clauses target. -/
theorem target
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : ConstructiveMicroscopicClauses law) :
    ConstructiveMicroscopicClausesTarget law := by
  exact ⟨data⟩

end ConstructiveMicroscopicClauses

namespace ConstructiveMicroscopicLaw

/-- Forget the grammar/intrinsicity side and read the smaller constructive
current law. -/
def toConstructiveCurrentLaw
    {Index Time Carrier Law : Type}
    (data : ConstructiveMicroscopicLaw Index Time Carrier Law) :
    ConstructiveCurrentLaw Index Time Carrier Law where
  toAnchoredCurrentTransport := data.toAnchoredCurrentTransport
  firstStableBulkEventHasFourLegs := data.firstStableBulkEventHasFourLegs
  sixPairSlots := data.sixPairSlots
  exactifier := data.exactifier
  firstStableBulkEventHasFourLegs_valid :=
    data.firstStableBulkEventHasFourLegs_valid
  sixPairSlots_valid := data.sixPairSlots_valid

/-- Forget the constructive current side and read only the common grammar and
bundle-intrinsicity clauses above the induced microscopic law. -/
def toConstructiveMicroscopicClauses
    {Index Time Carrier Law : Type}
    (data : ConstructiveMicroscopicLaw Index Time Carrier Law) :
    ConstructiveMicroscopicClauses data.toConstructiveCurrentLaw.toMicroscopicClosureLaw where
  commonGrammar := data.commonGrammar
  bundleArisesIntrinsicallyOnLeastMotionCut :=
    data.bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses :=
    data.noCarrierWiseVisibilityHypotheses
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

/-- Read the proposition-level microscopic closure law from the constructive
microscopic law. -/
def toMicroscopicClosureLaw
    {Index Time Carrier Law : Type}
    (data : ConstructiveMicroscopicLaw Index Time Carrier Law) :
    MicroscopicClosureLaw Index Time Carrier Law where
  bridge := data.bridge
  physicalPrinciple := data.physicalPrinciple
  sameSelectedLawAsBridge := data.sameSelectedLawAsBridge
  hiddenExactExchangeCurrent :=
    Nonempty (PairExchangeCurrent data.currentCarrier data.Leg)
  currentLivesOnOrientedPairSlots :=
    ∀ a b : data.Leg,
      data.current.value b a =
        data.currentCarrier.reverse (data.current.value a b)
  firstStableBulkEventCarriesSixSlotCurrent :=
    data.firstStableBulkEventHasFourLegs ∧ data.sixPairSlots
  currentStockConserved := data.exactifier.stockPreserved
  currentDirectReturnCompatible := data.toCurrentAnchor.currentDirectReturnCompatible
  relabelingEquivariant := data.exactifier.relabelingEquivariant
  localLosslessExactification := data.exactifier.localLossless
  visiblePrimitiveReadoutAutonomous :=
    data.toCurrentAnchor.visiblePrimitiveReadoutAutonomous
  returnedDefectActsAsVisibleResidual :=
    data.exactifier.returnedDefectVisibleResidual
  hiddenExactExchangeCurrent_valid := ⟨data.current⟩
  currentLivesOnOrientedPairSlots_valid := data.current.swap_reverse
  firstStableBulkEventCarriesSixSlotCurrent_valid :=
    ⟨data.firstStableBulkEventHasFourLegs_valid, data.sixPairSlots_valid⟩
  currentStockConserved_valid := data.exactifier.stockPreserved_valid
  currentDirectReturnCompatible_valid := by
    intro x
    exact
      ⟨data.currentCarrier.reverse_involutive x,
        data.currentCarrier.stock_reverse x⟩
  relabelingEquivariant_valid := data.exactifier.relabelingEquivariant_valid
  localLosslessExactification_valid := data.exactifier.localLossless_valid
  visiblePrimitiveReadoutAutonomous_valid := by
    intro role
    exact (data.quotient role).autonomousReadout_valid
  returnedDefectActsAsVisibleResidual_valid :=
    data.exactifier.returnedDefectVisibleResidual_valid

/-- Forget the exactifier and slot-count bookkeeping and read the smaller
selected-anchor readout layer that already suffices for origin closure. -/
def toOriginReadoutLaw
    {Index Time Carrier Law : Type}
    (data : ConstructiveMicroscopicLaw Index Time Carrier Law) :
    OriginReadoutLaw data.toMicroscopicClosureLaw :=
  OriginReadoutLaw.ofParts
    data.toConstructiveCurrentLaw.toOriginReadoutTransport
    data.toConstructiveMicroscopicClauses.toOriginReadoutClauses

/-- Surface theorem for the smaller constructive microscopic law. The selected
anchor already carries exact visibility, forced continuum closure, common
selected-cut transport, and the bundle-intrinsicity clauses needed for origin
closure. -/
theorem surface
    {Index Time Carrier Law : Type}
    (data : ConstructiveMicroscopicLaw Index Time Carrier Law) :
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
            observer.continuumClass) ∧
      data.bundleArisesIntrinsicallyOnLeastMotionCut ∧
      data.noCarrierWiseVisibilityHypotheses := by
  obtain ⟨hcurrent, hdirret, haut, hmin, hexact, hforced, htransport⟩ :=
    data.toAnchoredCurrentTransport.surface
  exact
    ⟨hcurrent,
      hdirret,
      haut,
      hmin,
      hexact,
      hforced,
      htransport,
      data.bundleArisesIntrinsicallyOnLeastMotionCut_valid,
      data.noCarrierWiseVisibilityHypotheses_valid⟩

/-- The selected-bundle/readout witness forced by the smaller constructive
microscopic law. -/
def toOriginClosureWitness
    {Index Time Carrier Law : Type}
    (data : ConstructiveMicroscopicLaw Index Time Carrier Law) :
    OriginClosureWitness data.toMicroscopicClosureLaw :=
  data.toOriginReadoutLaw.toOriginClosureWitness

/-- The smaller constructive microscopic law already realizes the exact
selected-anchor target for its proposition-level microscopic law. -/
theorem originReadoutAnchorTarget
    {Index Time Carrier Law : Type}
    (data : ConstructiveMicroscopicLaw Index Time Carrier Law) :
    OriginReadoutAnchorTarget data.toMicroscopicClosureLaw := by
  exact data.toConstructiveCurrentLaw.originReadoutAnchorTarget

/-- The smaller constructive microscopic law already realizes the exact
selected-cut closure-transport target for its proposition-level microscopic
law. -/
theorem originReadoutClosureTarget
    {Index Time Carrier Law : Type}
    (data : ConstructiveMicroscopicLaw Index Time Carrier Law) :
    OriginReadoutClosureTarget data.toMicroscopicClosureLaw := by
  exact data.toConstructiveCurrentLaw.originReadoutClosureTarget

/-- The smaller constructive microscopic law already realizes the exact
origin-readout descent target for its proposition-level microscopic law. -/
theorem originReadoutTransportTarget
    {Index Time Carrier Law : Type}
    (data : ConstructiveMicroscopicLaw Index Time Carrier Law) :
    OriginReadoutTransportTarget data.toMicroscopicClosureLaw := by
  exact data.toConstructiveCurrentLaw.originReadoutTransportTarget

/-- The smaller constructive microscopic law already realizes the exact
common-grammar/intrinsicity target for its proposition-level microscopic law.
-/
theorem originReadoutClausesTarget
    {Index Time Carrier Law : Type}
    (data : ConstructiveMicroscopicLaw Index Time Carrier Law) :
    OriginReadoutClausesTarget data.toMicroscopicClosureLaw := by
  exact data.toConstructiveMicroscopicClauses.originReadoutClausesTarget

/-- The smaller constructive microscopic law already realizes the exact
constructive current target for its proposition-level microscopic law. -/
theorem currentTarget
    {Index Time Carrier Law : Type}
    (data : ConstructiveMicroscopicLaw Index Time Carrier Law) :
    ConstructiveCurrentTarget data.toMicroscopicClosureLaw := by
  exact data.toConstructiveCurrentLaw.target

/-- The smaller constructive microscopic law already realizes the smaller
exact anchor-current target for its proposition-level microscopic law. -/
theorem anchorCurrentTarget
    {Index Time Carrier Law : Type}
    (data : ConstructiveMicroscopicLaw Index Time Carrier Law) :
    ConstructiveAnchorCurrentTarget data.toMicroscopicClosureLaw := by
  exact data.toConstructiveCurrentLaw.anchorCurrentTarget

/-- The smaller constructive microscopic law already realizes the exact
grammar/intrinsicity target for its proposition-level microscopic law. -/
theorem clausesTarget
    {Index Time Carrier Law : Type}
    (data : ConstructiveMicroscopicLaw Index Time Carrier Law) :
    ConstructiveMicroscopicClausesTarget data.toMicroscopicClosureLaw := by
  exact data.toConstructiveMicroscopicClauses.target

/-- The smaller constructive microscopic law already realizes the exact
origin-readout descent target for its proposition-level microscopic law. -/
theorem originReadoutTarget
    {Index Time Carrier Law : Type}
    (data : ConstructiveMicroscopicLaw Index Time Carrier Law) :
    OriginReadoutTarget data.toMicroscopicClosureLaw := by
  exact
    data.toMicroscopicClosureLaw.originReadoutTargetOfParts
      data.originReadoutTransportTarget
      data.originReadoutClausesTarget

/-- The self-contained constructive microscopic law determines the detached
local-event object directly, with the selected-bundle/readout witness read from
the smaller origin layer and the exactifier/slot data retained locally. -/
def toLocalEventObject
    {Index Time Carrier Law : Type}
    (data : ConstructiveMicroscopicLaw Index Time Carrier Law) :
    LocalEventObject Index Time Carrier Law where
  bridge := data.bridge
  physicalPrinciple := data.physicalPrinciple
  sameSelectedLawAsBridge := data.sameSelectedLawAsBridge
  commonGrammar := data.commonGrammar
  currentCarrier := data.currentCarrier
  Leg := data.Leg
  firstStableBulkEventHasFourLegs := data.firstStableBulkEventHasFourLegs
  sixPairSlots := data.sixPairSlots
  current := data.current
  exactifier := data.exactifier
  visible := data.visible
  quotient := data.quotient
  selectedObservedBundle := data.toOriginClosureWitness.selectedObservedBundle
  sectors := data.toOriginClosureWitness.sectors
  bundlePhysicallyRealized := data.toOriginClosureWitness.bundlePhysicallyRealized
  bundleSharedByAllCarriers :=
    data.toOriginClosureWitness.bundleSharedByAllCarriers
  sameSelectedEffectiveLawOnEachCarrier :=
    data.toOriginClosureWitness.sameSelectedEffectiveLawOnEachCarrier
  carrierLevelIdentificationOnlyFinalStep :=
    data.toOriginClosureWitness.carrierLevelIdentificationOnlyFinalStep
  readsRoleOnSelectedBundle :=
    data.toOriginClosureWitness.readsRoleOnSelectedBundle
  readsRoleOnSelectedBundle_sameSelection :=
    data.toOriginClosureWitness.readsRoleOnSelectedBundle_sameSelection
  sameContinuumClosureClassOnSelectedBundle :=
    data.toOriginClosureWitness.sameContinuumClosureClassOnSelectedBundle
  bundleArisesIntrinsicallyOnLeastMotionCut :=
    data.bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses :=
    data.noCarrierWiseVisibilityHypotheses
  selectedObservedBundle_valid :=
    data.toOriginClosureWitness.selectedObservedBundle_valid
  phaseCarrierSector_valid := data.toOriginClosureWitness.phaseCarrierSector_valid
  waveCarrierSector_valid := data.toOriginClosureWitness.waveCarrierSector_valid
  kineticCarrierSector_valid :=
    data.toOriginClosureWitness.kineticCarrierSector_valid
  gaugeCarrierSector_valid := data.toOriginClosureWitness.gaugeCarrierSector_valid
  geometricCarrierSector_valid :=
    data.toOriginClosureWitness.geometricCarrierSector_valid
  bundlePhysicallyRealized_valid :=
    data.toOriginClosureWitness.bundlePhysicallyRealized_valid
  bundleSharedByAllCarriers_valid :=
    data.toOriginClosureWitness.bundleSharedByAllCarriers_valid
  sameSelectedEffectiveLawOnEachCarrier_valid :=
    data.toOriginClosureWitness.sameSelectedEffectiveLawOnEachCarrier_valid
  carrierLevelIdentificationOnlyFinalStep_valid :=
    data.toOriginClosureWitness.carrierLevelIdentificationOnlyFinalStep_valid
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

/-- The smaller constructive microscopic law already proves the previously
target-level origin-closure statement. -/
theorem originClosureTarget
    {Index Time Carrier Law : Type}
    (data : ConstructiveMicroscopicLaw Index Time Carrier Law) :
    OriginClosureTarget data.toMicroscopicClosureLaw := by
  exact
    data.toMicroscopicClosureLaw.originClosureTargetOfReadout
      data.originReadoutTarget

/-- The detached selected-bundle forcing surface already follows from the
smaller constructive microscopic law with no extra origin witness hypothesis.
-/
theorem originTargetSurface
    {Index Time Carrier Law : Type}
    (data : ConstructiveMicroscopicLaw Index Time Carrier Law) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      realized_generator_carries_bedrock_law data.bridge.generator ∧
      AutonomousHorizon
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator ∧
      horizonFiberInvariant
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator := by
  exact
    data.toMicroscopicClosureLaw.originReadoutTargetSurface
      data.originReadoutTarget

end ConstructiveMicroscopicLaw

/-- Exact law-level constructive target above one proposition-level
microscopic closure law. It asks only that the law admit one self-contained
constructive microscopic realization on the same selected datum. -/
def ConstructiveMicroscopicTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) : Prop :=
  ∃ data : ConstructiveMicroscopicLaw Index Time Carrier Law,
    data.toMicroscopicClosureLaw = law

namespace ConstructiveMicroscopicLaw

/-- Any actual constructive microscopic law immediately realizes the exact
law-level constructive target for its proposition-level law. -/
theorem target
    {Index Time Carrier Law : Type}
    (data : ConstructiveMicroscopicLaw Index Time Carrier Law) :
    ConstructiveMicroscopicTarget data.toMicroscopicClosureLaw := by
  exact ⟨data, rfl⟩

end ConstructiveMicroscopicLaw

/-- Manuscript-facing name for the first theorem-bearing detached microscopic
law. A closure-stable local event now carries its own selected anchor, visible
origin, and coherent selected-cut closure transport on the same selected datum,
instead of leaving that realization implicit in later witness packages. -/
abbrev CanonicalOriginLaw (Index Time Carrier Law : Type) :=
  ConstructiveMicroscopicLaw Index Time Carrier Law

namespace CanonicalOriginLaw

/-- The canonical-origin detached law already realizes the exact law-level
constructive target for its underlying proposition-level microscopic law. -/
theorem target
    {Index Time Carrier Law : Type}
    (data : CanonicalOriginLaw Index Time Carrier Law) :
    ConstructiveMicroscopicTarget data.toMicroscopicClosureLaw := by
  exact ConstructiveMicroscopicLaw.target data

/-- The canonical-origin detached law already forces origin closure for its
underlying proposition-level microscopic law. -/
theorem originClosureTarget
    {Index Time Carrier Law : Type}
    (data : CanonicalOriginLaw Index Time Carrier Law) :
    OriginClosureTarget data.toMicroscopicClosureLaw := by
  exact ConstructiveMicroscopicLaw.originClosureTarget data

/-- The detached selected-bundle forcing surface already follows from the
canonical-origin detached law. -/
theorem canonicalOriginSurface
    {Index Time Carrier Law : Type}
    (data : CanonicalOriginLaw Index Time Carrier Law) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      realized_generator_carries_bedrock_law data.bridge.generator ∧
      AutonomousHorizon
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator ∧
      horizonFiberInvariant
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator := by
  exact ConstructiveMicroscopicLaw.originTargetSurface data

/-- Surface theorem for the canonical-origin detached law. It already supplies
its own exact law-level realization, origin closure, and detached selected-
bundle forcing surface on the same selected datum. -/
theorem surface
    {Index Time Carrier Law : Type}
    (data : CanonicalOriginLaw Index Time Carrier Law) :
    ConstructiveMicroscopicTarget data.toMicroscopicClosureLaw ∧
      OriginClosureTarget data.toMicroscopicClosureLaw ∧
      Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      realized_generator_carries_bedrock_law data.bridge.generator ∧
      AutonomousHorizon
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator ∧
      horizonFiberInvariant
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator := by
  exact
    ⟨data.target,
      data.originClosureTarget,
      data.canonicalOriginSurface.1,
      data.canonicalOriginSurface.2.1,
      data.canonicalOriginSurface.2.2.1,
      data.canonicalOriginSurface.2.2.2⟩

end CanonicalOriginLaw

namespace MicroscopicClosureLaw

/-- The exact constructive anchor-current target together with the exact
selected-cut closure target already yield the constructive current target for
the same proposition-level microscopic law. -/
theorem constructiveCurrentTargetOfConstructiveAnchorCurrentTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hanchor : ConstructiveAnchorCurrentTarget law)
    (hclosure : OriginReadoutClosureTarget law) :
    ConstructiveCurrentTarget law := by
  rcases hanchor with ⟨data, rfl⟩
  rcases hclosure with ⟨closureTransport⟩
  exact ⟨data.toConstructiveCurrentLaw closureTransport, rfl⟩

/-- The exact law-level constructive current target already yields the smaller
constructive anchor-current target. -/
theorem constructiveAnchorCurrentTargetOfConstructiveCurrentTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hcurrent : ConstructiveCurrentTarget law) :
    ConstructiveAnchorCurrentTarget law := by
  rcases hcurrent with ⟨data, rfl⟩
  exact data.anchorCurrentTarget

/-- The exact constructive current target already yields the selected-anchor
transport target for the same proposition-level microscopic law. -/
theorem originReadoutTransportTargetOfConstructiveCurrentTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hcurrent : ConstructiveCurrentTarget law) :
    OriginReadoutTransportTarget law := by
  rcases hcurrent with ⟨data, rfl⟩
  exact data.originReadoutTransportTarget

/-- The exact grammar/intrinsicity target already yields the origin-readout
clauses target for the same proposition-level microscopic law. -/
theorem originReadoutClausesTargetOfConstructiveMicroscopicClausesTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hclauses : ConstructiveMicroscopicClausesTarget law) :
    OriginReadoutClausesTarget law := by
  rcases hclauses with ⟨clauses⟩
  exact clauses.originReadoutClausesTarget

/-- The exact constructive anchor-current target already yields the smaller
selected-anchor target for the same proposition-level microscopic law. -/
theorem originReadoutAnchorTargetOfConstructiveAnchorCurrentTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hanchor : ConstructiveAnchorCurrentTarget law) :
    OriginReadoutAnchorTarget law := by
  rcases hanchor with ⟨data, rfl⟩
  exact data.originReadoutAnchorTarget

/-- The exact constructive anchor-current target together with the exact
selected-cut closure target already yield the selected-anchor transport target
for the same proposition-level microscopic law. -/
theorem originReadoutTransportTargetOfConstructiveAnchorCurrentTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hanchor : ConstructiveAnchorCurrentTarget law)
    (hclosure : OriginReadoutClosureTarget law) :
    OriginReadoutTransportTarget law := by
  exact
    law.originReadoutTransportTargetOfParts
      (law.originReadoutAnchorTargetOfConstructiveAnchorCurrentTarget hanchor)
      hclosure

/-- The exact constructive anchor-current target together with the exact
selected-cut closure target and the exact grammar/intrinsicity target already
yield the full origin-readout target. -/
theorem originReadoutTargetOfConstructiveAnchorCurrentTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hanchor : ConstructiveAnchorCurrentTarget law)
    (hclosure : OriginReadoutClosureTarget law)
    (hclauses : ConstructiveMicroscopicClausesTarget law) :
    OriginReadoutTarget law := by
  exact
    law.originReadoutTargetOfParts
      (law.originReadoutTransportTargetOfConstructiveAnchorCurrentTarget
        hanchor hclosure)
      (law.originReadoutClausesTargetOfConstructiveMicroscopicClausesTarget
        hclauses)

/-- The exact constructive anchor-current target together with the exact
selected-cut closure target and the exact grammar/intrinsicity target already
yield origin closure. -/
theorem originClosureTargetOfConstructiveAnchorCurrentTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hanchor : ConstructiveAnchorCurrentTarget law)
    (hclosure : OriginReadoutClosureTarget law)
    (hclauses : ConstructiveMicroscopicClausesTarget law) :
    OriginClosureTarget law := by
  exact
    law.originClosureTargetOfReadout
      (law.originReadoutTargetOfConstructiveAnchorCurrentTarget
        hanchor hclosure hclauses)

/-- The detached selected-bundle forcing surface already follows from the
exact constructive anchor-current target together with the exact
selected-cut closure target and the exact grammar/intrinsicity target. -/
theorem originTargetSurfaceOfConstructiveAnchorCurrentTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hanchor : ConstructiveAnchorCurrentTarget law)
    (hclosure : OriginReadoutClosureTarget law)
    (hclauses : ConstructiveMicroscopicClausesTarget law) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      realized_generator_carries_bedrock_law law.bridge.generator ∧
      AutonomousHorizon
        law.bridge.selectedBridge.observer.selection.realization.tower
        law.bridge.selectedBridge.observer.selection.horizon
        law.bridge.generator ∧
      horizonFiberInvariant
        law.bridge.selectedBridge.observer.selection.realization.tower
        law.bridge.selectedBridge.observer.selection.horizon
        law.bridge.generator := by
  exact
    law.originReadoutTargetSurface
      (law.originReadoutTargetOfConstructiveAnchorCurrentTarget
        hanchor hclosure hclauses)

/-- The exact constructive current target together with the exact
grammar/intrinsicity target already yield the origin-readout target. -/
theorem originReadoutTargetOfConstructiveParts
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hcurrent : ConstructiveCurrentTarget law)
    (hclauses : ConstructiveMicroscopicClausesTarget law) :
    OriginReadoutTarget law := by
  exact
    law.originReadoutTargetOfParts
      (law.originReadoutTransportTargetOfConstructiveCurrentTarget hcurrent)
      (law.originReadoutClausesTargetOfConstructiveMicroscopicClausesTarget
        hclauses)

/-- The exact constructive current target together with the exact
grammar/intrinsicity target already yield origin closure. -/
theorem originClosureTargetOfConstructiveParts
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hcurrent : ConstructiveCurrentTarget law)
    (hclauses : ConstructiveMicroscopicClausesTarget law) :
    OriginClosureTarget law := by
  exact
    law.originClosureTargetOfReadout
      (law.originReadoutTargetOfConstructiveParts hcurrent hclauses)

/-- The detached selected-bundle forcing surface already follows from the
exact constructive current target together with the exact
grammar/intrinsicity target. -/
theorem originTargetSurfaceOfConstructiveParts
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hcurrent : ConstructiveCurrentTarget law)
    (hclauses : ConstructiveMicroscopicClausesTarget law) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      realized_generator_carries_bedrock_law law.bridge.generator ∧
      AutonomousHorizon
        law.bridge.selectedBridge.observer.selection.realization.tower
        law.bridge.selectedBridge.observer.selection.horizon
        law.bridge.generator ∧
      horizonFiberInvariant
        law.bridge.selectedBridge.observer.selection.realization.tower
        law.bridge.selectedBridge.observer.selection.horizon
        law.bridge.generator := by
  exact
    law.originReadoutTargetSurface
      (law.originReadoutTargetOfConstructiveParts hcurrent hclauses)

/-- Once the constructive current target is met, the constructive clause layer
is already supplied by the public physical principle carried on the same
microscopic law. No separate detached clause datum is needed. -/
theorem originReadoutTargetOfConstructiveCurrentTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hcurrent : ConstructiveCurrentTarget law) :
    OriginReadoutTarget law := by
  exact
    law.originReadoutTargetOfConstructiveParts
      hcurrent
      law.constructiveMicroscopicClausesTargetOfPhysicalPrinciple

/-- Once the constructive current target is met, origin closure already
follows from the public physical principle on that same microscopic law. -/
theorem originClosureTargetOfConstructiveCurrentTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hcurrent : ConstructiveCurrentTarget law) :
    OriginClosureTarget law := by
  exact
    law.originClosureTargetOfConstructiveParts
      hcurrent
      law.constructiveMicroscopicClausesTargetOfPhysicalPrinciple

/-- Once the constructive current target is met, the detached selected-bundle
forcing surface already follows; the grammar/intrinsicity side is supplied by
the public physical principle itself. -/
theorem originTargetSurfaceOfConstructiveCurrentTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hcurrent : ConstructiveCurrentTarget law) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      realized_generator_carries_bedrock_law law.bridge.generator ∧
      AutonomousHorizon
        law.bridge.selectedBridge.observer.selection.realization.tower
        law.bridge.selectedBridge.observer.selection.horizon
        law.bridge.generator ∧
      horizonFiberInvariant
        law.bridge.selectedBridge.observer.selection.realization.tower
        law.bridge.selectedBridge.observer.selection.horizon
        law.bridge.generator := by
  exact
    law.originTargetSurfaceOfConstructiveParts
      hcurrent
      law.constructiveMicroscopicClausesTargetOfPhysicalPrinciple

/-- The exact law-level constructive microscopic target is already recovered
from the smaller constructive current target together with the exact
grammar/intrinsicity target. -/
theorem constructiveMicroscopicTargetOfParts
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hcurrent : ConstructiveCurrentTarget law)
    (hclauses : ConstructiveMicroscopicClausesTarget law) :
    ConstructiveMicroscopicTarget law := by
  rcases hcurrent with ⟨current, hcurrentLaw⟩
  rcases hclauses with ⟨clauses⟩
  subst hcurrentLaw
  exact
    ⟨{ toAnchoredCurrentTransport := current.toAnchoredCurrentTransport
       commonGrammar := clauses.commonGrammar
       firstStableBulkEventHasFourLegs := current.firstStableBulkEventHasFourLegs
       sixPairSlots := current.sixPairSlots
       exactifier := current.exactifier
       bundleArisesIntrinsicallyOnLeastMotionCut :=
         clauses.bundleArisesIntrinsicallyOnLeastMotionCut
       noCarrierWiseVisibilityHypotheses :=
         clauses.noCarrierWiseVisibilityHypotheses
       firstStableBulkEventHasFourLegs_valid :=
         current.firstStableBulkEventHasFourLegs_valid
       sixPairSlots_valid := current.sixPairSlots_valid
       hiddenCoherentLaw_valid := clauses.hiddenCoherentLaw_valid
       residualReturnFieldOnSelectedCut_valid :=
         clauses.residualReturnFieldOnSelectedCut_valid
       selectedVisibleLawPhysicallyRealized_valid :=
         clauses.selectedVisibleLawPhysicallyRealized_valid
       onlyReturnActsOnVisibleBundle_valid :=
         clauses.onlyReturnActsOnVisibleBundle_valid
       characteristicEndpointReduction_valid :=
         clauses.characteristicEndpointReduction_valid
       canonicalSectorGeneration_valid :=
         clauses.canonicalSectorGeneration_valid
       symmetryRigidMinimalClosure_valid :=
         clauses.symmetryRigidMinimalClosure_valid
       carrierLevelPhysicalLaw_valid :=
         clauses.carrierLevelPhysicalLaw_valid
       bundleArisesIntrinsicallyOnLeastMotionCut_valid :=
         clauses.bundleArisesIntrinsicallyOnLeastMotionCut_valid
       noCarrierWiseVisibilityHypotheses_valid :=
         clauses.noCarrierWiseVisibilityHypotheses_valid }, rfl⟩

/-- Once the constructive current target is met, the bundled constructive
microscopic target is recovered without any extra detached clause package. -/
theorem constructiveMicroscopicTargetOfConstructiveCurrentTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hcurrent : ConstructiveCurrentTarget law) :
    ConstructiveMicroscopicTarget law := by
  exact
    law.constructiveMicroscopicTargetOfParts
      hcurrent
      law.constructiveMicroscopicClausesTargetOfPhysicalPrinciple

/-- The exact constructive anchor-current target together with the exact
selected-cut closure target and the exact grammar/intrinsicity target already
recover the bundled constructive microscopic target. -/
theorem constructiveMicroscopicTargetOfConstructiveAnchorCurrentTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hanchor : ConstructiveAnchorCurrentTarget law)
    (hclosure : OriginReadoutClosureTarget law)
    (hclauses : ConstructiveMicroscopicClausesTarget law) :
    ConstructiveMicroscopicTarget law := by
  exact
    law.constructiveMicroscopicTargetOfParts
      (law.constructiveCurrentTargetOfConstructiveAnchorCurrentTarget
        hanchor hclosure)
      hclauses

/-- Once the constructive anchor-current target and selected-cut closure
transport are met, the bundled constructive microscopic target is recovered;
the grammar/intrinsicity side is again supplied by the public physical
principle on the same microscopic law. -/
theorem constructiveMicroscopicTargetOfConstructiveAnchorCurrentTargetAndClosure
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hanchor : ConstructiveAnchorCurrentTarget law)
    (hclosure : OriginReadoutClosureTarget law) :
    ConstructiveMicroscopicTarget law := by
  exact
    law.constructiveMicroscopicTargetOfConstructiveAnchorCurrentTarget
      hanchor
      hclosure
      law.constructiveMicroscopicClausesTargetOfPhysicalPrinciple

/-- The exact law-level constructive microscopic target already yields the
smaller constructive current target. -/
theorem constructiveCurrentTargetOfConstructiveMicroscopicTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hconstructive : ConstructiveMicroscopicTarget law) :
    ConstructiveCurrentTarget law := by
  rcases hconstructive with ⟨data, rfl⟩
  exact data.currentTarget

/-- The exact law-level constructive microscopic target already yields the
smaller constructive anchor-current target. -/
theorem constructiveAnchorCurrentTargetOfConstructiveMicroscopicTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hconstructive : ConstructiveMicroscopicTarget law) :
    ConstructiveAnchorCurrentTarget law := by
  exact
    law.constructiveAnchorCurrentTargetOfConstructiveCurrentTarget
      (law.constructiveCurrentTargetOfConstructiveMicroscopicTarget
        hconstructive)

/-- The exact law-level constructive microscopic target already yields the
smaller grammar/intrinsicity target. -/
theorem constructiveMicroscopicClausesTargetOfConstructiveMicroscopicTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hconstructive : ConstructiveMicroscopicTarget law) :
    ConstructiveMicroscopicClausesTarget law := by
  rcases hconstructive with ⟨data, rfl⟩
  exact data.clausesTarget

/-- The exact law-level constructive microscopic target already yields the
origin-readout target. -/
theorem originReadoutTargetOfConstructiveMicroscopicTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hconstructive : ConstructiveMicroscopicTarget law) :
    OriginReadoutTarget law := by
  exact
    law.originReadoutTargetOfConstructiveParts
      (law.constructiveCurrentTargetOfConstructiveMicroscopicTarget hconstructive)
      (law.constructiveMicroscopicClausesTargetOfConstructiveMicroscopicTarget
        hconstructive)

/-- The exact law-level constructive microscopic target already yields the
origin-closure target. -/
theorem originClosureTargetOfConstructiveMicroscopicTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hconstructive : ConstructiveMicroscopicTarget law) :
    OriginClosureTarget law := by
  exact
    law.originClosureTargetOfConstructiveParts
      (law.constructiveCurrentTargetOfConstructiveMicroscopicTarget hconstructive)
      (law.constructiveMicroscopicClausesTargetOfConstructiveMicroscopicTarget
        hconstructive)

/-- The detached selected-bundle forcing surface already follows from the
exact law-level constructive microscopic target. -/
theorem originTargetSurfaceOfConstructiveMicroscopicTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hconstructive : ConstructiveMicroscopicTarget law) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      realized_generator_carries_bedrock_law law.bridge.generator ∧
      AutonomousHorizon
        law.bridge.selectedBridge.observer.selection.realization.tower
        law.bridge.selectedBridge.observer.selection.horizon
        law.bridge.generator ∧
      horizonFiberInvariant
        law.bridge.selectedBridge.observer.selection.realization.tower
        law.bridge.selectedBridge.observer.selection.horizon
        law.bridge.generator := by
  exact
    law.originTargetSurfaceOfConstructiveParts
      (law.constructiveCurrentTargetOfConstructiveMicroscopicTarget hconstructive)
      (law.constructiveMicroscopicClausesTargetOfConstructiveMicroscopicTarget
        hconstructive)

end MicroscopicClosureLaw

namespace LocalEventExactificationLaw

/-- The stronger local-event exactification law already carries the common
grammar and bundle-intrinsicity clauses needed for the smaller constructive
microscopic layer above its induced microscopic law. -/
def toConstructiveMicroscopicClauses
    {Index Time Carrier Law : Type}
    (data : LocalEventExactificationLaw Index Time Carrier Law) :
    ConstructiveMicroscopicClauses data.toMicroscopicClosureLaw where
  commonGrammar := data.commonGrammar
  bundleArisesIntrinsicallyOnLeastMotionCut :=
    data.bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses :=
    data.noCarrierWiseVisibilityHypotheses
  hiddenCoherentLaw_valid := data.hiddenCoherentLaw_valid
  residualReturnFieldOnSelectedCut_valid :=
    data.residualReturnFieldOnSelectedCut_valid
  selectedVisibleLawPhysicallyRealized_valid :=
    data.selectedVisibleLawPhysicallyRealized_valid
  onlyReturnActsOnVisibleBundle_valid :=
    data.onlyReturnActsOnVisibleBundle_valid
  characteristicEndpointReduction_valid :=
    data.characteristicEndpointReduction_valid
  canonicalSectorGeneration_valid := data.canonicalSectorGeneration_valid
  symmetryRigidMinimalClosure_valid :=
    data.symmetryRigidMinimalClosure_valid
  carrierLevelPhysicalLaw_valid := data.carrierLevelPhysicalLaw_valid
  bundleArisesIntrinsicallyOnLeastMotionCut_valid :=
    data.bundleArisesIntrinsicallyOnLeastMotionCut_valid
  noCarrierWiseVisibilityHypotheses_valid :=
    data.noCarrierWiseVisibilityHypotheses_valid

/-- The stronger local-event exactification law already realizes the exact
grammar/intrinsicity target for the smaller constructive microscopic layer
above its induced microscopic law. -/
theorem constructiveMicroscopicClausesTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventExactificationLaw Index Time Carrier Law) :
    ConstructiveMicroscopicClausesTarget data.toMicroscopicClosureLaw := by
  exact data.toConstructiveMicroscopicClauses.target

/-- Above the stronger local-event exactification law, the remaining
constructive current seam is exactly the constructive anchor-current target.
Once that target is met, the constructive current target follows
immediately. -/
theorem constructiveCurrentTargetOfConstructiveAnchorCurrentTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventExactificationLaw Index Time Carrier Law)
    (hanchor : ConstructiveAnchorCurrentTarget data.toMicroscopicClosureLaw) :
    ConstructiveCurrentTarget data.toMicroscopicClosureLaw := by
  exact
    MicroscopicClosureLaw.constructiveCurrentTargetOfConstructiveAnchorCurrentTarget
      data.toMicroscopicClosureLaw
      hanchor
      data.closureTarget

/-- Above the stronger local-event exactification law, the remaining
constructive origin seam is exactly the constructive anchor-current target.
Once that target is met, the bundled constructive microscopic target follows.
-/
theorem constructiveMicroscopicTargetOfConstructiveAnchorCurrentTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventExactificationLaw Index Time Carrier Law)
    (hanchor : ConstructiveAnchorCurrentTarget data.toMicroscopicClosureLaw) :
    ConstructiveMicroscopicTarget data.toMicroscopicClosureLaw := by
  exact
    data.toMicroscopicClosureLaw.constructiveMicroscopicTargetOfParts
      (data.constructiveCurrentTargetOfConstructiveAnchorCurrentTarget hanchor)
      data.constructiveMicroscopicClausesTarget

/-- Above the stronger local-event exactification law, the remaining
constructive origin seam is exactly the constructive current target. Once that
target is met, the bundled constructive microscopic target follows. -/
theorem constructiveMicroscopicTargetOfConstructiveCurrentTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventExactificationLaw Index Time Carrier Law)
    (hcurrent : ConstructiveCurrentTarget data.toMicroscopicClosureLaw) :
    ConstructiveMicroscopicTarget data.toMicroscopicClosureLaw := by
  exact
    data.toMicroscopicClosureLaw.constructiveMicroscopicTargetOfParts
      hcurrent
      data.constructiveMicroscopicClausesTarget

/-- Above the stronger local-event exactification law, the remaining
constructive origin seam is exactly the constructive anchor-current target.
Once that target is met, the origin-readout target follows immediately. -/
theorem originReadoutTargetOfConstructiveAnchorCurrentTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventExactificationLaw Index Time Carrier Law)
    (hanchor : ConstructiveAnchorCurrentTarget data.toMicroscopicClosureLaw) :
    OriginReadoutTarget data.toMicroscopicClosureLaw := by
  exact
    data.toMicroscopicClosureLaw.originReadoutTargetOfConstructiveParts
      (data.constructiveCurrentTargetOfConstructiveAnchorCurrentTarget hanchor)
      data.constructiveMicroscopicClausesTarget

/-- Above the stronger local-event exactification law, the remaining
constructive origin seam is exactly the constructive current target. Once that
target is met, the origin-readout target follows immediately. -/
theorem originReadoutTargetOfConstructiveCurrentTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventExactificationLaw Index Time Carrier Law)
    (hcurrent : ConstructiveCurrentTarget data.toMicroscopicClosureLaw) :
    OriginReadoutTarget data.toMicroscopicClosureLaw := by
  exact
    data.toMicroscopicClosureLaw.originReadoutTargetOfConstructiveParts
      hcurrent
      data.constructiveMicroscopicClausesTarget

/-- Above the stronger local-event exactification law, the remaining
constructive origin seam is exactly the constructive anchor-current target.
Once that target is met, origin closure follows immediately. -/
theorem originClosureTargetOfConstructiveAnchorCurrentTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventExactificationLaw Index Time Carrier Law)
    (hanchor : ConstructiveAnchorCurrentTarget data.toMicroscopicClosureLaw) :
    OriginClosureTarget data.toMicroscopicClosureLaw := by
  exact
    data.toMicroscopicClosureLaw.originClosureTargetOfConstructiveParts
      (data.constructiveCurrentTargetOfConstructiveAnchorCurrentTarget hanchor)
      data.constructiveMicroscopicClausesTarget

/-- Above the stronger local-event exactification law, the remaining
constructive origin seam is exactly the constructive current target. Once that
target is met, origin closure follows immediately. -/
theorem originClosureTargetOfConstructiveCurrentTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventExactificationLaw Index Time Carrier Law)
    (hcurrent : ConstructiveCurrentTarget data.toMicroscopicClosureLaw) :
    OriginClosureTarget data.toMicroscopicClosureLaw := by
  exact
    data.toMicroscopicClosureLaw.originClosureTargetOfConstructiveParts
      hcurrent
      data.constructiveMicroscopicClausesTarget

/-- Above the stronger local-event exactification law, the detached
selected-bundle forcing surface already follows from the constructive
anchor-current target alone. -/
theorem originTargetSurfaceOfConstructiveAnchorCurrentTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventExactificationLaw Index Time Carrier Law)
    (hanchor : ConstructiveAnchorCurrentTarget data.toMicroscopicClosureLaw) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      realized_generator_carries_bedrock_law data.bridge.generator ∧
      AutonomousHorizon
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator ∧
      horizonFiberInvariant
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator := by
  exact
    data.toMicroscopicClosureLaw.originTargetSurfaceOfConstructiveParts
      (data.constructiveCurrentTargetOfConstructiveAnchorCurrentTarget hanchor)
      data.constructiveMicroscopicClausesTarget

/-- Above the stronger local-event exactification law, the detached
selected-bundle forcing surface already follows from the constructive current
target alone. -/
theorem originTargetSurfaceOfConstructiveCurrentTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventExactificationLaw Index Time Carrier Law)
    (hcurrent : ConstructiveCurrentTarget data.toMicroscopicClosureLaw) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      realized_generator_carries_bedrock_law data.bridge.generator ∧
      AutonomousHorizon
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator ∧
      horizonFiberInvariant
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator := by
  exact
    data.toMicroscopicClosureLaw.originTargetSurfaceOfConstructiveParts
      hcurrent
      data.constructiveMicroscopicClausesTarget

end LocalEventExactificationLaw

/-- Forget the distinguished leg from the anchored current object and read the
smaller constructive microscopic law that still suffices for origin closure.
-/
def AnchoredCurrentObject.toConstructiveMicroscopicLaw
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentObject Index Time Carrier Law) :
    ConstructiveMicroscopicLaw Index Time Carrier Law where
  toAnchoredCurrentTransport := data.toAnchoredCurrentTransport
  commonGrammar := data.commonGrammar
  firstStableBulkEventHasFourLegs := data.firstStableBulkEventHasFourLegs
  sixPairSlots := data.sixPairSlots
  exactifier := data.exactifier
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

/-- Forget the distinguished leg and exactifier-specific bookkeeping from the
anchored current object and read the minimal origin readout layer. -/
def AnchoredCurrentObject.toOriginReadoutLaw
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentObject Index Time Carrier Law) :
    OriginReadoutLaw data.toConstructiveMicroscopicLaw.toMicroscopicClosureLaw :=
  data.toConstructiveMicroscopicLaw.toOriginReadoutLaw

/-- Forget the object-level selected-bundle witness packaging and read the
smaller constructive microscopic law. -/
def LocalEventObject.toConstructiveMicroscopicLaw
    {Index Time Carrier Law : Type}
    (data : LocalEventObject Index Time Carrier Law) :
    ConstructiveMicroscopicLaw Index Time Carrier Law where
  toAnchoredCurrentTransport := {
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
        data.sameContinuumClosureClassOnSelectedBundle
          data.bridge.selectedBridge.observer rfl }
    closureTransport := {
      sameSelection := data.sameContinuumClosureClassOnSelectedBundle } }
  commonGrammar := data.commonGrammar
  firstStableBulkEventHasFourLegs := data.firstStableBulkEventHasFourLegs
  sixPairSlots := data.sixPairSlots
  exactifier := data.exactifier
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

/-- Forgetting to the local-event object and rebuilding the smaller
constructive microscopic law recovers the original package exactly. -/
theorem ConstructiveMicroscopicLaw.toLocalEventObject_toConstructiveMicroscopicLaw
    {Index Time Carrier Law : Type}
    (data : ConstructiveMicroscopicLaw Index Time Carrier Law) :
    data.toLocalEventObject.toConstructiveMicroscopicLaw = data := by
  cases data
  rfl

/-- Forget the object-level selected-bundle witness packaging and read the
smaller constructive origin-readout layer. -/
def LocalEventObject.toOriginReadoutLaw
    {Index Time Carrier Law : Type}
    (data : LocalEventObject Index Time Carrier Law) :
    OriginReadoutLaw data.toConstructiveMicroscopicLaw.toMicroscopicClosureLaw :=
  data.toConstructiveMicroscopicLaw.toOriginReadoutLaw

/-- Forget the object-level selected-bundle witness packaging from the local
event sector object and read the smaller constructive sector law. -/
def LocalEventSectorObject.toConstructiveSectorLaw
    {Index Time Carrier Law : Type}
    (data : LocalEventSectorObject Index Time Carrier Law) :
    ConstructiveSectorLaw Index Time Carrier Law where
  toConstructiveMicroscopicLaw := data.toLocalEventObject.toConstructiveMicroscopicLaw
  canonicalGeneration := data.canonicalGeneration
  generatedFromIntrinsicChannelAlgebra :=
    data.generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly :=
    data.minimalCompatibleRealizationsOnly
  generatedFromIntrinsicChannelAlgebra_valid :=
    data.generatedFromIntrinsicChannelAlgebra_valid
  minimalCompatibleRealizationsOnly_valid :=
    data.minimalCompatibleRealizationsOnly_valid

/-- Forget the distinguished leg from the anchored current sector object and
read the smaller constructive sector law. -/
def AnchoredCurrentSectorObject.toConstructiveSectorLaw
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentSectorObject Index Time Carrier Law) :
    ConstructiveSectorLaw Index Time Carrier Law where
  toConstructiveMicroscopicLaw := data.toAnchoredCurrentObject.toConstructiveMicroscopicLaw
  canonicalGeneration := data.canonicalGeneration
  generatedFromIntrinsicChannelAlgebra :=
    data.generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly :=
    data.minimalCompatibleRealizationsOnly
  generatedFromIntrinsicChannelAlgebra_valid :=
    data.generatedFromIntrinsicChannelAlgebra_valid
  minimalCompatibleRealizationsOnly_valid :=
    data.minimalCompatibleRealizationsOnly_valid

namespace ConstructiveSectorLaw

/-- Forget to the minimal origin readout layer below the constructive
microscopic law. -/
def toOriginReadoutLaw
    {Index Time Carrier Law : Type}
    (data : ConstructiveSectorLaw Index Time Carrier Law) :
    OriginReadoutLaw data.toConstructiveMicroscopicLaw.toMicroscopicClosureLaw :=
  data.toConstructiveMicroscopicLaw.toOriginReadoutLaw

/-- The sector law still determines the detached local-event sector object. -/
def toLocalEventSectorObject
    {Index Time Carrier Law : Type}
    (data : ConstructiveSectorLaw Index Time Carrier Law) :
    LocalEventSectorObject Index Time Carrier Law where
  toLocalEventObject := data.toConstructiveMicroscopicLaw.toLocalEventObject
  canonicalGeneration := data.canonicalGeneration
  generatedFromIntrinsicChannelAlgebra :=
    data.generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly :=
    data.minimalCompatibleRealizationsOnly
  generatedFromIntrinsicChannelAlgebra_valid :=
    data.generatedFromIntrinsicChannelAlgebra_valid
  minimalCompatibleRealizationsOnly_valid :=
    data.minimalCompatibleRealizationsOnly_valid

/-- Forgetting to the local-event sector object and rebuilding the smaller
constructive sector law recovers the original Step 3 package exactly. -/
theorem toLocalEventSectorObject_toConstructiveSectorLaw
    {Index Time Carrier Law : Type}
    (data : ConstructiveSectorLaw Index Time Carrier Law) :
    data.toLocalEventSectorObject.toConstructiveSectorLaw = data := by
  cases data
  rfl

/-- Read the proposition-level microscopic closure law from the constructive
sector law. -/
def toMicroscopicClosureLaw
    {Index Time Carrier Law : Type}
    (data : ConstructiveSectorLaw Index Time Carrier Law) :
    MicroscopicClosureLaw Index Time Carrier Law :=
  data.toConstructiveMicroscopicLaw.toMicroscopicClosureLaw

/-- Read the origin-closure witness from the constructive sector law. -/
def toOriginClosureWitness
    {Index Time Carrier Law : Type}
    (data : ConstructiveSectorLaw Index Time Carrier Law) :
    OriginClosureWitness data.toMicroscopicClosureLaw :=
  data.toConstructiveMicroscopicLaw.toOriginClosureWitness

/-- Read the intrinsic sector witness from the constructive sector law. -/
def toSectorOriginWitness
    {Index Time Carrier Law : Type}
    (data : ConstructiveSectorLaw Index Time Carrier Law) :
    SectorOriginWitness data.toMicroscopicClosureLaw where
  canonicalGeneration := data.canonicalGeneration
  generatedFromIntrinsicChannelAlgebra :=
    data.generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly :=
    data.minimalCompatibleRealizationsOnly
  generatedFromIntrinsicChannelAlgebra_valid :=
    data.generatedFromIntrinsicChannelAlgebra_valid
  minimalCompatibleRealizationsOnly_valid :=
    data.minimalCompatibleRealizationsOnly_valid

/-- Read the detached selected-bundle forcing package directly from the
constructive sector law. -/
def toSelectedBundleForcing
    {Index Time Carrier Law : Type}
    (data : ConstructiveSectorLaw Index Time Carrier Law) :
    SelectedBundleForcing Index Time Carrier Law :=
  data.toOriginClosureWitness.toSelectedBundleForcing

/-- Read the detached intrinsic-sector forcing package directly from the
constructive sector law. -/
def toIntrinsicSectorForcing
    {Index Time Carrier Law : Type}
    (data : ConstructiveSectorLaw Index Time Carrier Law) :
    IntrinsicSectorForcing Index Time Carrier Law :=
  data.toSectorOriginWitness.toIntrinsicSectorForcing
    data.toOriginClosureWitness

/-- Read the active intrinsic sector-generation object directly from the
constructive sector law. -/
def toIntrinsicSectorGeneration
    {Index Time Carrier Law : Type}
    (data : ConstructiveSectorLaw Index Time Carrier Law) :
    IntrinsicSectorGeneration Time Carrier Law :=
  data.toIntrinsicSectorForcing.toIntrinsicSectorGeneration

/-- Surface theorem for the constructive sector law. Above the smaller
constructive microscopic law, the only new public output is intrinsic sector
generation. -/
theorem surface
    {Index Time Carrier Law : Type}
    (data : ConstructiveSectorLaw Index Time Carrier Law) :
    Nonempty (PairExchangeCurrent data.currentCarrier data.Leg) ∧
      data.toConstructiveMicroscopicLaw.toCurrentAnchor.currentDirectReturnCompatible ∧
      data.toConstructiveMicroscopicLaw.toCurrentAnchor.visiblePrimitiveReadoutAutonomous ∧
      data.toConstructiveMicroscopicLaw.toCurrentAnchor.minimalVisibleQuotients ∧
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
            observer.continuumClass) ∧
      data.toConstructiveMicroscopicLaw.bundleArisesIntrinsicallyOnLeastMotionCut ∧
      data.toConstructiveMicroscopicLaw.noCarrierWiseVisibilityHypotheses ∧
      data.generatedFromIntrinsicChannelAlgebra ∧
      data.minimalCompatibleRealizationsOnly ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  obtain ⟨hcurrent, hdirret, haut, hmin, hexact, hforced, htransport, hintrinsic,
    hnocarrier⟩ := data.toConstructiveMicroscopicLaw.surface
  have horigin : OriginClosureTarget data.toMicroscopicClosureLaw :=
    data.originClosureTarget
  have hsector : SectorClosureTarget data.toMicroscopicClosureLaw :=
    by
      intro _origin
      exact ⟨data.toSectorOriginWitness⟩
  obtain ⟨_hbundle, _hstep3, _hbedrock, _haut2, _hfiber, _hgenmin, hprofile⟩ :=
    data.toMicroscopicClosureLaw.sectorTargetSurface horigin hsector
  exact
    ⟨hcurrent,
      hdirret,
      haut,
      hmin,
      hexact,
      hforced,
      htransport,
      hintrinsic,
      hnocarrier,
      data.generatedFromIntrinsicChannelAlgebra_valid,
      data.minimalCompatibleRealizationsOnly_valid,
      hprofile⟩

/-- The constructive sector law inherits origin closure from its underlying
constructive microscopic law. -/
theorem originClosureTarget
    {Index Time Carrier Law : Type}
    (data : ConstructiveSectorLaw Index Time Carrier Law) :
    OriginClosureTarget data.toMicroscopicClosureLaw := by
  exact data.toConstructiveMicroscopicLaw.originClosureTarget

/-- The constructive sector law now proves the previously target-level
sector-closure statement. -/
theorem sectorClosureTarget
    {Index Time Carrier Law : Type}
    (data : ConstructiveSectorLaw Index Time Carrier Law) :
    SectorClosureTarget data.toMicroscopicClosureLaw := by
  intro _origin
  exact ⟨data.toSectorOriginWitness⟩

/-- The detached Step 3 forcing surface already follows from the constructive
sector law with no extra sector witness hypothesis. -/
theorem sectorTargetSurface
    {Index Time Carrier Law : Type}
    (data : ConstructiveSectorLaw Index Time Carrier Law) :
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
      (∃ generatedFromIntrinsicChannelAlgebra :
          Prop,
          ∃ minimalCompatibleRealizationsOnly : Prop,
            generatedFromIntrinsicChannelAlgebra ∧
              minimalCompatibleRealizationsOnly) ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  exact
    data.toMicroscopicClosureLaw.sectorTargetSurface
      data.originClosureTarget
      data.sectorClosureTarget

end ConstructiveSectorLaw

/-- Exact law-level constructive sector target above one proposition-level
microscopic closure law. It asks only that the law admit one self-contained
constructive sector realization on the same selected datum. -/
def ConstructiveSectorTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) : Prop :=
  ∃ data : ConstructiveSectorLaw Index Time Carrier Law,
    data.toMicroscopicClosureLaw = law

namespace ConstructiveSectorLaw

/-- Any actual constructive sector law immediately realizes the exact
law-level sector target for its proposition-level law. -/
theorem target
    {Index Time Carrier Law : Type}
    (data : ConstructiveSectorLaw Index Time Carrier Law) :
    ConstructiveSectorTarget data.toMicroscopicClosureLaw := by
  exact ⟨data, rfl⟩

end ConstructiveSectorLaw

namespace MicroscopicClosureLaw

/-- The exact constructive sector target already yields the constructive
microscopic target by forgetting the sector-generation extension. -/
theorem constructiveMicroscopicTargetOfConstructiveSectorTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hsector : ConstructiveSectorTarget law) :
    ConstructiveMicroscopicTarget law := by
  rcases hsector with ⟨data, rfl⟩
  exact ⟨data.toConstructiveMicroscopicLaw, rfl⟩

/-- The exact constructive sector target already yields origin closure. -/
theorem originClosureTargetOfConstructiveSectorTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hsector : ConstructiveSectorTarget law) :
    OriginClosureTarget law := by
  rcases hsector with ⟨data, rfl⟩
  exact data.originClosureTarget

/-- The exact constructive sector target already yields the sector-closure
target. -/
theorem sectorClosureTargetOfConstructiveSectorTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hsector : ConstructiveSectorTarget law) :
    SectorClosureTarget law := by
  rcases hsector with ⟨data, rfl⟩
  exact data.sectorClosureTarget

/-- The detached Step 3 forcing surface already follows from the exact
constructive sector target. -/
theorem sectorTargetSurfaceOfConstructiveSectorTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hsector : ConstructiveSectorTarget law) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
      realized_generator_carries_bedrock_law law.bridge.generator ∧
      AutonomousHorizon
        law.bridge.selectedBridge.observer.selection.realization.tower
        law.bridge.selectedBridge.observer.selection.horizon
        law.bridge.generator ∧
      horizonFiberInvariant
        law.bridge.selectedBridge.observer.selection.realization.tower
        law.bridge.selectedBridge.observer.selection.horizon
        law.bridge.generator ∧
      (∃ generatedFromIntrinsicChannelAlgebra :
          Prop,
          ∃ minimalCompatibleRealizationsOnly : Prop,
            generatedFromIntrinsicChannelAlgebra ∧
              minimalCompatibleRealizationsOnly) ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  rcases hsector with ⟨data, rfl⟩
  exact data.sectorTargetSurface

end MicroscopicClosureLaw

end ClosureCurrent

end CoherenceCalculus
