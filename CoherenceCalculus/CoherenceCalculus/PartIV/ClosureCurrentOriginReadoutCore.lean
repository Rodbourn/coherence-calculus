import CoherenceCalculus.PartIV.ClosureCurrentOriginClosureCore
import CoherenceCalculus.PartIV.ClosureCurrentLocalEventCore
import CoherenceCalculus.PartIV.ClosureCurrentAnchorCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentOriginReadoutCore

Minimal constructive readout layer above one microscopic closure law.

`MicroscopicClosureLaw` is proposition-level. `OriginClosureWitness` is the
selected-bundle/readout package one ultimately wants to force from it. The
remaining honest question is therefore not whether stronger anchored objects
can realize origin closure; they already can. The question is what exact
constructive layer sits immediately above one fixed microscopic law and is
already sufficient to build that witness.

This file isolates that layer as `OriginReadoutLaw law`, and also splits it
into the smaller pieces that make the first unresolved theorem exact. It
keeps only:

* one selected-anchor current and visible quotient family;
* one common selected-cut closure transport package;
* one common grammar package and the two bundle-intrinsicity clauses.

No exactifier, no leg-count bookkeeping, and no distinguished leg are needed
at this seam. The new split makes the first unresolved descent precise:

* `OriginReadoutAnchorTarget law` asks for the selected-anchor current and
  visible quotient family;
* `OriginReadoutClosureTarget law` asks for the common selected-cut closure
  transport package;
* `OriginReadoutClausesTarget law` asks for the common grammar package and the
  two bundle-intrinsicity clauses.

The first two realize `OriginReadoutTransportTarget law`. That transport target
together with the clauses target realizes `OriginReadoutTarget law`. Once that
target is met, `OriginClosureTarget law` already follows directly.
-/

namespace ClosureCurrent

/-- Selected-anchor current side of the minimal origin readout layer above one
fixed microscopic closure law. -/
structure OriginReadoutAnchor
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) where
  currentCarrier : PairExchangeCarrier
  Leg : Type
  current : PairExchangeCurrent currentCarrier Leg
  visible : VisibleCarrierRole → Type
  quotient :
    (role : VisibleCarrierRole) →
      VisibleQuotient currentCarrier Leg (visible role)

/-- Selected-anchor transport side of the minimal origin readout layer above
one fixed microscopic closure law. -/
structure OriginReadoutTransport
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    extends OriginReadoutAnchor law where
  closureTransport :
    ClosureClassTransport
      Time Carrier Law
      law.bridge.selectedBridge.observer.selection
      law.physicalPrinciple.selectedLaw.endpointClosureClass

/-- Common grammar and intrinsicity clauses above one fixed microscopic
closure law. These are the proposition-level clauses still needed together
with the selected-anchor transport data to build the origin readout layer. -/
structure OriginReadoutClauses
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

/-- Minimal constructive readout layer above one fixed microscopic closure law.
It carries exactly the selected-anchor data needed to build the
selected-bundle/readout witness for `law`. -/
structure OriginReadoutLaw
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    extends OriginReadoutTransport law, OriginReadoutClauses law

/-- Exact selected-anchor transport target above one proposition-level
microscopic closure law. -/
def OriginReadoutAnchorTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) : Prop :=
  Nonempty (OriginReadoutAnchor law)

namespace MicroscopicClosureLaw

private def trivialPairExchangeCarrier : PairExchangeCarrier where
  Value := PUnit
  Stock := PUnit
  zero := PUnit.unit
  reverse := fun _ => PUnit.unit
  stock := fun _ => PUnit.unit
  reverse_involutive := by
    intro x
    cases x
    rfl
  reverse_zero := rfl
  stock_reverse := by
    intro x
    cases x
    rfl

private def trivialPairExchangeCurrent :
    PairExchangeCurrent trivialPairExchangeCarrier PUnit where
  value := fun _ _ => PUnit.unit
  diagonal_zero := by
    intro a
    cases a
    rfl
  swap_reverse := by
    intro a b
    cases a
    cases b
    rfl

private def trivialVisibleQuotient :
    VisibleQuotient trivialPairExchangeCarrier PUnit PUnit where
  read := fun _ => PUnit.unit
  evolve := fun _ => PUnit.unit
  autonomousReadout := True
  minimalNontrivial := True
  autonomousReadout_valid := trivial
  minimalNontrivial_valid := trivial

/-- The selected-anchor portion of the origin-readout target is canonical:
the target only asks for one selected-anchor carrier/current/readout object,
and a trivial such object exists without any additional detached hypothesis. -/
theorem trivialOriginReadoutAnchorTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) :
    OriginReadoutAnchorTarget law := by
  exact
    ⟨{ currentCarrier := trivialPairExchangeCarrier
       Leg := PUnit
       current := trivialPairExchangeCurrent
       visible := fun _ => PUnit
       quotient := fun _ => trivialVisibleQuotient }⟩

end MicroscopicClosureLaw

/-- Exact selected-cut closure-transport target above one proposition-level
microscopic closure law. -/
def OriginReadoutClosureTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) : Prop :=
  Nonempty
    (ClosureClassTransport
      Time Carrier Law
      law.bridge.selectedBridge.observer.selection
      law.physicalPrinciple.selectedLaw.endpointClosureClass)

/-- Exact selected-anchor transport target above one proposition-level
microscopic closure law. -/
def OriginReadoutTransportTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) : Prop :=
  Nonempty (OriginReadoutTransport law)

namespace OriginReadoutTransport

/-- Reassemble the selected-anchor transport package from the selected-anchor
current data and the common selected-cut closure transport. -/
def ofParts
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (anchor : OriginReadoutAnchor law)
    (closureTransport :
      ClosureClassTransport
        Time Carrier Law
        law.bridge.selectedBridge.observer.selection
        law.physicalPrinciple.selectedLaw.endpointClosureClass) :
    OriginReadoutTransport law where
  toOriginReadoutAnchor := anchor
  closureTransport := closureTransport

/-- The selected-anchor current data of an actual transport package already
realize the corresponding anchor target. -/
theorem anchorTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : OriginReadoutTransport law) :
    OriginReadoutAnchorTarget law := by
  exact ⟨data.toOriginReadoutAnchor⟩

/-- The selected-cut closure transport of an actual transport package already
realizes the corresponding closure target. -/
theorem closureTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : OriginReadoutTransport law) :
    OriginReadoutClosureTarget law := by
  exact ⟨data.closureTransport⟩

end OriginReadoutTransport

/-- Exact common-grammar/intrinsicity target above one proposition-level
microscopic closure law. -/
def OriginReadoutClausesTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) : Prop :=
  Nonempty (OriginReadoutClauses law)

/-- The exact remaining origin-side descent target above one proposition-level
microscopic closure law: the law admits the minimal selected-anchor readout
layer needed to build the selected-bundle/readout witness. -/
def OriginReadoutTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) : Prop :=
  Nonempty (OriginReadoutLaw law)

namespace OriginReadoutLaw

/-- The selected-anchor current side of an actual origin readout law already
realizes the corresponding anchor target. -/
theorem anchorTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : OriginReadoutLaw law) :
    OriginReadoutAnchorTarget law := by
  exact data.toOriginReadoutTransport.anchorTarget

/-- The selected-cut closure transport side of an actual origin readout law
already realizes the corresponding closure target. -/
theorem closureTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : OriginReadoutLaw law) :
    OriginReadoutClosureTarget law := by
  exact data.toOriginReadoutTransport.closureTarget

/-- The selected-anchor transport side of an actual origin readout law already
realizes the corresponding transport target. -/
theorem transportTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : OriginReadoutLaw law) :
    OriginReadoutTransportTarget law := by
  exact ⟨data.toOriginReadoutTransport⟩

/-- The common grammar and intrinsicity clauses of an actual origin readout
law already realize the corresponding clauses target. -/
theorem clausesTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : OriginReadoutLaw law) :
    OriginReadoutClausesTarget law := by
  exact ⟨data.toOriginReadoutClauses⟩

/-- Any actual minimal readout layer immediately realizes the readout target
for its microscopic closure law. -/
theorem readoutTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : OriginReadoutLaw law) :
    OriginReadoutTarget law := by
  exact ⟨data⟩

/-- Reassemble the minimal origin readout law from its two smaller components.
-/
def ofParts
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (transport : OriginReadoutTransport law)
    (clauses : OriginReadoutClauses law) :
    OriginReadoutLaw law where
  toOriginReadoutTransport := transport
  toOriginReadoutClauses := clauses

/-- The minimal readout layer still determines the transported selected
current anchor used by the detached current lane. -/
def toAnchoredCurrentTransport
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : OriginReadoutLaw law) :
    AnchoredCurrentTransport Index Time Carrier Law where
  toCurrentAnchor := {
    bridge := law.bridge
    physicalPrinciple := law.physicalPrinciple
    sameSelectedLawAsBridge := law.sameSelectedLawAsBridge
    currentCarrier := data.currentCarrier
    Leg := data.Leg
    current := data.current
    visible := data.visible
    quotient := data.quotient
    sameAnchoredContinuumClosureClass :=
      data.closureTransport.sameSelection law.bridge.selectedBridge.observer rfl }
  closureTransport := data.closureTransport

/-- Surface theorem for the minimal readout layer. The selected anchor already
provides exact visibility, forced continuum closure, selected-cut closure
transport, and the two bundle-intrinsicity clauses. -/
theorem surface
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : OriginReadoutLaw law) :
    Nonempty (PairExchangeCurrent data.currentCarrier data.Leg) ∧
      data.toAnchoredCurrentTransport.toCurrentAnchor.currentDirectReturnCompatible ∧
      data.toAnchoredCurrentTransport.toCurrentAnchor.visiblePrimitiveReadoutAutonomous ∧
      data.toAnchoredCurrentTransport.toCurrentAnchor.minimalVisibleQuotients ∧
      exactVisibleOnCut
        (law.bridge.selectedBridge.observer.selection.realization.tower.π
          law.bridge.selectedBridge.observer.selection.horizon)
        (selected_observed_law law.bridge.selectedBridge.observer.selection).op ∧
      ForcedContinuumLaw
        law.bridge.selectedBridge.observer.continuumClass
        law.physicalPrinciple.selectedLaw.selectedClosureLaw ∧
      (∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
        observer.selection = law.bridge.selectedBridge.observer.selection →
          law.physicalPrinciple.selectedLaw.endpointClosureClass =
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

/-- Visible bundle sectors derived directly from the selected-anchor quotient
values. The kinetic sector is witnessed by stock at the zero current value. -/
def derivedSectors
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : OriginReadoutLaw law) :
    BundleSectorFamily where
  sector
    | BundleSectorRole.phase => Nonempty (data.visible VisibleCarrierRole.phase)
    | BundleSectorRole.wave => Nonempty (data.visible VisibleCarrierRole.wave)
    | BundleSectorRole.kinetic => Nonempty data.currentCarrier.Stock
    | BundleSectorRole.gauge => Nonempty (data.visible VisibleCarrierRole.gauge)
    | BundleSectorRole.geometric =>
        Nonempty (data.visible VisibleCarrierRole.geometric)

/-- Role readout on the selected bundle for the minimal readout layer. -/
def readsRoleOnSelectedBundle
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (_data : OriginReadoutLaw law)
    (_role : VisibleCarrierRole) :
    ObserverSelection.LeastMotion Time Carrier Law → Prop :=
  fun observer => observer = law.bridge.selectedBridge.observer

/-- The selected-anchor readout remains on the selected bridge observer. -/
theorem readsRoleOnSelectedBundle_sameSelection
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : OriginReadoutLaw law)
    (role : VisibleCarrierRole)
    (observer : ObserverSelection.LeastMotion Time Carrier Law)
    (hread : data.readsRoleOnSelectedBundle role observer) :
    observer.selection = law.bridge.selectedBridge.observer.selection := by
  rcases hread with rfl
  rfl

/-- Build the selected-bundle/readout witness directly from the minimal
readout layer above `law`. -/
def toOriginClosureWitness
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : OriginReadoutLaw law) :
    OriginClosureWitness law where
  commonGrammar := data.commonGrammar
  selectedObservedBundle := law.physicalPrinciple.sameCoherentBundle
  sectors := data.derivedSectors
  bundlePhysicallyRealized :=
    data.commonGrammar.selectedVisibleLawPhysicallyRealized
  bundleSharedByAllCarriers :=
    ∀ role : VisibleCarrierRole,
      ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
        data.readsRoleOnSelectedBundle role observer →
          observer.selection = law.bridge.selectedBridge.observer.selection
  sameSelectedEffectiveLawOnEachCarrier :=
    law.physicalPrinciple.selectedLaw.selection =
      law.bridge.selectedBridge.observer.selection
  carrierLevelIdentificationOnlyFinalStep :=
    data.commonGrammar.carrierLevelPhysicalLaw
  bundleArisesIntrinsicallyOnLeastMotionCut :=
    data.bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses :=
    data.noCarrierWiseVisibilityHypotheses
  readsRoleOnSelectedBundle := data.readsRoleOnSelectedBundle
  readsRoleOnSelectedBundle_sameSelection := by
    intro role observer hread
    exact data.readsRoleOnSelectedBundle_sameSelection role observer hread
  sameContinuumClosureClassOnSelectedBundle := by
    intro observer hselection
    exact data.closureTransport.sameSelection observer hselection
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
  selectedObservedBundle_valid :=
    law.physicalPrinciple.sameCoherentBundle_valid
  phaseCarrierSector_valid :=
    ⟨(data.quotient VisibleCarrierRole.phase).read data.current⟩
  waveCarrierSector_valid :=
    ⟨(data.quotient VisibleCarrierRole.wave).read data.current⟩
  kineticCarrierSector_valid :=
    ⟨data.currentCarrier.stock data.currentCarrier.zero⟩
  gaugeCarrierSector_valid :=
    ⟨(data.quotient VisibleCarrierRole.gauge).read data.current⟩
  geometricCarrierSector_valid :=
    ⟨(data.quotient VisibleCarrierRole.geometric).read data.current⟩
  bundlePhysicallyRealized_valid :=
    data.selectedVisibleLawPhysicallyRealized_valid
  bundleSharedByAllCarriers_valid := by
    intro role observer hread
    exact data.readsRoleOnSelectedBundle_sameSelection role observer hread
  sameSelectedEffectiveLawOnEachCarrier_valid :=
    law.sameSelectedLawAsBridge
  carrierLevelIdentificationOnlyFinalStep_valid :=
    data.carrierLevelPhysicalLaw_valid
  bundleArisesIntrinsicallyOnLeastMotionCut_valid :=
    data.bundleArisesIntrinsicallyOnLeastMotionCut_valid
  noCarrierWiseVisibilityHypotheses_valid :=
    data.noCarrierWiseVisibilityHypotheses_valid

/-- The minimal readout layer already forces the origin-closure target for the
fixed microscopic law. -/
theorem originClosureTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : OriginReadoutLaw law) :
    OriginClosureTarget law := by
  exact ⟨data.toOriginClosureWitness⟩

/-- The detached selected-bundle forcing surface follows directly from the
minimal readout layer. -/
theorem originTargetSurface
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : OriginReadoutLaw law) :
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
  exact law.originTargetSurface data.originClosureTarget

end OriginReadoutLaw

/-- Once the minimal origin readout target is met for `law`, the
selected-bundle/readout witness target is already met as well. -/
theorem MicroscopicClosureLaw.originClosureTargetOfReadout
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hreadout : OriginReadoutTarget law) :
    OriginClosureTarget law := by
  rcases hreadout with ⟨data⟩
  exact data.originClosureTarget

/-- The two smaller origin-side targets already realize the full origin
readout target. -/
theorem MicroscopicClosureLaw.originReadoutTargetOfParts
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (htransport : OriginReadoutTransportTarget law)
    (hclauses : OriginReadoutClausesTarget law) :
    OriginReadoutTarget law := by
  rcases htransport with ⟨transport⟩
  rcases hclauses with ⟨clauses⟩
  exact ⟨OriginReadoutLaw.ofParts transport clauses⟩

/-- The selected-anchor data and the selected-cut closure transport already
realize the exact transport target. -/
theorem MicroscopicClosureLaw.originReadoutTransportTargetOfParts
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hanchor : OriginReadoutAnchorTarget law)
    (hclosure : OriginReadoutClosureTarget law) :
    OriginReadoutTransportTarget law := by
  rcases hanchor with ⟨anchor⟩
  rcases hclosure with ⟨closureTransport⟩
  exact ⟨OriginReadoutTransport.ofParts anchor closureTransport⟩

/-- If the exact origin-readout descent target is met for a microscopic closure
law, then the detached selected-bundle forcing surface follows immediately. -/
theorem MicroscopicClosureLaw.originReadoutTargetSurface
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hreadout : OriginReadoutTarget law) :
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
  exact law.originTargetSurface (law.originClosureTargetOfReadout hreadout)

/-- If the two smaller origin-side targets are met for a microscopic closure
law, then the detached selected-bundle forcing surface follows immediately. -/
theorem MicroscopicClosureLaw.originReadoutTargetSurfaceOfParts
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (htransport : OriginReadoutTransportTarget law)
    (hclauses : OriginReadoutClausesTarget law) :
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
      (law.originReadoutTargetOfParts htransport hclauses)

namespace LocalEventExactificationLaw

/-- Forget the selected-bundle/readout data carried by the local-event
exactification law and recover the smaller proposition-level microscopic
closure law on the same bridge and selected physical law. -/
def toMicroscopicClosureLaw
    {Index Time Carrier Law : Type}
    (data : LocalEventExactificationLaw Index Time Carrier Law) :
    MicroscopicClosureLaw Index Time Carrier Law where
  bridge := data.bridge
  physicalPrinciple := data.physicalPrinciple
  sameSelectedLawAsBridge := data.sameSelectedLawAsBridge
  hiddenExactExchangeCurrent := data.hiddenExactExchangeCurrent
  currentLivesOnOrientedPairSlots := data.currentLivesOnOrientedPairSlots
  firstStableBulkEventCarriesSixSlotCurrent :=
    data.firstStableBulkEventCarriesSixSlotCurrent
  currentStockConserved := data.currentStockConserved
  currentDirectReturnCompatible := data.currentDirectReturnCompatible
  relabelingEquivariant := data.relabelingEquivariant
  localLosslessExactification := data.localLosslessExactification
  visiblePrimitiveReadoutAutonomous :=
    data.visiblePrimitiveReadoutAutonomous
  returnedDefectActsAsVisibleResidual :=
    data.returnedDefectActsAsVisibleResidual
  hiddenExactExchangeCurrent_valid := data.hiddenExactExchangeCurrent_valid
  currentLivesOnOrientedPairSlots_valid :=
    data.currentLivesOnOrientedPairSlots_valid
  firstStableBulkEventCarriesSixSlotCurrent_valid :=
    data.firstStableBulkEventCarriesSixSlotCurrent_valid
  currentStockConserved_valid := data.currentStockConserved_valid
  currentDirectReturnCompatible_valid :=
    data.currentDirectReturnCompatible_valid
  relabelingEquivariant_valid := data.relabelingEquivariant_valid
  localLosslessExactification_valid :=
    data.localLosslessExactification_valid
  visiblePrimitiveReadoutAutonomous_valid :=
    data.visiblePrimitiveReadoutAutonomous_valid
  returnedDefectActsAsVisibleResidual_valid :=
    data.returnedDefectActsAsVisibleResidual_valid

/-- The stronger local-event exactification law already carries the entire
common-grammar/intrinsicity side of the origin seam for its smaller
microscopic closure law. -/
def toOriginReadoutClauses
    {Index Time Carrier Law : Type}
    (data : LocalEventExactificationLaw Index Time Carrier Law) :
    OriginReadoutClauses data.toMicroscopicClosureLaw where
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
common-grammar/intrinsicity target for its smaller microscopic closure law. -/
theorem clausesTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventExactificationLaw Index Time Carrier Law) :
    OriginReadoutClausesTarget data.toMicroscopicClosureLaw := by
  exact ⟨data.toOriginReadoutClauses⟩

/-- The stronger local-event exactification law already realizes the exact
selected-cut closure-transport target for its smaller microscopic closure law.
-/
theorem closureTarget
    {Index Time Carrier Law : Type}
    (data : LocalEventExactificationLaw Index Time Carrier Law) :
    OriginReadoutClosureTarget data.toMicroscopicClosureLaw := by
  exact ⟨data.toLocalEventCurrentLaw.toClosureClassTransport⟩

/-- Above the stronger local-event exactification law, the remaining transport
seam is exactly the selected-anchor current/quotient target. -/
theorem originReadoutTransportTargetOfAnchor
    {Index Time Carrier Law : Type}
    (data : LocalEventExactificationLaw Index Time Carrier Law)
    (hanchor : OriginReadoutAnchorTarget data.toMicroscopicClosureLaw) :
    OriginReadoutTransportTarget data.toMicroscopicClosureLaw := by
  exact
    data.toMicroscopicClosureLaw.originReadoutTransportTargetOfParts
      hanchor
      data.closureTarget

/-- Above the stronger local-event exactification law, the remaining origin
seam is exactly the selected-anchor current/quotient target. Once that target
is met, the full origin readout target follows immediately. -/
theorem originReadoutTargetOfAnchor
    {Index Time Carrier Law : Type}
    (data : LocalEventExactificationLaw Index Time Carrier Law)
    (hanchor : OriginReadoutAnchorTarget data.toMicroscopicClosureLaw) :
    OriginReadoutTarget data.toMicroscopicClosureLaw := by
  exact
    data.toMicroscopicClosureLaw.originReadoutTargetOfParts
      (data.originReadoutTransportTargetOfAnchor hanchor)
      data.clausesTarget

/-- Above the stronger local-event exactification law, the remaining origin
seam is exactly the selected-anchor transport target. Once that target is met,
the full origin readout target follows immediately. -/
theorem originReadoutTargetOfTransport
    {Index Time Carrier Law : Type}
    (data : LocalEventExactificationLaw Index Time Carrier Law)
    (htransport : OriginReadoutTransportTarget data.toMicroscopicClosureLaw) :
    OriginReadoutTarget data.toMicroscopicClosureLaw := by
  exact
    data.toMicroscopicClosureLaw.originReadoutTargetOfParts
      htransport
      data.clausesTarget

/-- Above the stronger local-event exactification law, a selected-anchor
transport witness already forces origin closure. -/
theorem originClosureTargetOfTransport
    {Index Time Carrier Law : Type}
    (data : LocalEventExactificationLaw Index Time Carrier Law)
    (htransport : OriginReadoutTransportTarget data.toMicroscopicClosureLaw) :
    OriginClosureTarget data.toMicroscopicClosureLaw := by
  exact
    data.toMicroscopicClosureLaw.originClosureTargetOfReadout
      (data.originReadoutTargetOfTransport htransport)

/-- Above the stronger local-event exactification law, a selected-anchor
current/quotient witness already forces origin closure. -/
theorem originClosureTargetOfAnchor
    {Index Time Carrier Law : Type}
    (data : LocalEventExactificationLaw Index Time Carrier Law)
    (hanchor : OriginReadoutAnchorTarget data.toMicroscopicClosureLaw) :
    OriginClosureTarget data.toMicroscopicClosureLaw := by
  exact
    data.originClosureTargetOfTransport
      (data.originReadoutTransportTargetOfAnchor hanchor)

/-- Above the stronger local-event exactification law, the detached
selected-bundle forcing surface already follows from the selected-anchor
transport target alone. -/
theorem originTargetSurfaceOfTransport
    {Index Time Carrier Law : Type}
    (data : LocalEventExactificationLaw Index Time Carrier Law)
    (htransport : OriginReadoutTransportTarget data.toMicroscopicClosureLaw) :
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
    data.toMicroscopicClosureLaw.originReadoutTargetSurfaceOfParts
      htransport
      data.clausesTarget

/-- Above the stronger local-event exactification law, the detached
selected-bundle forcing surface already follows from the selected-anchor
current/quotient target alone. -/
theorem originTargetSurfaceOfAnchor
    {Index Time Carrier Law : Type}
    (data : LocalEventExactificationLaw Index Time Carrier Law)
    (hanchor : OriginReadoutAnchorTarget data.toMicroscopicClosureLaw) :
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
    data.originTargetSurfaceOfTransport
      (data.originReadoutTransportTargetOfAnchor hanchor)

end LocalEventExactificationLaw

end ClosureCurrent

end CoherenceCalculus
