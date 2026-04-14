import CoherenceCalculus.PartIV.ClosureCurrentForcingCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentMicroscopicCore

Role-indexed detached microscopic interface for the candidate closure-current
law.

`ClosureCurrentForcingCore` isolates the exact selected-bundle and
intrinsic-sector-generation packages needed to recover the active Part IV
surface. This file compresses the remaining microscopic seam one step further:

* one role-indexed visible carrier family replaces four independent carrier
  readout clauses;
* one microscopic selected-bundle law yields the detached
  `SelectedBundleForcing` package;
* one microscopic sector law then yields the detached
  `IntrinsicSectorForcing` package and therefore the current upstream forcing
  surface.

Nothing here claims that the active bedrock-certified spine has already proved
this microscopic law. The point is to make the remaining theorem target
smaller, cleaner, and more visibly role-indexed.
-/

namespace ClosureCurrent

/-- The four visible carrier roles presently read from the detached
closure-current law surface. The role indexing is explicit so the microscopic
law can state one common readout family instead of four unrelated predicates.
-/
inductive VisibleCarrierRole
  | phase
  | wave
  | gauge
  | geometric

/-- The five visible carrier sectors appearing in the common selected-bundle
assembly. This includes the hydrodynamic closure sector, since the bundle-side
assembly package is wider than the four direct readout roles. -/
inductive BundleSectorRole
  | phase
  | wave
  | kinetic
  | gauge
  | geometric

/-- Role-indexed bundle-sector family for the common selected-bundle assembly.
This compresses the bundle-side sector bookkeeping into one visible-family
interface instead of five separate primitive fields. -/
structure BundleSectorFamily where
  sector : BundleSectorRole → Prop

/-- Detached bundle-first assembly law above the physical realization package.
This is smaller than `SelectedBundle.Assembly`: it stores one role-indexed
sector family instead of separate carrier-sector fields. -/
structure BundleAssemblyLaw (Time Carrier Law : Type) where
  selectedObservedBundle : Prop
  sectors : BundleSectorFamily
  physicalPrinciple : PhysicalRealizationPrinciple Time Carrier Law
  bundlePhysicallyRealized : Prop
  bundleSharedByAllCarriers : Prop
  sameSelectedEffectiveLawOnEachCarrier : Prop
  carrierLevelIdentificationOnlyFinalStep : Prop
  selectedObservedBundle_valid : selectedObservedBundle
  phaseCarrierSector_valid : sectors.sector BundleSectorRole.phase
  waveCarrierSector_valid : sectors.sector BundleSectorRole.wave
  kineticCarrierSector_valid : sectors.sector BundleSectorRole.kinetic
  gaugeCarrierSector_valid : sectors.sector BundleSectorRole.gauge
  geometricCarrierSector_valid : sectors.sector BundleSectorRole.geometric
  bundlePhysicallyRealized_valid : bundlePhysicallyRealized
  bundleSharedByAllCarriers_valid : bundleSharedByAllCarriers
  sameSelectedEffectiveLawOnEachCarrier_valid :
    sameSelectedEffectiveLawOnEachCarrier
  carrierLevelIdentificationOnlyFinalStep_valid :
    carrierLevelIdentificationOnlyFinalStep

/-- The detached bundle-first assembly law recovers the active
`SelectedBundle.Assembly` package. -/
def BundleAssemblyLaw.toAssembly
    {Time Carrier Law : Type}
    (data : BundleAssemblyLaw Time Carrier Law) :
    SelectedBundle.Assembly Time Carrier Law where
  selectedObservedBundle := data.selectedObservedBundle
  phaseCarrierSector := data.sectors.sector BundleSectorRole.phase
  waveCarrierSector := data.sectors.sector BundleSectorRole.wave
  kineticCarrierSector := data.sectors.sector BundleSectorRole.kinetic
  gaugeCarrierSector := data.sectors.sector BundleSectorRole.gauge
  geometricCarrierSector := data.sectors.sector BundleSectorRole.geometric
  physicalPrinciple := data.physicalPrinciple
  bundlePhysicallyRealized := data.bundlePhysicallyRealized
  bundleSharedByAllCarriers := data.bundleSharedByAllCarriers
  sameSelectedEffectiveLawOnEachCarrier :=
    data.sameSelectedEffectiveLawOnEachCarrier
  carrierLevelIdentificationOnlyFinalStep :=
    data.carrierLevelIdentificationOnlyFinalStep
  selectedObservedBundle_valid := data.selectedObservedBundle_valid
  phaseCarrierSector_valid := data.phaseCarrierSector_valid
  waveCarrierSector_valid := data.waveCarrierSector_valid
  kineticCarrierSector_valid := data.kineticCarrierSector_valid
  gaugeCarrierSector_valid := data.gaugeCarrierSector_valid
  geometricCarrierSector_valid := data.geometricCarrierSector_valid
  bundlePhysicallyRealized_valid := data.bundlePhysicallyRealized_valid
  bundleSharedByAllCarriers_valid := data.bundleSharedByAllCarriers_valid
  sameSelectedEffectiveLawOnEachCarrier_valid :=
    data.sameSelectedEffectiveLawOnEachCarrier_valid
  carrierLevelIdentificationOnlyFinalStep_valid :=
    data.carrierLevelIdentificationOnlyFinalStep_valid

/-- The detached bundle-first assembly law already carries the full selected
bundle assembly surface. -/
theorem BundleAssemblyLaw.surface
    {Time Carrier Law : Type}
    (data : BundleAssemblyLaw Time Carrier Law) :
    data.selectedObservedBundle ∧
      data.sectors.sector BundleSectorRole.phase ∧
      data.sectors.sector BundleSectorRole.wave ∧
      data.sectors.sector BundleSectorRole.kinetic ∧
      data.sectors.sector BundleSectorRole.gauge ∧
      data.sectors.sector BundleSectorRole.geometric ∧
      data.bundlePhysicallyRealized ∧
      data.bundleSharedByAllCarriers ∧
      data.sameSelectedEffectiveLawOnEachCarrier ∧
      data.carrierLevelIdentificationOnlyFinalStep := by
  exact
    ⟨data.selectedObservedBundle_valid,
      data.phaseCarrierSector_valid,
      data.waveCarrierSector_valid,
      data.kineticCarrierSector_valid,
      data.gaugeCarrierSector_valid,
      data.geometricCarrierSector_valid,
      data.bundlePhysicallyRealized_valid,
      data.bundleSharedByAllCarriers_valid,
      data.sameSelectedEffectiveLawOnEachCarrier_valid,
      data.carrierLevelIdentificationOnlyFinalStep_valid⟩

/-- A role-indexed selected-bundle readout family. Every visible carrier role
is read on the same selected bundle. -/
structure RoleReadoutFamily
    (Time Carrier Law : Type)
    (selection : SelectionDatum Time) where
  readsOnSelectedBundle :
    VisibleCarrierRole →
      ObserverSelection.LeastMotion Time Carrier Law → Prop
  sameSelection :
    ∀ role : VisibleCarrierRole,
      ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
        readsOnSelectedBundle role observer →
          observer.selection = selection

/-- Each role in a role-indexed family defines one carrier readout on the same
selected bundle. -/
def RoleReadoutFamily.carrierReadout
    {Time Carrier Law : Type}
    {selection : SelectionDatum Time}
    (data : RoleReadoutFamily Time Carrier Law selection)
    (role : VisibleCarrierRole) :
    CarrierReadout Time Carrier Law selection where
  readsOnSelectedBundle := data.readsOnSelectedBundle role
  sameSelection := data.sameSelection role

/-- Reading one role from the role-indexed family already fixes the selected
cut of that observer. -/
theorem RoleReadoutFamily.selection
    {Time Carrier Law : Type}
    {selection : SelectionDatum Time}
    (data : RoleReadoutFamily Time Carrier Law selection)
    (role : VisibleCarrierRole)
    (observer : ObserverSelection.LeastMotion Time Carrier Law)
    (hread : data.readsOnSelectedBundle role observer) :
    observer.selection = selection := by
  exact data.sameSelection role observer hread

/-- Detached microscopic selected-bundle law: one role-indexed visible family,
one common continuum-closure transport law, and the same selected bridge datum
used by the present autonomy package. -/
structure MicroscopicBundleLaw (Index Time Carrier Law : Type) where
  bridge : BridgeData Index Time Carrier Law
  assembly : BundleAssemblyLaw Time Carrier Law
  sameSelectedLawAsBridge :
    assembly.physicalPrinciple.selectedLaw.selection =
      bridge.selectedBridge.observer.selection
  roles :
    RoleReadoutFamily
      Time Carrier Law
      bridge.selectedBridge.observer.selection
  continuumClosure :
    ClosureClassTransport
      Time Carrier Law
      bridge.selectedBridge.observer.selection
      assembly.physicalPrinciple.selectedLaw.endpointClosureClass
  bundleArisesIntrinsicallyOnLeastMotionCut : Prop
  noCarrierWiseVisibilityHypotheses : Prop
  bundleArisesIntrinsicallyOnLeastMotionCut_valid :
    bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses_valid :
    noCarrierWiseVisibilityHypotheses

/-- The role-indexed microscopic law yields the detached bundle-readout
package. -/
def MicroscopicBundleLaw.toBundleReadout
    {Index Time Carrier Law : Type}
    (data : MicroscopicBundleLaw Index Time Carrier Law) :
    BundleReadout
      Time Carrier Law
      data.bridge.selectedBridge.observer.selection
      data.assembly.physicalPrinciple.selectedLaw.endpointClosureClass where
  phase := data.roles.carrierReadout VisibleCarrierRole.phase
  wave := data.roles.carrierReadout VisibleCarrierRole.wave
  gauge := data.roles.carrierReadout VisibleCarrierRole.gauge
  geometric := data.roles.carrierReadout VisibleCarrierRole.geometric
  continuumClosure := data.continuumClosure
  bundleArisesIntrinsicallyOnLeastMotionCut :=
    data.bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses :=
    data.noCarrierWiseVisibilityHypotheses
  bundleArisesIntrinsicallyOnLeastMotionCut_valid :=
    data.bundleArisesIntrinsicallyOnLeastMotionCut_valid
  noCarrierWiseVisibilityHypotheses_valid :=
    data.noCarrierWiseVisibilityHypotheses_valid

/-- The role-indexed microscopic law yields the detached selected-bundle
forcing interface directly. -/
def MicroscopicBundleLaw.toSelectedBundleForcing
    {Index Time Carrier Law : Type}
    (data : MicroscopicBundleLaw Index Time Carrier Law) :
    SelectedBundleForcing Index Time Carrier Law where
  bridge := data.bridge
  assembly := data.assembly.toAssembly
  sameSelectedLawAsBridge := data.sameSelectedLawAsBridge
  readout := data.toBundleReadout

/-- Any role read from the microscopic selected-bundle law inherits the exact
carrier closure readout package automatically. -/
theorem MicroscopicBundleLaw.carrierClosureReadout
    {Index Time Carrier Law : Type}
    (data : MicroscopicBundleLaw Index Time Carrier Law)
    (role : VisibleCarrierRole)
    (observer : ObserverSelection.LeastMotion Time Carrier Law)
    (hread : data.roles.readsOnSelectedBundle role observer) :
    (data.assembly.physicalPrinciple.selectedLaw.selection =
      observer.selection) ∧
      exactVisibleOnCut
        (observer.selection.realization.tower.π observer.selection.horizon)
        (selected_observed_law observer.selection).op ∧
      ForcedContinuumLaw
        observer.continuumClass
        data.assembly.physicalPrinciple.selectedLaw.selectedClosureLaw := by
  exact
    SelectedBundleForcing.carrierClosureReadout
      data.toSelectedBundleForcing
      (data.roles.carrierReadout role)
      observer
      hread

/-- The role-indexed microscopic law transports exact carrier closure readout
uniformly across all four visible carrier roles. -/
theorem MicroscopicBundleLaw.readoutSurface
    {Index Time Carrier Law : Type}
    (data : MicroscopicBundleLaw Index Time Carrier Law) :
    ∀ role : VisibleCarrierRole,
      ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
        data.roles.readsOnSelectedBundle role observer →
          (data.assembly.physicalPrinciple.selectedLaw.selection =
            observer.selection) ∧
          exactVisibleOnCut
            (observer.selection.realization.tower.π observer.selection.horizon)
            (selected_observed_law observer.selection).op ∧
          ForcedContinuumLaw
            observer.continuumClass
            data.assembly.physicalPrinciple.selectedLaw.selectedClosureLaw := by
  intro role observer hread
  exact data.carrierClosureReadout role observer hread

/-- Surface theorem for the role-indexed microscopic selected-bundle law. -/
theorem MicroscopicBundleLaw.surface
    {Index Time Carrier Law : Type}
    (data : MicroscopicBundleLaw Index Time Carrier Law) :
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
          data.roles.readsOnSelectedBundle role observer →
            (data.assembly.physicalPrinciple.selectedLaw.selection =
              observer.selection) ∧
            exactVisibleOnCut
              (observer.selection.realization.tower.π observer.selection.horizon)
              (selected_observed_law observer.selection).op ∧
            ForcedContinuumLaw
              observer.continuumClass
              data.assembly.physicalPrinciple.selectedLaw.selectedClosureLaw) := by
  obtain ⟨hbundle, hbedrock, haut, hfiber⟩ :=
    data.toSelectedBundleForcing.surface
  exact ⟨hbundle, hbedrock, haut, hfiber, data.readoutSurface⟩

/-- Detached microscopic sector law: the role-indexed microscopic bundle law
plus the intrinsic non-dictionary generation clauses needed for Step 3. -/
structure MicroscopicSectorLaw (Index Time Carrier Law : Type) where
  bundle : MicroscopicBundleLaw Index Time Carrier Law
  canonicalGeneration : SelectedBundle.CanonicalGeneration
  generatedFromIntrinsicChannelAlgebra : Prop
  minimalCompatibleRealizationsOnly : Prop
  generatedFromIntrinsicChannelAlgebra_valid :
    generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly_valid :
    minimalCompatibleRealizationsOnly

/-- The role-indexed microscopic sector law yields the detached intrinsic
sector-forcing package directly. -/
def MicroscopicSectorLaw.toIntrinsicSectorForcing
    {Index Time Carrier Law : Type}
    (data : MicroscopicSectorLaw Index Time Carrier Law) :
    IntrinsicSectorForcing Index Time Carrier Law where
  selectedBundle := data.bundle.toSelectedBundleForcing
  canonicalGeneration := data.canonicalGeneration
  generatedFromIntrinsicChannelAlgebra :=
    data.generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly :=
    data.minimalCompatibleRealizationsOnly
  generatedFromIntrinsicChannelAlgebra_valid :=
    data.generatedFromIntrinsicChannelAlgebra_valid
  minimalCompatibleRealizationsOnly_valid :=
    data.minimalCompatibleRealizationsOnly_valid

/-- Surface theorem for the role-indexed microscopic sector law: once the
role-indexed readout family and intrinsic sector-generation clauses are
supplied, the current upstream forcing surface is recovered exactly. -/
theorem MicroscopicSectorLaw.surface
    {Index Time Carrier Law : Type}
    (data : MicroscopicSectorLaw Index Time Carrier Law) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
      realized_generator_carries_bedrock_law data.bundle.bridge.generator ∧
      AutonomousHorizon
        data.bundle.bridge.selectedBridge.observer.selection.realization.tower
        data.bundle.bridge.selectedBridge.observer.selection.horizon
        data.bundle.bridge.generator ∧
      horizonFiberInvariant
        data.bundle.bridge.selectedBridge.observer.selection.realization.tower
        data.bundle.bridge.selectedBridge.observer.selection.horizon
        data.bundle.bridge.generator ∧
      (∀ role : VisibleCarrierRole,
        ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
          data.bundle.roles.readsOnSelectedBundle role observer →
            (data.bundle.assembly.physicalPrinciple.selectedLaw.selection =
              observer.selection) ∧
            exactVisibleOnCut
              (observer.selection.realization.tower.π observer.selection.horizon)
              (selected_observed_law observer.selection).op ∧
            ForcedContinuumLaw
              observer.continuumClass
              data.bundle.assembly.physicalPrinciple.selectedLaw.selectedClosureLaw) ∧
      data.generatedFromIntrinsicChannelAlgebra ∧
      data.minimalCompatibleRealizationsOnly ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  obtain ⟨hbundle, hsector, hbedrock, haut, hfiber, hgen, hmin, hprofile⟩ :=
    forcingSurface data.toIntrinsicSectorForcing
  exact
    ⟨hbundle,
      hsector,
      hbedrock,
      haut,
      hfiber,
      data.bundle.readoutSurface,
      hgen,
      hmin,
      hprofile⟩

end ClosureCurrent

end CoherenceCalculus
