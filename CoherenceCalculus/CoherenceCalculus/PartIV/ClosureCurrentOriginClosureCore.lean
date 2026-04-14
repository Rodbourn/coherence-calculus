import CoherenceCalculus.PartIV.ClosureCurrentLocalEventCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentOriginClosureCore

Explicit theorem targets above the smaller microscopic closure law.

`ClosureCurrentLocalEventCore` isolates one smaller primitive
`MicroscopicClosureLaw` and the explicit witness packages that would need to be
recovered to close the present upstream seam. This file turns that statement
into theorem-level targets rather than prose:

* `OriginClosureTarget law` is the theorem target that the selected-bundle and
  role-readout witness is forced from `law`;
* `SectorClosureTarget law` is the theorem target that the intrinsic
  non-dictionary sector package is forced once origin closure is in hand;
* once those witness targets are supplied, the detached selected-bundle and
  Step 3 forcing surfaces are recovered exactly.

Nothing here claims those targets are already proved. The purpose is to state
the missing microscopic closure theorems in the same explicit language as the
existing detached Part IV interfaces.
-/

namespace ClosureCurrent

/-- The theorem target saying that one smaller microscopic closure law already
forces the selected-bundle and role-readout witness package. -/
def OriginClosureTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) : Prop :=
  Nonempty (OriginClosureWitness law)

/-- The theorem target saying that, once origin closure is in hand, the same
microscopic law forces the intrinsic non-dictionary sector-generation package.
-/
def SectorClosureTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) : Prop :=
  ∀ _origin : OriginClosureWitness law, Nonempty (SectorOriginWitness law)

/-- Repackage an origin-closure witness as the role-indexed microscopic
selected-bundle law used by the forcing layer. -/
def OriginClosureWitness.toMicroscopicBundleLaw
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : OriginClosureWitness law) :
    MicroscopicBundleLaw Index Time Carrier Law where
  bridge := law.bridge
  assembly := data.toBundleAssemblyLaw
  sameSelectedLawAsBridge := law.sameSelectedLawAsBridge
  roles := data.toRoleReadoutFamily
  continuumClosure := data.toClosureClassTransport
  bundleArisesIntrinsicallyOnLeastMotionCut :=
    data.bundleArisesIntrinsicallyOnLeastMotionCut
  noCarrierWiseVisibilityHypotheses :=
    data.noCarrierWiseVisibilityHypotheses
  bundleArisesIntrinsicallyOnLeastMotionCut_valid :=
    data.bundleArisesIntrinsicallyOnLeastMotionCut_valid
  noCarrierWiseVisibilityHypotheses_valid :=
    data.noCarrierWiseVisibilityHypotheses_valid

/-- Repackage an origin-closure witness directly as the detached selected-bundle
forcing package. -/
def OriginClosureWitness.toSelectedBundleForcing
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : OriginClosureWitness law) :
    SelectedBundleForcing Index Time Carrier Law :=
  data.toMicroscopicBundleLaw.toSelectedBundleForcing

/-- Once the origin-closure witness exists, the role-indexed microscopic
selected-bundle surface is already recovered exactly. -/
theorem OriginClosureWitness.microscopicSurface
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : OriginClosureWitness law) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      realized_generator_carries_bedrock_law law.bridge.generator ∧
      AutonomousHorizon
        law.bridge.selectedBridge.observer.selection.realization.tower
        law.bridge.selectedBridge.observer.selection.horizon
        law.bridge.generator ∧
      horizonFiberInvariant
        law.bridge.selectedBridge.observer.selection.realization.tower
        law.bridge.selectedBridge.observer.selection.horizon
        law.bridge.generator ∧
      (∀ role : VisibleCarrierRole,
        ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
          data.readsRoleOnSelectedBundle role observer →
            (law.physicalPrinciple.selectedLaw.selection =
              observer.selection) ∧
            exactVisibleOnCut
              (observer.selection.realization.tower.π observer.selection.horizon)
              (selected_observed_law observer.selection).op ∧
            ForcedContinuumLaw
              observer.continuumClass
              law.physicalPrinciple.selectedLaw.selectedClosureLaw) := by
  simpa [OriginClosureWitness.toMicroscopicBundleLaw] using
    data.toMicroscopicBundleLaw.surface

/-- Once the origin-closure witness exists, the detached selected-bundle forcing
surface is already recovered exactly. -/
theorem OriginClosureWitness.forcingSurface
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : OriginClosureWitness law) :
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
  simpa [OriginClosureWitness.toSelectedBundleForcing] using
    data.toSelectedBundleForcing.surface

/-- Repackage the sector witness as the role-indexed microscopic sector law used
by the forcing layer. -/
def SectorOriginWitness.toMicroscopicSectorLaw
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (origin : OriginClosureWitness law)
    (data : SectorOriginWitness law) :
    MicroscopicSectorLaw Index Time Carrier Law where
  bundle := origin.toMicroscopicBundleLaw
  canonicalGeneration := data.canonicalGeneration
  generatedFromIntrinsicChannelAlgebra :=
    data.generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly :=
    data.minimalCompatibleRealizationsOnly
  generatedFromIntrinsicChannelAlgebra_valid :=
    data.generatedFromIntrinsicChannelAlgebra_valid
  minimalCompatibleRealizationsOnly_valid :=
    data.minimalCompatibleRealizationsOnly_valid

/-- Repackage the sector witness directly as the detached intrinsic-sector
forcing package. -/
def SectorOriginWitness.toIntrinsicSectorForcing
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (origin : OriginClosureWitness law)
    (data : SectorOriginWitness law) :
    IntrinsicSectorForcing Index Time Carrier Law :=
  data.toMicroscopicSectorLaw origin |>.toIntrinsicSectorForcing

/-- Once origin closure and sector closure exist, the role-indexed microscopic
sector surface is already recovered exactly. -/
theorem SectorOriginWitness.microscopicSurface
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (origin : OriginClosureWitness law)
    (data : SectorOriginWitness law) :
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
      (∀ role : VisibleCarrierRole,
        ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
          origin.readsRoleOnSelectedBundle role observer →
            (law.physicalPrinciple.selectedLaw.selection =
              observer.selection) ∧
            exactVisibleOnCut
              (observer.selection.realization.tower.π observer.selection.horizon)
              (selected_observed_law observer.selection).op ∧
            ForcedContinuumLaw
              observer.continuumClass
              law.physicalPrinciple.selectedLaw.selectedClosureLaw) ∧
      data.generatedFromIntrinsicChannelAlgebra ∧
      data.minimalCompatibleRealizationsOnly ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  simpa [SectorOriginWitness.toMicroscopicSectorLaw] using
    data.toMicroscopicSectorLaw origin |>.surface

/-- Once origin closure and sector closure exist, the detached Step 3 forcing
surface is already recovered exactly. -/
theorem SectorOriginWitness.forcingSurface
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (origin : OriginClosureWitness law)
    (data : SectorOriginWitness law) :
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
      data.generatedFromIntrinsicChannelAlgebra ∧
      data.minimalCompatibleRealizationsOnly ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  simpa [SectorOriginWitness.toIntrinsicSectorForcing] using
    CoherenceCalculus.ClosureCurrent.forcingSurface
      (data.toIntrinsicSectorForcing origin)

/-- If the origin-closure theorem target is met for a microscopic closure law,
the detached selected-bundle forcing surface follows immediately. -/
theorem MicroscopicClosureLaw.originTargetSurface
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (horigin : OriginClosureTarget law) :
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
  rcases horigin with ⟨origin⟩
  exact origin.forcingSurface

/-- If both origin closure and sector closure targets are met for a microscopic
closure law, the detached Step 3 forcing surface follows immediately. -/
theorem MicroscopicClosureLaw.sectorTargetSurface
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (horigin : OriginClosureTarget law)
    (hsector : SectorClosureTarget law) :
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
  rcases horigin with ⟨origin⟩
  rcases hsector origin with ⟨sector⟩
  obtain ⟨hbundle, hstep3, hbedrock, haut, hfiber, hgen, hmin, hprofile⟩ :=
    sector.forcingSurface origin
  exact
    ⟨hbundle,
      hstep3,
      hbedrock,
      haut,
      hfiber,
      ⟨sector.generatedFromIntrinsicChannelAlgebra,
        sector.minimalCompatibleRealizationsOnly,
        hgen,
        hmin⟩,
      hprofile⟩

end ClosureCurrent

end CoherenceCalculus
