import CoherenceCalculus.Foundation.AutonomyCore
import CoherenceCalculus.PartIV.ManuscriptSurfaceCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentBridgeCore

Detached bridge from the candidate closure-current law language to the active
Part IV selected-cut surface.

This file does not claim to derive a microscopic closure current from the
bedrock-certified spine. Instead it records the exact interface needed to read
the existing Part IV selected-cut completion surface in autonomy language:

* one realized exactification generator is identified with the selected visible
  law on a canonical selected Schur bridge;
* exact visibility on that cut makes the matched generator autonomous there;
* the current Part IV completion surface already packages the three direct
  visible generations, the unique geometric lift surface, and the selected
  Schur/HFT-2 exact closure surface.

The purpose is architectural honesty: the active Lean surface already closes
the selected carriers exactly once the right selected-bundle hypotheses are in
hand, but the upstream theorem that a microscopic closure-current law forces
those hypotheses is still separate work.
-/

namespace ClosureCurrent

/-- Detached bridge datum: a realized exactification generator is identified
with the currently selected visible law on one canonical selected Schur bridge.
The bedrock-carrying clause is kept explicit; this interface does not pretend
that the current Part IV surface has already derived the microscopic law. -/
structure BridgeData (Index Time Carrier Law : Type) where
  selectedBridge : CanonicalSelectedSchurBridge Index Time Carrier Law
  generator : RealizedExactificationGenerator
  carriesBedrockLaw : realized_generator_carries_bedrock_law generator
  generatorMatchesSelectedLaw :
    ∀ x : State,
      generator.toFun x =
        (selected_observed_law selectedBridge.observer.selection).op x

/-- The selected projection carried by the bridge datum. -/
def selectedProjection
    {Index Time Carrier Law : Type}
    (data : BridgeData Index Time Carrier Law) : Projection :=
  data.selectedBridge.observer.selection.realization.tower.π
    data.selectedBridge.observer.selection.horizon

/-- The selected visible law read as an additive operator on the bridge datum. -/
def selectedOperator
    {Index Time Carrier Law : Type}
    (data : BridgeData Index Time Carrier Law) : AddMap :=
  (selected_observed_law data.selectedBridge.observer.selection).op

/-- The bridge identifies the detached realized generator with the selected
visible law pointwise. -/
theorem generator_eq_selectedOperator
    {Index Time Carrier Law : Type}
    (data : BridgeData Index Time Carrier Law) :
    ∀ x : State, data.generator.toFun x = selectedOperator data x := by
  intro x
  simpa [selectedOperator] using data.generatorMatchesSelectedLaw x

/-- Exact visibility on the selected cut already forces the matched generator
to land in the observable sector. -/
theorem selectedLawVisibleOutput
    {Index Time Carrier Law : Type}
    (data : BridgeData Index Time Carrier Law) :
    ∀ x : State,
      selectedProjection data (data.generator.toFun x) = data.generator.toFun x := by
  intro x
  have hx :
      selectedOperator data x =
        selectedProjection data
          (selectedOperator data (selectedProjection data x)) := by
    simpa [selectedOperator, selectedProjection, operatorCompression_eq_blockPP]
      using data.selectedBridge.exactVisibleSelectedLaw x
  calc
    selectedProjection data (data.generator.toFun x)
        = selectedProjection data (selectedOperator data x) := by
            simpa [selectedOperator] using congrArg (selectedProjection data) (data.generatorMatchesSelectedLaw x)
    _ = selectedProjection data
          (selectedProjection data
            (selectedOperator data (selectedProjection data x))) := by
          rw [hx]
    _ = selectedProjection data
          (selectedOperator data (selectedProjection data x)) := by
          rw [(selectedProjection data).idem]
    _ = selectedOperator data x := hx.symm
    _ = data.generator.toFun x := by
          simpa [selectedOperator] using (data.generatorMatchesSelectedLaw x).symm

/-- Once the detached generator is identified with the selected visible law,
the exact-visible selected-cut law is already an autonomous scale law on that
cut. The autonomy law is the generator itself, not an extra auxiliary map. -/
theorem selectedHorizonAutonomousScale
    {Index Time Carrier Law : Type}
    (data : BridgeData Index Time Carrier Law) :
    AutonomousScaleLaw
      data.selectedBridge.observer.selection.realization.tower
      data.selectedBridge.observer.selection.horizon
      data.generator
      data.generator.toFun := by
  refine ⟨?_, ?_⟩
  · intro y
    exact selectedLawVisibleOutput data y
  · intro x
    have hx :
        selectedOperator data x =
          selectedProjection data
            (selectedOperator data (selectedProjection data x)) := by
      simpa
          [selectedOperator, selectedProjection, operatorCompression_eq_blockPP]
        using data.selectedBridge.exactVisibleSelectedLaw x
    have hPx :
        selectedOperator data (selectedProjection data x) =
          selectedProjection data
            (selectedOperator data (selectedProjection data x)) := by
      have hvis :=
        data.selectedBridge.exactVisibleSelectedLaw
          (selectedProjection data x)
      have hraw :
          selectedOperator data (selectedProjection data x) =
            selectedProjection data
              (selectedOperator data
                (selectedProjection data (selectedProjection data x))) := by
        simpa
            [selectedOperator, selectedProjection, operatorCompression_eq_blockPP]
          using hvis
      calc
        selectedOperator data (selectedProjection data x)
            = selectedProjection data
                (selectedOperator data
                  (selectedProjection data (selectedProjection data x))) := hraw
        _ = selectedProjection data
              (selectedOperator data (selectedProjection data x)) := by
              rw [(selectedProjection data).idem]
    calc
      selectedProjection data (data.generator.toFun x) = data.generator.toFun x := by
        exact selectedLawVisibleOutput data x
      _ = selectedOperator data x := by
        simpa [selectedOperator] using data.generatorMatchesSelectedLaw x
      _ =
          selectedProjection data
            (selectedOperator data (selectedProjection data x)) := hx
      _ = selectedOperator data (selectedProjection data x) := hPx.symm
      _ = data.generator.toFun (selectedProjection data x) := by
        simpa [selectedOperator] using
          (data.generatorMatchesSelectedLaw (selectedProjection data x)).symm

/-- The selected cut is autonomous for the matched realized generator. -/
theorem selectedHorizonAutonomous
    {Index Time Carrier Law : Type}
    (data : BridgeData Index Time Carrier Law) :
    AutonomousHorizon
      data.selectedBridge.observer.selection.realization.tower
      data.selectedBridge.observer.selection.horizon
      data.generator := by
  exact ⟨data.generator.toFun, selectedHorizonAutonomousScale data⟩

/-- The matched selected generator therefore satisfies the autonomy criterion
on the selected cut: projected evolution depends only on selected visible data.
-/
theorem selectedHorizonFiberInvariant
    {Index Time Carrier Law : Type}
    (data : BridgeData Index Time Carrier Law) :
    horizonFiberInvariant
      data.selectedBridge.observer.selection.realization.tower
      data.selectedBridge.observer.selection.horizon
      data.generator := by
  exact
    (autonomy_criterion_uniqueness
      data.selectedBridge.observer.selection.realization.tower
      data.selectedBridge.observer.selection.horizon
      data.generator).mp (selectedHorizonAutonomous data)

/-- Any other autonomous scale law on the same selected cut agrees with the
matched generator on projection-fixed states. -/
theorem selectedAutonomousLaw_unique
    {Index Time Carrier Law : Type}
    (data : BridgeData Index Time Carrier Law)
    {L : State → State}
    (hL :
      AutonomousScaleLaw
        data.selectedBridge.observer.selection.realization.tower
        data.selectedBridge.observer.selection.horizon
        data.generator
        L) :
    ∀ y : State,
      selectedProjection data y = y →
        L y = data.generator.toFun y := by
  intro y hy
  exact
    autonomous_scale_law_unique
      data.selectedBridge.observer.selection.realization.tower
      data.selectedBridge.observer.selection.horizon
      data.generator
      hL
      (selectedHorizonAutonomousScale data)
      y
      hy

/-- The detached closure-current bridge carries exactly the current autonomy
surface that can already be read on the selected cut. -/
theorem bridgeSurface
    {Index Time Carrier Law : Type}
    (data : BridgeData Index Time Carrier Law) :
    realized_generator_carries_bedrock_law data.generator ∧
      AutonomousHorizon
        data.selectedBridge.observer.selection.realization.tower
        data.selectedBridge.observer.selection.horizon
        data.generator ∧
      horizonFiberInvariant
        data.selectedBridge.observer.selection.realization.tower
        data.selectedBridge.observer.selection.horizon
        data.generator := by
  exact
    ⟨data.carriesBedrockLaw,
      selectedHorizonAutonomous data,
      selectedHorizonFiberInvariant data⟩

/-- On the active Lean surface, the first proof obligation already closes up
to the present selected-bundle language: the intrinsic `[3,2,1]` profile is
forced, the three direct visible generations are fixed, and no primitive
dictionary is introduced. What is still separate is the upstream theorem that
every microscopic closure current forces exactly this surface. -/
theorem threePrimitiveDirectSurface
    {Time Carrier Law : Type}
    (data : NaturalOperatorCompletion Time Carrier Law) :
    natListSum [3, 2, 1] = balancedClosureSlotCount closureStableDimension ∧
      IsCanonicalLogicalProfile [3, 2, 1] ∧
      data.sectorGeneration.generatedFromIntrinsicChannelAlgebra ∧
      data.sectorGeneration.scalarChannelGeneratesPhase ∧
      data.sectorGeneration.scalarChannelGeneratesWave ∧
      data.sectorGeneration.exactOneFormExchangeGeneratesGauge ∧
      data.sectorGeneration.notPrimitiveDictionary ∧
      data.phaseRepresentativeClassified ∧
      data.waveRepresentativeClassified ∧
      data.gaugeRepresentativeClassified := by
  obtain ⟨hsum, hprofile⟩ := forced_intrinsic_channel_profile
  have hchannels := IntrinsicSectorGeneration.primitiveChannels data.sectorGeneration
  rcases hchannels with ⟨hphase, hwave, hgauge, hnotDict⟩
  exact
    ⟨hsum,
      hprofile,
      data.sectorGeneration.generatedFromIntrinsicChannelAlgebra_valid,
      hphase,
      hwave,
      hgauge,
      hnotDict,
      data.phaseRepresentativeClassified_valid,
      data.waveRepresentativeClassified_valid,
      data.gaugeRepresentativeClassified_valid⟩

/-- On the active Lean surface, the second proof obligation already closes as
the unique geometric-lift package: once phase, wave, and gauge have already
been classified and a primitive-three bilinear lift witness is supplied,
geometry is exactly the remaining intrinsic symmetric-response lift. -/
theorem primitiveThreeUniqueLiftSurface
    {Time Carrier Law Tensor Scalar Group : Type}
    (completion : NaturalOperatorCompletion Time Carrier Law)
    (lift :
      GeometricWitness.PrimitiveThreePackage
        Time Carrier Law Tensor Scalar Group) :
    Nonempty
        (GeometricWitness.SquarePackage
          Time Carrier Law Tensor Scalar Group) ∧
      completion.sectorGeneration.symmetricResponseGeneratesGeometry ∧
      completion.sectorGeneration.notPrimitiveDictionary ∧
      completion.phaseRepresentativeClassified ∧
      completion.waveRepresentativeClassified ∧
      completion.gaugeRepresentativeClassified ∧
      completion.geometricRepresentativeClassified := by
  have hderived :=
    SelectedSchur.derivedGeometricLift completion.sectorGeneration lift
  have hremaining :=
    IntrinsicSectorGeneration.remainingGeometricLane
      completion.sectorGeneration
      completion
  rcases hderived with ⟨hsquare, hgeom, hnotDict⟩
  rcases hremaining with ⟨hphase, hwave, hgauge, _hgeom'⟩
  exact
    ⟨hsquare,
      hgeom,
      hnotDict,
      hphase,
      hwave,
      hgauge,
      completion.geometricRepresentativeClassified_valid⟩

/-- The third proof obligation is already present verbatim on the active Lean
surface: the canonical selected Schur bridge and HFT-2 close the generated
selected carriers exactly on one selected datum. -/
theorem selectedSchurHFT2ClosureSurface
    {Index Time Carrier Law : Type}
    (bridge : SelectedSchur.Package Index Time Carrier Law) :
    exactVisibleOnCut
        (bridge.observer.selection.realization.tower.π
          bridge.observer.selection.horizon)
        (selected_observed_law bridge.observer.selection).op ∧
      bridge.groundedBridge.physicalPrinciple.intrinsicallyClosedOnLeastMotionCut ∧
      bridge.groundedBridge.physicalPrinciple.noExogenousConstitutiveCompletion ∧
      bridge.groundedBridge.physicalPrinciple.apparentConstitutiveTermsAreReturnedResidual ∧
      (returnedResidual (canonicalSelectedResidualReturnField bridge) =
        schurComplement
          (bridge.observer.selection.realization.tower.π
            bridge.observer.selection.horizon)
          (selected_observed_law bridge.observer.selection).op
          (canonicalSelectedShadowPropagator bridge)) ∧
      (∀ x : State,
        (selected_observed_law bridge.observer.selection).op x =
          State.add
            (blockPP
              (bridge.observer.selection.realization.tower.π
                bridge.observer.selection.horizon)
              ((selected_observed_law bridge.observer.selection).op) x)
            (returnedResidual (canonicalSelectedResidualReturnField bridge) x)) ∧
      (∀ x : State,
        canonicalSelectedResidualStock bridge x =
          canonicalSelectedReturnFlux bridge x +
            unrecoveredResidualStock bridge.energyTower x
              (bridge.observer.selection.horizon + 1)) ∧
      (∀ h : Nat, ∀ x : State,
        unrecoveredResidualStock bridge.energyTower x (h + 1) ≤
          unrecoveredResidualStock bridge.energyTower x h) ∧
      (holographicImbalance 3 = SignedCount.ofNat 1) ∧
      IsCanonicalLogicalProfile [3, 2, 1] ∧
      SelectedCutOrthogonality.exactSplit bridge := by
  have hreal := SelectedSchur.derivedRealization bridge
  have horth := SelectedCutOrthogonality.exact bridge
  rcases hreal with
    ⟨_hproj, _hcut, _hforcing, _hmin, hvis, hclosed, hnoConst, hreturned,
      hret, hsplit, hstep, hmono, hd3, hprofile⟩
  exact
    ⟨hvis,
      hclosed,
      hnoConst,
      hreturned,
      hret,
      hsplit,
      hstep,
      hmono,
      hd3,
      hprofile,
      horth⟩

/-- Compact bridge theorem: if one supplies a detached closure-current bridge
on the same selected datum as the active completion package, then the active
Lean surface already gives the current autonomy and selected-cut completion
surfaces together without any additional carrier-side law. -/
theorem completionBridgeSurface
    {Time Carrier Law : Type}
    (completion : NaturalOperatorCompletion Time Carrier Law)
    (current :
      BridgeData completion.sectorGeneration.selectedBundle.Index Time Carrier Law)
    (hsame :
      completion.sectorGeneration.selectedBundle.selectedSchurBridge =
        current.selectedBridge) :
    completion.sectorGeneration.selectedBundle.selectedSchurBridge =
        current.selectedBridge ∧
      realized_generator_carries_bedrock_law current.generator ∧
      AutonomousHorizon
        current.selectedBridge.observer.selection.realization.tower
        current.selectedBridge.observer.selection.horizon
        current.generator ∧
      PartIVLawCompletionStatement completion := by
  exact
    ⟨hsame,
      current.carriesBedrockLaw,
      selectedHorizonAutonomous current,
      partIV_law_completion completion⟩

end ClosureCurrent

end CoherenceCalculus
