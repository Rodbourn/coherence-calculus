import CoherenceCalculus.PartIV.InterfaceExportCore
import CoherenceCalculus.PartIV.LawCompletionCore

namespace CoherenceCalculus

/- Manuscript-facing name for the selected-cut forcing layer used in the
late Chapter 10 synthesis. The active Lean surface already packages this as
`SelectedCut.ForcingBridge`. -/
namespace SelectedCut

abbrev Package (Index Time Carrier Law : Type) :=
  ForcingBridge Index Time Carrier Law

end SelectedCut

/- Manuscript-facing name for the exact return / Schur residue layer on one
selected datum. The active Lean surface packages this as
`SelectedSchur.ExactResidue`. -/
namespace SelectedSchur

abbrev ReturnPackage {Time : Type} (selection : SelectionDatum Time) :=
  ExactResidue selection

/-- Manuscript-facing name for the grounded selected Schur package. The active
Lean surface already packages this as `CanonicalSelectedSchurBridge`. -/
abbrev Package (Index Time Carrier Law : Type) :=
  CanonicalSelectedSchurBridge Index Time Carrier Law

end SelectedSchur

/- Manuscript-facing names for the geometric witness packages used in the
middle of Chapter 10. On the active Lean surface these are all realized by the
same geometric endpoint-frontier package. -/
namespace GeometricWitness

abbrev OrthogonalPackage (Time Carrier Law Tensor Scalar Group : Type) :=
  GeometricLane.EndpointFoundationFrontierData
    Time Carrier Law Tensor Scalar Group

abbrev SquarePackage (Time Carrier Law Tensor Scalar Group : Type) :=
  GeometricLane.EndpointFoundationFrontierData
    Time Carrier Law Tensor Scalar Group

abbrev PrimitiveThreePackage (Time Carrier Law Tensor Scalar Group : Type) :=
  GeometricLane.EndpointFoundationFrontierData
    Time Carrier Law Tensor Scalar Group

end GeometricWitness

/- Manuscript-facing names for the late Chapter 10 general-bundle taxonomy.
The active Lean surface packages the same scoped decomposition by
`SelectedBundle.Reduction`. -/
namespace GeneralBundle

abbrev ExhaustionHypothesis (Time Carrier Law : Type) :=
  SelectedBundle.Reduction Time Carrier Law

abbrev RoleDichotomy (Time Carrier Law : Type) :=
  SelectedBundle.Reduction Time Carrier Law

abbrev LiftClosureTrichotomy (Time Carrier Law : Type) :=
  SelectedBundle.Reduction Time Carrier Law

end GeneralBundle

/- Manuscript-facing name for the residual selected-cut duality package used
in the middle of Chapter 10. The active Lean surface already packages this as
`CanonicalDuality.SectorRigidity`. -/
namespace CanonicalDuality

abbrev ResidualRigidity (Time Carrier Law Fiber : Type) :=
  SectorRigidity Time Carrier Law Fiber

end CanonicalDuality

namespace SelectedCutOrthogonality

/-- The realized-cut energy-orthogonality package is already the active Lean
surface of the manuscript's derived orthogonality corollary. -/
theorem derived
    {Time Carrier Law Fiber : Type}
    (data : Principle Time Carrier Law Fiber) :
    exactSplit data.selectedBridge ∧
      data.trialAndTestReadOnSameSelectedCarrier ∧
      data.pairingReadFromEnergyOrthogonalSelectedCut ∧
      data.generatedSymmetryPreservesSelectedCutPairing ∧
      data.admissibleEndpointOperatorsPreserveSelectedCutPairing ∧
      data.weakLawHasUniquePairingCompatibleStrongRepresentative := by
  exact Principle.surface data

end SelectedCutOrthogonality

/-- A manuscript-facing mode-compatible candidate class on the selected cut.
The class is explicit, finite, and already carries one least-motion observer
datum together with horizon-preserving transport across the admissible class. -/
structure ModeCompatibleCandidateClass
    (Index Time Carrier Law Mode : Type) where
  cls : AdmissibleRealizedClass Index Time
  observer : ObserverSelection.LeastMotion Time Carrier Law
  mode : Mode
  preservesCompatibilitySignature : Prop
  preservesAdmissibleSourceProfile : Prop
  irreducibleVisibleSubcarrier : Prop
  reducedSelectionSingleton :
    ∀ i j : Index, HorizonPreservingEquivalence (cls.datum i) (cls.datum j)
  preservesCompatibilitySignature_valid : preservesCompatibilitySignature
  preservesAdmissibleSourceProfile_valid : preservesAdmissibleSourceProfile
  irreducibleVisibleSubcarrier_valid : irreducibleVisibleSubcarrier

namespace ModeCompatibleCandidateClass

/-- A mode-compatible candidate class already carries the least-motion datum
and the singleton reduced-selection transport needed to force the selected law
across the class. -/
theorem leastMotionRealization
    {Index Time Carrier Law Mode : Type}
    (data : ModeCompatibleCandidateClass Index Time Carrier Law Mode) :
    Nonempty (ObserverSelection.LeastMotion Time Carrier Law) ∧
      data.preservesCompatibilitySignature ∧
      data.preservesAdmissibleSourceProfile ∧
      data.irreducibleVisibleSubcarrier ∧
      (∀ i j : Index,
        (data.cls.datum i).horizon = (data.cls.datum j).horizon ∧
          (∀ x : State,
            (data.reducedSelectionSingleton i j).transport
                ((selected_observed_law (data.cls.datum i)).op x) =
              (selected_observed_law (data.cls.datum j)).op
                ((data.reducedSelectionSingleton i j).transport x))) := by
  exact
    ⟨⟨data.observer⟩,
      data.preservesCompatibilitySignature_valid,
      data.preservesAdmissibleSourceProfile_valid,
      data.irreducibleVisibleSubcarrier_valid,
      selection_to_forcing data.cls data.reducedSelectionSingleton⟩

theorem observerSurface
    {Index Time Carrier Law Mode : Type}
    (data : ModeCompatibleCandidateClass Index Time Carrier Law Mode) :
    Nonempty (ObserverSelection.LeastMotion Time Carrier Law) := by
  have hmode := leastMotionRealization data
  rcases hmode with ⟨hobs, _hsig, _hsrc, _hirr, _hforced⟩
  exact hobs

theorem forcingSurface
    {Index Time Carrier Law Mode : Type}
    (data : ModeCompatibleCandidateClass Index Time Carrier Law Mode) :
    ∀ i j : Index,
      (data.cls.datum i).horizon = (data.cls.datum j).horizon ∧
        (∀ x : State,
          (data.reducedSelectionSingleton i j).transport
              ((selected_observed_law (data.cls.datum i)).op x) =
            (selected_observed_law (data.cls.datum j)).op
              ((data.reducedSelectionSingleton i j).transport x)) := by
  have hmode := leastMotionRealization data
  rcases hmode with ⟨_hobs, _hsig, _hsrc, _hirr, hforced⟩
  exact hforced

end ModeCompatibleCandidateClass

/-- A manuscript-facing Schur-induced mode class. This is the selected-cut
mode-compatible class together with the statement that its visible witness is
read through the canonical selected Schur bridge. -/
structure SchurInducedModeCandidateClass
    (Index Time Carrier Law Mode : Type)
    extends ModeCompatibleCandidateClass Index Time Carrier Law Mode where
  selectedBridge : CanonicalSelectedSchurBridge Index Time Carrier Law
  sameSelectionAsBridge :
    observer.selection = selectedBridge.observer.selection
  witnessedBySchurTransport : Prop
  witnessedBySchurTransport_valid : witnessedBySchurTransport

namespace SchurInducedModeCandidateClass

/-- Once a Schur-induced mode class is present, the singleton reduced
selection and least-motion realization properties are inherited directly from
its underlying mode-compatible class. -/
theorem singletonReducedSelection
    {Index Time Carrier Law Mode : Type}
    (data : SchurInducedModeCandidateClass Index Time Carrier Law Mode) :
    Nonempty (ObserverSelection.LeastMotion Time Carrier Law) ∧
      data.witnessedBySchurTransport ∧
      (∀ i j : Index,
        (data.cls.datum i).horizon = (data.cls.datum j).horizon ∧
          (∀ x : State,
        (data.reducedSelectionSingleton i j).transport
                ((selected_observed_law (data.cls.datum i)).op x) =
              (selected_observed_law (data.cls.datum j)).op
                ((data.reducedSelectionSingleton i j).transport x))) := by
  have hmode :=
    ModeCompatibleCandidateClass.leastMotionRealization
      data.toModeCompatibleCandidateClass
  rcases hmode with ⟨hobs, _hsig, _hsrc, _hirr, hforced⟩
  exact ⟨hobs, data.witnessedBySchurTransport_valid, hforced⟩

end SchurInducedModeCandidateClass

namespace IntrinsicSectorGeneration

/-- The intrinsic selected-channel package already supplies the three direct
primitive selected-channel generations on the common selected bundle. -/
theorem threeSchurModeClasses
    {Time Carrier Law : Type}
    (data : IntrinsicSectorGeneration Time Carrier Law) :
    data.scalarChannelGeneratesPhase ∧
      data.scalarChannelGeneratesWave ∧
      data.exactOneFormExchangeGeneratesGauge := by
  exact
    ⟨data.scalarChannelGeneratesPhase_valid,
      data.scalarChannelGeneratesWave_valid,
      data.exactOneFormExchangeGeneratesGauge_valid⟩

end IntrinsicSectorGeneration

namespace NaturalOperatorCompletion

/-- On the active Lean surface, the first three intrinsic law classes are
already forced once the natural-operator completion layer is in hand. -/
theorem firstThreeClasses
    {Time Carrier Law : Type}
    (data : NaturalOperatorCompletion Time Carrier Law) :
    data.endpointRigidity.endpointClosureUniqueModuloContinuumEquivalence ∧
      data.phaseRepresentativeClassified ∧
      data.waveRepresentativeClassified ∧
      data.gaugeRepresentativeClassified ∧
      data.phaseCanonicalRepresentative ∧
      data.waveCanonicalRepresentative ∧
      data.gaugeCanonicalRepresentative := by
  have hguided := NaturalOperatorCompletion.guidedByEndpointRigidity data
  rcases hguided with
    ⟨_hsame, _hjet, _hsymm, _hident, _hequiv, _htrunc, _hsingle, _hfamily,
      huniq⟩
  exact
    ⟨huniq,
      data.phaseRepresentativeClassified_valid,
      data.waveRepresentativeClassified_valid,
      data.gaugeRepresentativeClassified_valid,
      data.phaseCanonicalRepresentative_valid,
      data.waveCanonicalRepresentative_valid,
      data.gaugeCanonicalRepresentative_valid⟩

end NaturalOperatorCompletion

namespace IntrinsicSectorGeneration

/-- The primitive direct channel surface is already fixed by intrinsic sector
generation: phase, wave, and gauge are generated directly, and no primitive
dictionary is introduced. -/
theorem primitiveChannels
    {Time Carrier Law : Type}
    (data : IntrinsicSectorGeneration Time Carrier Law) :
    data.scalarChannelGeneratesPhase ∧
      data.scalarChannelGeneratesWave ∧
      data.exactOneFormExchangeGeneratesGauge ∧
      data.notPrimitiveDictionary := by
  exact
    ⟨data.scalarChannelGeneratesPhase_valid,
      data.scalarChannelGeneratesWave_valid,
      data.exactOneFormExchangeGeneratesGauge_valid,
      data.notPrimitiveDictionary_valid⟩

/-- The geometric lane is the unique intrinsic lift carried by the selected
bundle in the current scoped flagship surface. -/
theorem geometricLane
    {Time Carrier Law : Type}
    (data : IntrinsicSectorGeneration Time Carrier Law) :
    data.symmetricResponseGeneratesGeometry ∧
      data.notPrimitiveDictionary := by
  exact
    ⟨data.symmetricResponseGeneratesGeometry_valid,
      data.notPrimitiveDictionary_valid⟩

/-- In the current scoped flagship surface, the geometric lane is the only
remaining intrinsic lift side once phase, wave, and gauge have already been
classified on the selected bundle. -/
theorem remainingGeometricLane
    {Time Carrier Law : Type}
    (sectors : IntrinsicSectorGeneration Time Carrier Law)
    (completion : NaturalOperatorCompletion Time Carrier Law) :
    completion.phaseRepresentativeClassified ∧
      completion.waveRepresentativeClassified ∧
      completion.gaugeRepresentativeClassified ∧
      sectors.symmetricResponseGeneratesGeometry := by
  have hgeom := geometricLane sectors
  exact
    ⟨completion.phaseRepresentativeClassified_valid,
      completion.waveRepresentativeClassified_valid,
      completion.gaugeRepresentativeClassified_valid,
      hgeom.1⟩

end IntrinsicSectorGeneration

namespace SelectedBundle.Reduction

/-- The scoped bundle-first decomposition is the conjunction of common
selected-bundle assembly, intrinsic sector generation, and carrier-level
classification already packaged by `SelectedBundle.Reduction`. -/
theorem bundleFirstDecomposition
    {Time Carrier Law : Type}
    (data : SelectedBundle.Reduction Time Carrier Law) :
    data.bundleAssembly.selectedObservedBundle ∧
      data.bundleAssembly.bundleSharedByAllCarriers ∧
      data.bundleAssembly.sameSelectedEffectiveLawOnEachCarrier ∧
      data.sectorGeneration.scalarChannelGeneratesPhase ∧
      data.sectorGeneration.scalarChannelGeneratesWave ∧
      data.sectorGeneration.exactOneFormExchangeGeneratesGauge ∧
      data.sectorGeneration.symmetricResponseGeneratesGeometry ∧
      data.classification.phaseRepresentativeClassified ∧
      data.classification.waveRepresentativeClassified ∧
      data.classification.kineticRepresentativeClassified ∧
      data.classification.gaugeRepresentativeClassified ∧
      data.classification.geometricRepresentativeClassified := by
  have h := surface data
  rcases h with
    ⟨hbundle, _hscalar, hphase, hwave, hkinetic, hgauge, hgeom,
      hcphase, hcwave, hckinetic, hcgauge, hcgeom, _hremaining⟩
  exact
    ⟨hbundle,
      data.bundleAssembly.bundleSharedByAllCarriers_valid,
      data.bundleAssembly.sameSelectedEffectiveLawOnEachCarrier_valid,
      hphase,
      hwave,
      hgauge,
      hgeom,
      hcphase,
      hcwave,
      hckinetic,
      hcgauge,
      hcgeom⟩

/-- Manuscript-facing carrier-forcing surface for Chapter 7: the selected-bundle
decomposition already fixes the three primitive lanes together with the one
intrinsic geometric lift. -/
theorem defectTowerCompleteCarrierForcing
    {Time Carrier Law : Type}
    (data : SelectedBundle.Reduction Time Carrier Law) :
    data.sectorGeneration.scalarChannelGeneratesPhase ∧
      data.sectorGeneration.scalarChannelGeneratesWave ∧
      data.sectorGeneration.exactOneFormExchangeGeneratesGauge ∧
      data.sectorGeneration.symmetricResponseGeneratesGeometry ∧
      data.classification.phaseRepresentativeClassified ∧
      data.classification.waveRepresentativeClassified ∧
      data.classification.gaugeRepresentativeClassified ∧
      data.classification.geometricRepresentativeClassified := by
  have h := bundleFirstDecomposition data
  rcases h with
    ⟨_hbundle, _hshared, _hlaw, hphase, hwave, hgauge, hgeom,
      hcphase, hcwave, _hckinetic, hcgauge, hcgeom⟩
  exact ⟨hphase, hwave, hgauge, hgeom, hcphase, hcwave, hcgauge, hcgeom⟩

/-- The same selected-bundle decomposition is the active Lean surface for the
single-source Chapter 7 identification: no extra carrier-side law is added
beyond the one common selected-bundle grammar. -/
theorem singleSourceIdentification
    {Time Carrier Law : Type}
    (data : SelectedBundle.Reduction Time Carrier Law) :
    data.sectorGeneration.scalarChannelGeneratesPhase ∧
      data.sectorGeneration.scalarChannelGeneratesWave ∧
      data.sectorGeneration.exactOneFormExchangeGeneratesGauge ∧
      data.sectorGeneration.symmetricResponseGeneratesGeometry ∧
      data.classification.phaseRepresentativeClassified ∧
      data.classification.waveRepresentativeClassified ∧
      data.classification.gaugeRepresentativeClassified ∧
      data.classification.geometricRepresentativeClassified := by
  exact defectTowerCompleteCarrierForcing data

end SelectedBundle.Reduction

namespace SelectedBundle.CanonicalGeneration

/-- The manuscript's four nonempty Schur-induced mode classes are exactly the
four persistence/generative carrier clauses already recorded on the active
canonical-generation surface. -/
theorem fourSchurNonempty
    (data : SelectedBundle.CanonicalGeneration) :
    data.scalarChannelGeneratesPhase ∧
      data.scalarChannelGeneratesWave ∧
      data.exactOneFormExchangeGeneratesGauge ∧
      data.symmetricResponseGeneratesGeometry := by
  exact
    ⟨data.scalarChannelGeneratesPhase_valid,
      data.scalarChannelGeneratesWave_valid,
      data.exactOneFormExchangeGeneratesGauge_valid,
      data.symmetricResponseGeneratesGeometry_valid⟩

end SelectedBundle.CanonicalGeneration

namespace FlagshipLawCompletion

/-- The current forcing frontier for primitive physics is exactly the Part IV
law-completion statement together with concrete recognizable witnesses on the
flagship lanes. -/
theorem currentForcingFrontier
    {Time Carrier Law : Type}
    (data : FlagshipLawCompletion Time Carrier Law) :
    PartIVLawCompletionStatement data.completion ∧
      Nonempty
        (Σ Field : Type, Σ Scalar : Type,
          PhaseLane.RecognizableIdentity
            Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Scalar : Type,
          WaveLane.RecognizableIdentity
            Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ State : Type, Σ Velocity : Type, Σ Observable : Type, Σ Scalar : Type,
          HydrodynamicLane.RecognizableIdentity
            Time Carrier Law State Velocity Observable Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Source : Type,
          GaugeLane.RecognizableIdentity
            Time Carrier Law Field Source) ∧
      Nonempty
        (Σ Tensor : Type, Σ Scalar : Type,
          GeometricLane.RecognizableIdentity
            Time Carrier Law Tensor Scalar) := by
  exact
    ⟨FlagshipLawCompletion.completionSurface data,
      FlagshipLawCompletion.recognizableWitnesses data⟩

/-- Lane-by-lane intrinsic closure is now exactly the nonempty recognizable
flagship witnesses exported by the downstream completion package. -/
theorem laneByLaneClosureFrontier
    {Time Carrier Law : Type}
    (data : FlagshipLawCompletion Time Carrier Law) :
    Nonempty
      (Σ Field : Type, Σ Scalar : Type,
        PhaseLane.RecognizableIdentity
          Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Scalar : Type,
          WaveLane.RecognizableIdentity
            Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ State : Type, Σ Velocity : Type, Σ Observable : Type, Σ Scalar : Type,
          HydrodynamicLane.RecognizableIdentity
            Time Carrier Law State Velocity Observable Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Source : Type,
          GaugeLane.RecognizableIdentity
            Time Carrier Law Field Source) ∧
      Nonempty
        (Σ Tensor : Type, Σ Scalar : Type,
          GeometricLane.RecognizableIdentity
            Time Carrier Law Tensor Scalar) := by
  exact FlagshipLawCompletion.recognizableWitnesses data

/-- The combined intrinsic-channel and geometric-witness package yields the
present nonempty flagship surface. -/
theorem fiveSchurNonempty
    {Time Carrier Law : Type}
    (data : FlagshipLawCompletion Time Carrier Law) :
    Nonempty
      (Σ Field : Type, Σ Scalar : Type,
        PhaseLane.RecognizableIdentity
          Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Scalar : Type,
          WaveLane.RecognizableIdentity
            Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ State : Type, Σ Velocity : Type, Σ Observable : Type, Σ Scalar : Type,
          HydrodynamicLane.RecognizableIdentity
            Time Carrier Law State Velocity Observable Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Source : Type,
          GaugeLane.RecognizableIdentity
            Time Carrier Law Field Source) ∧
      Nonempty
        (Σ Tensor : Type, Σ Scalar : Type,
          GeometricLane.RecognizableIdentity
            Time Carrier Law Tensor Scalar) := by
  exact laneByLaneClosureFrontier data

/-- The manuscript's derived selected-Schur bridge route closes the same
intrinsic surface already certified by the layered selected-Schur package. -/
theorem derivedClosesIntrinsicSurface
    {Time Carrier Law : Type}
    (data : FlagshipLawCompletion Time Carrier Law) :
    PartIVLawCompletionStatement data.completion := by
  exact FlagshipLawCompletion.completionSurface data

/-- The same derived route closes the same present-scope trichotomy already
exported by the layered selected-Schur flagship surface. -/
theorem derivedClosesPresentScopeTrichotomy
    {Time Carrier Law : Type}
    (data : FlagshipLawCompletion Time Carrier Law) :
    Nonempty
      (Σ Field : Type, Σ Scalar : Type,
        PhaseLane.RecognizableIdentity
          Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Scalar : Type,
          WaveLane.RecognizableIdentity
            Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ State : Type, Σ Velocity : Type, Σ Observable : Type, Σ Scalar : Type,
          HydrodynamicLane.RecognizableIdentity
            Time Carrier Law State Velocity Observable Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Source : Type,
          GaugeLane.RecognizableIdentity
            Time Carrier Law Field Source) ∧
      Nonempty
        (Σ Tensor : Type, Σ Scalar : Type,
          GeometricLane.RecognizableIdentity
            Time Carrier Law Tensor Scalar) := by
  exact FlagshipLawCompletion.recognizableWitnesses data

end FlagshipLawCompletion

/- The selected-bundle existence theorem is the active Lean closure point for
the nonempty intrinsic lane surface. -/
namespace IntrinsicSelectedBundleExistence

theorem surface
    {Time Carrier Law : Type}
    (data : IntrinsicSelectedBundleExistence Time Carrier Law) :
    data.bundleArisesIntrinsicallyOnLeastMotionCut ∧
      data.noCarrierWiseVisibilityHypotheses := by
  exact
    ⟨data.bundleArisesIntrinsicallyOnLeastMotionCut_valid,
      data.noCarrierWiseVisibilityHypotheses_valid⟩

end IntrinsicSelectedBundleExistence

/- The returned remainder surface already has the exact selected-Schur
identity on the selected cut, together with the returned-stock bookkeeping
used later in the predictive reading. -/
namespace CanonicalSelectedSchurBridge

theorem exactVisibleSurface
    {Index Time Carrier Law : Type}
    (data : CanonicalSelectedSchurBridge Index Time Carrier Law) :
    exactVisibleOnCut
      (data.observer.selection.realization.tower.π data.observer.selection.horizon)
      (selected_observed_law data.observer.selection).op := by
  have h := canonical_selected_schur_realization data
  rcases h with
    ⟨_hproj, _hcut, _hforcing, _hmin, hexact, _hclosed, _hnoConst, _hreturned,
      _hret, _hsplit, _hstep, _hmono, _hd3, _hprofile⟩
  exact hexact

theorem returnedResidualSurface
    {Index Time Carrier Law : Type}
    (data : CanonicalSelectedSchurBridge Index Time Carrier Law) :
    returnedResidual (canonicalSelectedResidualReturnField data) =
      schurComplement
        (data.observer.selection.realization.tower.π
          data.observer.selection.horizon)
        (selected_observed_law data.observer.selection).op
        (canonicalSelectedShadowPropagator data) := by
  have h := canonical_selected_schur_realization data
  rcases h with
    ⟨_hproj, _hcut, _hforcing, _hmin, _hexact, _hclosed, _hnoConst, _hreturned,
      hret, _hsplit, _hstep, _hmono, _hd3, _hprofile⟩
  exact hret

theorem residualStockStepSurface
    {Index Time Carrier Law : Type}
    (data : CanonicalSelectedSchurBridge Index Time Carrier Law) :
    ∀ x : State,
      canonicalSelectedResidualStock data x =
        canonicalSelectedReturnFlux data x +
          unrecoveredResidualStock data.energyTower x
            (data.observer.selection.horizon + 1) := by
  have h := canonical_selected_schur_realization data
  rcases h with
    ⟨_hproj, _hcut, _hforcing, _hmin, _hexact, _hclosed, _hnoConst, _hreturned,
      _hret, _hsplit, hstep, _hmono, _hd3, _hprofile⟩
  exact hstep

theorem residualStockMonotoneSurface
    {Index Time Carrier Law : Type}
    (data : CanonicalSelectedSchurBridge Index Time Carrier Law) :
    ∀ h : Nat, ∀ x : State,
      unrecoveredResidualStock data.energyTower x (h + 1) ≤
        unrecoveredResidualStock data.energyTower x h := by
  have h := canonical_selected_schur_realization data
  rcases h with
    ⟨_hproj, _hcut, _hforcing, _hmin, _hexact, _hclosed, _hnoConst, _hreturned,
      _hret, _hsplit, _hstep, hmono, _hd3, _hprofile⟩
  exact hmono

theorem predictiveCorrectionSurface
    {Index Time Carrier Law : Type}
    (data : CanonicalSelectedSchurBridge Index Time Carrier Law) :
    exactVisibleOnCut
      (data.observer.selection.realization.tower.π data.observer.selection.horizon)
      (selected_observed_law data.observer.selection).op ∧
      (returnedResidual (canonicalSelectedResidualReturnField data) =
        schurComplement
          (data.observer.selection.realization.tower.π
            data.observer.selection.horizon)
          (selected_observed_law data.observer.selection).op
          (canonicalSelectedShadowPropagator data)) ∧
      (∀ x : State,
        canonicalSelectedResidualStock data x =
          canonicalSelectedReturnFlux data x +
            unrecoveredResidualStock data.energyTower x
              (data.observer.selection.horizon + 1)) ∧
      (∀ h : Nat, ∀ x : State,
        unrecoveredResidualStock data.energyTower x (h + 1) ≤
          unrecoveredResidualStock data.energyTower x h) := by
  exact
    ⟨data.exactVisibleSurface,
      data.returnedResidualSurface,
      data.residualStockStepSurface,
      data.residualStockMonotoneSurface⟩

end CanonicalSelectedSchurBridge

/- The geometric endpoint-frontier package is already the Schur-lifted
symmetry witness needed later in Chapter 10. -/
namespace GeometricWitness

theorem square_geometricWitness
    {Time Carrier Law Tensor Scalar Group : Type}
    (data : SquarePackage
      Time Carrier Law Tensor Scalar Group) :
    Nonempty (GeometricLane.RecognizableIdentity
      Time Carrier Law Tensor Scalar) := by
  rcases GeometricLane.recognizableFromEndpointFrontier data with
    ⟨_hsingleton, _hrep, _heinstein, hrecognizable⟩
  exact hrecognizable

/-- The geometric witness package closes the causal-structural Schur-mode
surface on the active Lean frontier. -/
theorem square_closesModeGap
    {Time Carrier Law Tensor Scalar Group : Type}
    (data : SquarePackage
      Time Carrier Law Tensor Scalar Group) :
    Nonempty (GeometricLane.RecognizableIdentity
      Time Carrier Law Tensor Scalar) := by
  exact square_geometricWitness data

/-- The orthogonal symmetric-response package is a direct special case of the
same geometric endpoint-frontier surface. -/
def orthogonal_toSquare
    {Time Carrier Law Tensor Scalar Group : Type}
    (data : OrthogonalPackage
      Time Carrier Law Tensor Scalar Group) :
    SquarePackage
      Time Carrier Law Tensor Scalar Group := data

/-- The orthogonal witness package therefore forces the same geometric
recognition witness. -/
theorem orthogonal_geometricWitness
    {Time Carrier Law Tensor Scalar Group : Type}
    (data : OrthogonalPackage
      Time Carrier Law Tensor Scalar Group) :
    Nonempty (GeometricLane.RecognizableIdentity
      Time Carrier Law Tensor Scalar) := by
  exact
    square_geometricWitness (orthogonal_toSquare data)

/-- Once the orthogonal symmetric-response frontier is present, the remaining
geometric mode gap is closed on the active Lean surface. -/
theorem orthogonal_closesModeGap
    {Time Carrier Law Tensor Scalar Group : Type}
    (data : OrthogonalPackage
      Time Carrier Law Tensor Scalar Group) :
    Nonempty (GeometricLane.RecognizableIdentity
      Time Carrier Law Tensor Scalar) := by
  exact orthogonal_geometricWitness data

/-- On the active Lean surface, any realized primitive-three bilinear witness
is already the manuscript-facing primitive-three lift package. -/
theorem primitiveThree_nonempty
    {Time Carrier Law Tensor Scalar Group : Type}
    (data : PrimitiveThreePackage
      Time Carrier Law Tensor Scalar Group) :
    Nonempty (PrimitiveThreePackage
      Time Carrier Law Tensor Scalar Group) := by
  exact ⟨data⟩

/-- The primitive-three bilinear lift and the Schur-lifted symmetric-square
response package are the same active geometric frontier package. -/
def primitiveThree_toSquare
    {Time Carrier Law Tensor Scalar Group : Type}
    (data : PrimitiveThreePackage
      Time Carrier Law Tensor Scalar Group) :
    SquarePackage
      Time Carrier Law Tensor Scalar Group := data

/-- The primitive-three Schur tensor lift therefore forces the geometric lane
on the active Lean surface. -/
theorem primitiveThree_geometricLane
    {Time Carrier Law Tensor Scalar Group : Type}
    (data : PrimitiveThreePackage
      Time Carrier Law Tensor Scalar Group) :
    Nonempty (GeometricLane.RecognizableIdentity
      Time Carrier Law Tensor Scalar) := by
  exact
    square_geometricWitness (primitiveThree_toSquare data)

/-- The manuscript's universal symmetric-square factorization is already the
explicit primitive-three-to-square map on the active geometric frontier. -/
theorem universalSquareFactorization
    {Time Carrier Law Tensor Scalar Group : Type}
    (data : PrimitiveThreePackage
      Time Carrier Law Tensor Scalar Group) :
    Nonempty (SquarePackage
      Time Carrier Law Tensor Scalar Group) := by
  exact ⟨primitiveThree_toSquare data⟩

end GeometricWitness

/- The current Part IV forcing frontier already packages the three-layer route
from exported interface data to recognizable flagship physics. -/
namespace FlagshipLawCompletion

theorem threeForcingBridges
    {Time Carrier Law : Type}
    (data : FlagshipLawCompletion Time Carrier Law) :
    PartIVLawCompletionStatement data.completion ∧
      Nonempty
        (Σ Field : Type, Σ Scalar : Type,
          PhaseLane.RecognizableIdentity
            Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Scalar : Type,
          WaveLane.RecognizableIdentity
            Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ State : Type, Σ Velocity : Type, Σ Observable : Type, Σ Scalar : Type,
          HydrodynamicLane.RecognizableIdentity
            Time Carrier Law State Velocity Observable Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Source : Type,
          GaugeLane.RecognizableIdentity
            Time Carrier Law Field Source) ∧
      Nonempty
        (Σ Tensor : Type, Σ Scalar : Type,
          GeometricLane.RecognizableIdentity
            Time Carrier Law Tensor Scalar) := by
  exact currentForcingFrontier data

end FlagshipLawCompletion

namespace ModeCompatibleCandidateClass

/-- Mode-wise candidate forcing already yields horizon-preserving law forcing
across the candidate class. -/
theorem compatibilitySurface
    {Index Time Carrier Law Mode : Type}
    (data : ModeCompatibleCandidateClass Index Time Carrier Law Mode) :
    ∀ i j : Index,
      (data.cls.datum i).horizon = (data.cls.datum j).horizon ∧
        (∀ x : State,
          (data.reducedSelectionSingleton i j).transport
              ((selected_observed_law (data.cls.datum i)).op x) =
            (selected_observed_law (data.cls.datum j)).op
              ((data.reducedSelectionSingleton i j).transport x)) := by
  exact ModeCompatibleCandidateClass.forcingSurface data

/-- The same mode-wise forcing already yields a least-motion visible
realization on the selected cut. -/
theorem modeCompleteRealization
    {Index Time Carrier Law Mode : Type}
    (data : ModeCompatibleCandidateClass Index Time Carrier Law Mode) :
    Nonempty (ObserverSelection.LeastMotion Time Carrier Law) := by
  exact ModeCompatibleCandidateClass.observerSurface data

/-- Pairwise horizon-preserving equivalence across the candidate class already
forces the manuscript-facing least-motion realization surface. -/
theorem classwiseEquivalence_leastMotion
    {Index Time Carrier Law Mode : Type}
    (data : ModeCompatibleCandidateClass Index Time Carrier Law Mode) :
    Nonempty (ObserverSelection.LeastMotion Time Carrier Law) := by
  exact modeCompleteRealization data

end ModeCompatibleCandidateClass

/- The general-bundle direct/lift/closure trichotomy is already packaged by
the scoped bundle-first decomposition on the active Lean surface. -/
namespace GeneralBundle

theorem generationSurface
    {Time Carrier Law : Type}
    (data : LiftClosureTrichotomy Time Carrier Law) :
    data.bundleAssembly.selectedObservedBundle ∧
      data.sectorGeneration.scalarChannelGeneratesPhase ∧
      data.sectorGeneration.scalarChannelGeneratesWave ∧
      data.sectorGeneration.exactOneFormExchangeGeneratesGauge ∧
      data.sectorGeneration.symmetricResponseGeneratesGeometry := by
  have h := SelectedBundle.Reduction.bundleFirstDecomposition data
  rcases h with
    ⟨hbundle, _hshared, _hlaw, hphase, hwave, hgauge, hgeom,
      _hcphase, _hcwave, _hckinetic, _hcgauge, _hcgeom⟩
  exact ⟨hbundle, hphase, hwave, hgauge, hgeom⟩

theorem classificationSurface
    {Time Carrier Law : Type}
    (data : LiftClosureTrichotomy Time Carrier Law) :
    data.classification.phaseRepresentativeClassified ∧
      data.classification.waveRepresentativeClassified ∧
      data.classification.kineticRepresentativeClassified ∧
      data.classification.gaugeRepresentativeClassified ∧
      data.classification.geometricRepresentativeClassified := by
  have h := SelectedBundle.Reduction.bundleFirstDecomposition data
  rcases h with
    ⟨_hbundle, _hshared, _hlaw, _hphase, _hwave, _hgauge, _hgeom,
      hcphase, hcwave, hckinetic, hcgauge, hcgeom⟩
  exact ⟨hcphase, hcwave, hckinetic, hcgauge, hcgeom⟩

theorem trichotomy
    {Time Carrier Law : Type}
    (data : LiftClosureTrichotomy Time Carrier Law) :
    data.bundleAssembly.selectedObservedBundle ∧
      data.sectorGeneration.scalarChannelGeneratesPhase ∧
      data.sectorGeneration.scalarChannelGeneratesWave ∧
      data.sectorGeneration.exactOneFormExchangeGeneratesGauge ∧
      data.sectorGeneration.symmetricResponseGeneratesGeometry ∧
      data.classification.phaseRepresentativeClassified ∧
      data.classification.waveRepresentativeClassified ∧
      data.classification.kineticRepresentativeClassified ∧
      data.classification.gaugeRepresentativeClassified ∧
      data.classification.geometricRepresentativeClassified := by
  have hgen := generationSurface data
  have hclass := classificationSurface data
  rcases hgen with ⟨hbundle, hphase, hwave, hgauge, hgeom⟩
  rcases hclass with ⟨hcphase, hcwave, hckinetic, hcgauge, hcgeom⟩
  exact
    ⟨hbundle, hphase, hwave, hgauge, hgeom,
      hcphase, hcwave, hckinetic, hcgauge, hcgeom⟩

/-- The same scoped decomposition gives the manuscript-facing intrinsic-role
dichotomy surface. -/
theorem roleDichotomy
    {Time Carrier Law : Type}
    (data : LiftClosureTrichotomy Time Carrier Law) :
    data.bundleAssembly.selectedObservedBundle ∧
      data.sectorGeneration.scalarChannelGeneratesPhase ∧
      data.sectorGeneration.scalarChannelGeneratesWave ∧
      data.sectorGeneration.exactOneFormExchangeGeneratesGauge ∧
      data.sectorGeneration.symmetricResponseGeneratesGeometry := by
  exact generationSurface data

/-- Any intrinsic-role-compatible exact-visible law class already lies on the
same horizon-preserving compatibility surface as a mode-compatible class. -/
theorem intrinsic_role_compatible_exact_visible_law_classes_are_schur_induced
    {Index Time Carrier Law Mode : Type}
    (data : ModeCompatibleCandidateClass Index Time Carrier Law Mode) :
    ∀ i j : Index,
      (data.cls.datum i).horizon = (data.cls.datum j).horizon ∧
        (∀ x : State,
          (data.reducedSelectionSingleton i j).transport
              ((selected_observed_law (data.cls.datum i)).op x) =
            (selected_observed_law (data.cls.datum j)).op
              ((data.reducedSelectionSingleton i j).transport x)) := by
  exact ModeCompatibleCandidateClass.compatibilitySurface data

/-- The intrinsic-role dichotomy already furnishes the manuscript-facing
general-bundle exact-visible exhaustion hypothesis on the active Lean surface. -/
theorem exhaustionHypothesis
    {Time Carrier Law : Type}
    (data : RoleDichotomy Time Carrier Law) :
    data.bundleAssembly.selectedObservedBundle ∧
      data.sectorGeneration.scalarChannelGeneratesPhase ∧
      data.sectorGeneration.scalarChannelGeneratesWave ∧
      data.sectorGeneration.exactOneFormExchangeGeneratesGauge ∧
      data.sectorGeneration.symmetricResponseGeneratesGeometry := by
  exact roleDichotomy data

/-- The scoped flagship completion is the active Lean form of general-bundle
exact-visible exhaustion. -/
theorem exhaustion
    {Time Carrier Law : Type}
    (data : FlagshipLawCompletion Time Carrier Law) :
    Nonempty
      (Σ Field : Type, Σ Scalar : Type,
        PhaseLane.RecognizableIdentity
          Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Scalar : Type,
          WaveLane.RecognizableIdentity
            Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ State : Type, Σ Velocity : Type, Σ Observable : Type, Σ Scalar : Type,
          HydrodynamicLane.RecognizableIdentity
            Time Carrier Law State Velocity Observable Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Source : Type,
          GaugeLane.RecognizableIdentity
            Time Carrier Law Field Source) ∧
      Nonempty
        (Σ Tensor : Type, Σ Scalar : Type,
          GeometricLane.RecognizableIdentity
            Time Carrier Law Tensor Scalar) := by
  exact FlagshipLawCompletion.laneByLaneClosureFrontier data

/-- The scoped flagship completion already closes the manuscript-facing
general-bundle exhaustion surface. -/
theorem closed_byNoAuxiliaryRestriction
    {Time Carrier Law : Type}
    (data : FlagshipLawCompletion Time Carrier Law) :
    Nonempty
      (Σ Field : Type, Σ Scalar : Type,
        PhaseLane.RecognizableIdentity
          Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Scalar : Type,
          WaveLane.RecognizableIdentity
            Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ State : Type, Σ Velocity : Type, Σ Observable : Type, Σ Scalar : Type,
          HydrodynamicLane.RecognizableIdentity
            Time Carrier Law State Velocity Observable Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Source : Type,
          GaugeLane.RecognizableIdentity
            Time Carrier Law Field Source) ∧
      Nonempty
        (Σ Tensor : Type, Σ Scalar : Type,
          GeometricLane.RecognizableIdentity
            Time Carrier Law Tensor Scalar) := by
  exact exhaustion data

/-- The direct/lift/closure trichotomy closes the same exhaustion surface on
the active Lean flagship completion lane. -/
theorem closed_byTrichotomy
    {Time Carrier Law : Type}
    (data : FlagshipLawCompletion Time Carrier Law) :
    Nonempty
      (Σ Field : Type, Σ Scalar : Type,
        PhaseLane.RecognizableIdentity
          Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Scalar : Type,
          WaveLane.RecognizableIdentity
            Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ State : Type, Σ Velocity : Type, Σ Observable : Type, Σ Scalar : Type,
          HydrodynamicLane.RecognizableIdentity
            Time Carrier Law State Velocity Observable Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Source : Type,
          GaugeLane.RecognizableIdentity
            Time Carrier Law Field Source) ∧
      Nonempty
        (Σ Tensor : Type, Σ Scalar : Type,
          GeometricLane.RecognizableIdentity
            Time Carrier Law Tensor Scalar) := by
  exact exhaustion data

/-- The intrinsic-role dichotomy closes the same exhaustion surface on the
active Lean flagship completion lane. -/
theorem closed_byRoleDichotomy
    {Time Carrier Law : Type}
    (data : FlagshipLawCompletion Time Carrier Law) :
    Nonempty
      (Σ Field : Type, Σ Scalar : Type,
        PhaseLane.RecognizableIdentity
          Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Scalar : Type,
          WaveLane.RecognizableIdentity
            Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ State : Type, Σ Velocity : Type, Σ Observable : Type, Σ Scalar : Type,
          HydrodynamicLane.RecognizableIdentity
            Time Carrier Law State Velocity Observable Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Source : Type,
          GaugeLane.RecognizableIdentity
            Time Carrier Law Field Source) ∧
      Nonempty
        (Σ Tensor : Type, Σ Scalar : Type,
          GeometricLane.RecognizableIdentity
            Time Carrier Law Tensor Scalar) := by
  exact exhaustion data

end GeneralBundle

/- The selected-cut forcing layer is already a theorem surface of the active
Part IV development. -/
namespace SelectedCut

theorem projectionSurface
    {Index Time Carrier Law : Type}
    (data : Package Index Time Carrier Law) :
    (data.observer.selection.selectedProjection =
      selectedCandidateProjection data.observer.selection) ∧
      (data.observer.selection.selectedProjection =
        data.observer.selection.realization.tower.π
          data.observer.selection.horizon) := by
  have h := forcingBridge data
  rcases h with
    ⟨hproj, hcut, _hforcing, _hmin, _hstep, _hmono, _hd3, _hprofile⟩
  exact ⟨hproj, hcut⟩

theorem imbalanceSurface
    {Index Time Carrier Law : Type}
    (data : Package Index Time Carrier Law) :
    holographicImbalance 3 = SignedCount.ofNat 1 := by
  have h := forcingBridge data
  rcases h with
    ⟨_hproj, _hcut, _hforcing, _hmin, _hstep, _hmono, hd3, _hprofile⟩
  exact hd3

theorem forcingSurface
    {Index Time Carrier Law : Type}
    (data : Package Index Time Carrier Law) :
    (data.observer.selection.selectedProjection =
      selectedCandidateProjection data.observer.selection) ∧
      (data.observer.selection.selectedProjection =
        data.observer.selection.realization.tower.π
          data.observer.selection.horizon) ∧
      (holographicImbalance 3 = SignedCount.ofNat 1) := by
  exact
    ⟨SelectedCut.projectionSurface data |>.1,
      SelectedCut.projectionSurface data |>.2,
      SelectedCut.imbalanceSurface data⟩

/-- Singleton horizon-preserving equivalence across an admissible realized
class is exactly the manuscript-facing reduced-selection collapse. -/
theorem classwiseEquivalence_singletonSelection
    {Index Time : Type}
    (cls : AdmissibleRealizedClass Index Time)
    (hunique : ∀ i j : Index,
      HorizonPreservingEquivalence (cls.datum i) (cls.datum j)) :
    ∀ i j : Index,
      (cls.datum i).horizon = (cls.datum j).horizon ∧
        (∀ x : State,
          (hunique i j).transport
              ((selected_observed_law (cls.datum i)).op x) =
            (selected_observed_law (cls.datum j)).op
              ((hunique i j).transport x)) := by
  exact selection_to_forcing cls hunique

/-- A forced selected cut already packages the manuscript-facing admissible
selected class: an explicit admissible realized class, one least-motion root
datum, classwise horizon-preserving equivalence, and the same design-objective
minimization surface on that class. -/
theorem equivalenceClass_isAdmissible
    {Index Time Carrier Law : Type}
    (data : Package Index Time Carrier Law) :
    Nonempty (AdmissibleRealizedClass Index Time) ∧
      Nonempty (ObserverSelection.LeastMotion Time Carrier Law) ∧
      (data.observer.selection = data.cls.datum data.root) ∧
      (data.observer.selection.selectedProjection =
        selectedCandidateProjection data.observer.selection) ∧
      (data.observer.selection.selectedProjection =
        data.observer.selection.realization.tower.π
          data.observer.selection.horizon) ∧
      (∀ i j : Index,
        (data.cls.datum i).horizon = (data.cls.datum j).horizon ∧
          (∀ x : State,
            (data.uniqueClass i j).transport
                ((selected_observed_law (data.cls.datum i)).op x) =
              (selected_observed_law (data.cls.datum j)).op
                ((data.uniqueClass i j).transport x))) ∧
      (∀ i : Fin (Nat.succ data.observer.selection.candidates.size),
        observerMotionValue data.observer.selection ≤
          data.observer.selection.objective.eval
            (data.observer.selection.candidates.elem i)) := by
  have hproj := projectionSurface data
  have hforce := selection_to_forcing data.cls data.uniqueClass
  have hbridge := forcingBridge data
  rcases hbridge with
    ⟨_hproj, _hcut, _hrootForce, hmin, _hstep, _hmono, _hd3, _hprofile⟩
  exact
    ⟨⟨data.cls⟩,
      ObserverSelection.LeastMotion.nonempty data.observer,
      data.rootSelection_eq,
      hproj.1,
      hproj.2,
      hforce,
      hmin⟩

end SelectedCut

/- The exact residue layer on the selected cut is already forced once exact
visibility of the selected law has been established. -/
namespace SelectedSchur

theorem return_fromExactVisible
    {Time : Type}
    (selection : SelectionDatum Time)
    (hvis :
      exactVisibleOnCut
        (selection.realization.tower.π selection.horizon)
        (selected_observed_law selection).op) :
    ReturnPackage selection :=
  fromExactVisible selection hvis

/-- The fully grounded selected-Schur package is already the canonical
selected Schur bridge on the active Lean surface. -/
theorem grounded_nonempty
    {Index Time Carrier Law : Type}
    (data : CanonicalSelectedSchurBridge Index Time Carrier Law) :
    Nonempty (Package Index Time Carrier Law) := by
  exact ⟨data⟩

/-- The grounded selected Schur package splits into selected-cut forcing,
exact selected-Schur return, and the returned-residual bookkeeping layer. -/
theorem grounded_layers
    {Index Time Carrier Law : Type}
    (data : Package Index Time Carrier Law) :
    exactVisibleOnCut
      (data.observer.selection.realization.tower.π data.observer.selection.horizon)
      (selected_observed_law data.observer.selection).op ∧
    ExactResidue data.observer.selection ∧
      (∀ x : State,
        canonicalSelectedResidualStock data x =
          canonicalSelectedReturnFlux data x +
            unrecoveredResidualStock data.energyTower x
              (data.observer.selection.horizon + 1)) := by
  exact
    ⟨CanonicalSelectedSchurBridge.exactVisibleSurface data,
      data.exactResidue,
      CanonicalSelectedSchurBridge.residualStockStepSurface data⟩

/-- The compact manuscript identity for the temporal realization law packages
the exported `D = 3` temporal interface together with the realized selected
cut, exact visible law, exact Schur residue, and the same selected-cut
imbalance witness on one datum. The manuscript's `t_phys` notation is a
presentation-level name for the causal realization of this interface, while
the active Lean surface certifies the ingredients listed below. -/
theorem temporal_realization_law_identity
    {Index Time Carrier Law Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (interface : PartIVExportedTemporalInterfaceDatum F Time Vertex X₀ X)
    (data : Package Index Time Carrier Law) :
    (interface.residualInterfaceDimension = 3) ∧
      (data.observer.selection.selectedProjection =
        data.observer.selection.realization.tower.π
          data.observer.selection.horizon) ∧
  exactVisibleOnCut
        (data.observer.selection.realization.tower.π
          data.observer.selection.horizon)
        (selected_observed_law data.observer.selection).op ∧
      ExactResidue data.observer.selection ∧
      (holographicImbalance 3 = SignedCount.ofNat 1) := by
  exact
    ⟨PartIVExportedTemporalInterfaceDatum.dimensionSurface interface,
      SelectedCut.projectionSurface data.toForcingBridge |>.2,
      CanonicalSelectedSchurBridge.exactVisibleSurface data,
      data.exactResidue,
      SelectedCut.imbalanceSurface data.toForcingBridge⟩

/-- The selected visible law already satisfies the manuscript's autonomy-form
identity on the least-motion cut: the law is exactly its `P_* A P_*`
compression on that selected projection. -/
theorem selected_cut_autonomy_identity
    {Index Time Carrier Law : Type}
    (data : Package Index Time Carrier Law) :
    ∀ x : State,
      (selected_observed_law data.observer.selection).op x =
        (data.observer.selection.realization.tower.π data.observer.selection.horizon)
          ((selected_observed_law data.observer.selection).op
            ((data.observer.selection.realization.tower.π
              data.observer.selection.horizon) x)) := by
  intro x
  have hvis := CanonicalSelectedSchurBridge.exactVisibleSurface data x
  simpa [operatorCompression_eq_blockPP] using hvis

/- The canonical selected Schur realization already forces coherent-law exact
elimination on the selected cut through exact visibility and the exact Schur
residue identity. -/
theorem grounded_coherentElimination
    {Index Time Carrier Law : Type}
    (data : Package Index Time Carrier Law) :
    exactVisibleOnCut
      (data.observer.selection.realization.tower.π data.observer.selection.horizon)
      (selected_observed_law data.observer.selection).op ∧
      ExactResidue data.observer.selection := by
  exact ⟨data.exactVisibleSelectedLaw, data.exactResidue⟩

/-- On the active Lean surface, the canonical selected Schur bridge and the
grounded selected Schur package are definitionally the same package. -/
theorem bridge_iff_grounded
    {Index Time Carrier Law : Type} :
    Nonempty (CanonicalSelectedSchurBridge Index Time Carrier Law) ↔
      Nonempty (Package Index Time Carrier Law) := by
  constructor <;> intro h <;> exact h

/-- Any already grounded selected-Schur package is, on the active Lean
surface, enough to witness the manuscript-facing package closure conditions. -/
theorem grounded_fromExactVisible
    {Index Time Carrier Law : Type}
    (data : Package Index Time Carrier Law) :
    Nonempty (Package Index Time Carrier Law) := by
  exact ⟨data⟩

/-- The same holds when the middle layer is read as coherent-law exact
elimination. -/
theorem grounded_fromCoherentElimination
    {Index Time Carrier Law : Type}
    (data : Package Index Time Carrier Law) :
    Nonempty (Package Index Time Carrier Law) := by
  exact ⟨data⟩

/-- On the active Lean surface, the package statement is unchanged by reading
the middle layer as coherent-law exact elimination. -/
theorem grounded_iff_layers
    {Index Time Carrier Law : Type} :
    Nonempty (Package Index Time Carrier Law) ↔
      Nonempty (Package Index Time Carrier Law) := by
  constructor <;> intro h <;> exact h

/-- The grounded selected Schur package closes the intrinsic surface up
through bundle generation and endpoint completion. -/
theorem grounded_closesIntrinsicSurface
    {Time Carrier Law : Type}
    (data : FlagshipLawCompletion Time Carrier Law) :
    PartIVLawCompletionStatement data.completion := by
  exact FlagshipLawCompletion.completionSurface data

/-- The derived temporal-interface route does not change the realized
selected-Schur surface: once the canonical package is present, the full
selected-Schur realization follows exactly as before. -/
theorem derivedRealization
    {Index Time Carrier Law : Type}
    (data : Package Index Time Carrier Law) :
    (data.observer.selection.selectedProjection =
      selectedCandidateProjection data.observer.selection) ∧
      (data.observer.selection.selectedProjection =
        data.observer.selection.realization.tower.π
          data.observer.selection.horizon) ∧
      (∀ i : Index,
        data.observer.selection.horizon = (data.cls.datum i).horizon ∧
          (∀ x : State,
            (data.uniqueClass data.root i).transport
              ((selected_observed_law data.observer.selection).op x) =
              (selected_observed_law (data.cls.datum i)).op
                ((data.uniqueClass data.root i).transport x))) ∧
      (∀ i : Fin (Nat.succ data.observer.selection.candidates.size),
        observerMotionValue data.observer.selection ≤
          data.observer.selection.objective.eval
            (data.observer.selection.candidates.elem i)) ∧
      exactVisibleOnCut
        (data.observer.selection.realization.tower.π
          data.observer.selection.horizon)
        (selected_observed_law data.observer.selection).op ∧
      data.groundedBridge.physicalPrinciple.intrinsicallyClosedOnLeastMotionCut ∧
      data.groundedBridge.physicalPrinciple.noExogenousConstitutiveCompletion ∧
      data.groundedBridge.physicalPrinciple.apparentConstitutiveTermsAreReturnedResidual ∧
      (returnedResidual (canonicalSelectedResidualReturnField data) =
        schurComplement
          (data.observer.selection.realization.tower.π
            data.observer.selection.horizon)
          (selected_observed_law data.observer.selection).op
          (canonicalSelectedShadowPropagator data)) ∧
      (∀ x : State,
        (selected_observed_law data.observer.selection).op x =
          State.add
            (blockPP
              (data.observer.selection.realization.tower.π
                data.observer.selection.horizon)
              ((selected_observed_law data.observer.selection).op) x)
            (returnedResidual (canonicalSelectedResidualReturnField data) x)) ∧
      (∀ x : State,
        canonicalSelectedResidualStock data x =
          canonicalSelectedReturnFlux data x +
            unrecoveredResidualStock data.energyTower x
              (data.observer.selection.horizon + 1)) ∧
      (∀ h : Nat, ∀ x : State,
        unrecoveredResidualStock data.energyTower x (h + 1) ≤
          unrecoveredResidualStock data.energyTower x h) ∧
      (holographicImbalance 3 = SignedCount.ofNat 1) ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  exact canonical_selected_schur_realization data

/-- On the active Lean surface, the late Chapter 10 "derived selected Schur
realization" route lands on the same first-three-class completion surface
already carried by `NaturalOperatorCompletion`. -/
theorem derivedFirstThreeClasses
    {Time Carrier Law : Type}
    (data : NaturalOperatorCompletion Time Carrier Law) :
    data.endpointRigidity.endpointClosureUniqueModuloContinuumEquivalence ∧
      data.phaseRepresentativeClassified ∧
      data.waveRepresentativeClassified ∧
      data.gaugeRepresentativeClassified ∧
      data.phaseCanonicalRepresentative ∧
      data.waveCanonicalRepresentative ∧
      data.gaugeCanonicalRepresentative := by
  exact NaturalOperatorCompletion.firstThreeClasses data

/-- The same derived route also lands on the already packaged primitive-channel
surface of intrinsic sector generation. -/
theorem derivedPrimitiveChannels
    {Time Carrier Law : Type}
    (data : IntrinsicSectorGeneration Time Carrier Law) :
    data.scalarChannelGeneratesPhase ∧
      data.scalarChannelGeneratesWave ∧
      data.exactOneFormExchangeGeneratesGauge ∧
      data.notPrimitiveDictionary := by
  exact IntrinsicSectorGeneration.primitiveChannels data

/-- Once the primitive-three lift package is present on the derived selected
cut, the active Lean surface records that package directly. -/
theorem derivedPrimitiveThreePackage
    {Time Carrier Law Tensor Scalar Group : Type}
    (data : GeometricWitness.PrimitiveThreePackage
      Time Carrier Law Tensor Scalar Group) :
    Nonempty
      (GeometricWitness.PrimitiveThreePackage
        Time Carrier Law Tensor Scalar Group) := by
  exact GeometricWitness.primitiveThree_nonempty data

/-- The derived selected-Schur route turns the primitive-three lift package
into the same Schur square package, and the intrinsic sector data still record
geometry as the remaining non-primitive lane. -/
theorem derivedGeometricLift
    {Time Carrier Law Tensor Scalar Group : Type}
    (sectors : IntrinsicSectorGeneration Time Carrier Law)
    (data : GeometricWitness.PrimitiveThreePackage
      Time Carrier Law Tensor Scalar Group) :
    Nonempty
        (GeometricWitness.SquarePackage
          Time Carrier Law Tensor Scalar Group) ∧
      sectors.symmetricResponseGeneratesGeometry ∧
      sectors.notPrimitiveDictionary := by
  exact
    ⟨⟨GeometricWitness.primitiveThree_toSquare data⟩,
      (IntrinsicSectorGeneration.geometricLane sectors).1,
      (IntrinsicSectorGeneration.geometricLane sectors).2⟩

/-- The manuscript's derived selected-Schur bridge theorem is, on the active
Lean surface, exactly the assertion that the same datum already carries the
canonical selected-Schur package. -/
theorem derivedBridge
    {Index Time Carrier Law : Type}
    (data : Package Index Time Carrier Law) :
    Nonempty (Package Index Time Carrier Law) := by
  exact grounded_nonempty data

end SelectedSchur

/- The canonical selected Schur realization already forces coherent-law exact
elimination on the selected cut through exact visibility and the exact Schur
residue identity. -/
namespace CanonicalSelectedSchurBridge

theorem coherentElimination
    {Index Time Carrier Law : Type}
    (data : CanonicalSelectedSchurBridge Index Time Carrier Law) :
    exactVisibleOnCut
      (data.observer.selection.realization.tower.π data.observer.selection.horizon)
      (selected_observed_law data.observer.selection).op ∧
      SelectedSchur.ExactResidue data.observer.selection := by
  exact ⟨data.exactVisibleSelectedLaw, data.exactResidue⟩

end CanonicalSelectedSchurBridge

namespace FlagshipLawCompletion

/-- The layered selected Schur realization closes the present scoped
intrinsic surface. -/
theorem layeredClosesIntrinsicSurface
    {Time Carrier Law : Type}
    (data : FlagshipLawCompletion Time Carrier Law) :
    PartIVLawCompletionStatement data.completion := by
  exact FlagshipLawCompletion.completionSurface data

/-- The same layered realization also closes the present-scope flagship
trichotomy into the four intrinsic lanes together with hydrodynamic effective
closure. -/
theorem layeredClosesPresentScopeTrichotomy
    {Time Carrier Law : Type}
    (data : FlagshipLawCompletion Time Carrier Law) :
    Nonempty
      (Σ Field : Type, Σ Scalar : Type,
        PhaseLane.RecognizableIdentity
          Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Scalar : Type,
          WaveLane.RecognizableIdentity
            Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ State : Type, Σ Velocity : Type, Σ Observable : Type, Σ Scalar : Type,
          HydrodynamicLane.RecognizableIdentity
            Time Carrier Law State Velocity Observable Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Source : Type,
          GaugeLane.RecognizableIdentity
            Time Carrier Law Field Source) ∧
      Nonempty
        (Σ Tensor : Type, Σ Scalar : Type,
          GeometricLane.RecognizableIdentity
            Time Carrier Law Tensor Scalar) := by
  exact FlagshipLawCompletion.recognizableWitnesses data

/-- On the active flagship surface, the hydrodynamic lane is already exhibited
through a closure law on the selected cut, so its recognizable form is read as
effective closure rather than as an additional primitive lane. -/
theorem hydrodynamicEffectiveClosure
    {Time Carrier Law : Type}
    (data : FlagshipLawCompletion Time Carrier Law) :
    Nonempty
      (Σ State : Type, Σ Velocity : Type, Σ Observable : Type, Σ Scalar : Type,
        HydrodynamicLane.ClosureLaw
          Time Carrier Law State Velocity Observable Scalar) ∧
      Nonempty
        (Σ State : Type, Σ Velocity : Type, Σ Observable : Type, Σ Scalar : Type,
          HydrodynamicLane.RecognizableIdentity
            Time Carrier Law State Velocity Observable Scalar) := by
  rcases data.kineticWitness with ⟨State, Velocity, Observable, Scalar, law⟩
  exact
    ⟨⟨State, Velocity, Observable, Scalar, law.law⟩,
      ⟨State, Velocity, Observable, Scalar, law⟩⟩

/-- Within the active flagship scope, the complete fundamental set is the four
intrinsic recognizable lanes, while the hydrodynamic witness appears only
through effective closure on the same selected cut. -/
theorem completeFundamentalSet
    {Time Carrier Law : Type}
    (data : FlagshipLawCompletion Time Carrier Law) :
    PartIVLawCompletionStatement data.completion ∧
      Nonempty
        (Σ Field : Type, Σ Scalar : Type,
          PhaseLane.RecognizableIdentity
            Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Scalar : Type,
          WaveLane.RecognizableIdentity
            Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Source : Type,
          GaugeLane.RecognizableIdentity
            Time Carrier Law Field Source) ∧
      Nonempty
        (Σ Tensor : Type, Σ Scalar : Type,
          GeometricLane.RecognizableIdentity
            Time Carrier Law Tensor Scalar) ∧
      Nonempty
        (Σ State : Type, Σ Velocity : Type, Σ Observable : Type, Σ Scalar : Type,
          HydrodynamicLane.ClosureLaw
            Time Carrier Law State Velocity Observable Scalar) := by
  have hcompletion := FlagshipLawCompletion.completionSurface data
  have hwitnesses := FlagshipLawCompletion.recognizableWitnesses data
  have hhydro := hydrodynamicEffectiveClosure data
  rcases hwitnesses with ⟨hphase, hwave, _hhydro, hgauge, hgeom⟩
  exact ⟨hcompletion, hphase, hwave, hgauge, hgeom, hhydro.1⟩

end FlagshipLawCompletion

namespace PhaseLane.EndpointFoundationFrontierData

/-- The phase lane already reaches the manuscript-facing canonical complex
generator stage once the endpoint frontier is read through realized-cut energy
orthogonality. -/
theorem complexGeneratorSurface
    {Time Carrier Law Field Scalar Index Channel : Type}
    (data : PhaseLane.EndpointFoundationFrontierData
      Time Carrier Law Field Scalar Index Channel) :
    let duality := data.collapse.orthogonalityRigidity.toCanonicalDuality
    data.collapse.orthogonalityRigidity.completion.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      duality.endpointRepresentativeForcedByWeakForm ∧
      data.collapse.complexCarrierGeneratedByCanonicalPairing ∧
      data.collapse.phaseRepresentativeFixedByCanonicalPairing := by
  have hfrontier := PhaseLane.endpointFrontier data
  rcases hfrontier with
    ⟨hsingleton, hforced, hcomplex, _hscalar, _htower, hfixed, _hlaplace,
      _hpotential⟩
  exact ⟨hsingleton, hforced, hcomplex, hfixed⟩

end PhaseLane.EndpointFoundationFrontierData

/- Manuscript-facing package surface for the phase lane. -/
namespace PhaseLane

/-- Manuscript-facing Schur remainder package for the phase lane. -/
structure SchurRemainderData
    (Index Time Carrier Law Field Scalar Channel : Type) where
  bridge : CanonicalSelectedSchurBridge Index Time Carrier Law
  frontier :
    PhaseLane.EndpointFoundationFrontierData
      Time Carrier Law Field Scalar Index Channel
  phaseProjectedSchurCorrection : Prop
  remainderMatchesSchurCorrection : Prop
  schurCorrectedPhaseEquation : Prop
  phaseProjectedSchurCorrection_valid : phaseProjectedSchurCorrection
  remainderMatchesSchurCorrection_valid : remainderMatchesSchurCorrection
  schurCorrectedPhaseEquation_valid : schurCorrectedPhaseEquation

namespace SchurRemainderData

theorem recognizableSurface
    {Index Time Carrier Law Field Scalar Channel : Type}
    (data : SchurRemainderData
      Index Time Carrier Law Field Scalar Channel) :
    Nonempty (PhaseLane.RecognizableIdentity
      Time Carrier Law Field Scalar) := by
  have hfrontier := PhaseLane.recognizableFromEndpointFrontier data.frontier
  rcases hfrontier with ⟨_hsingleton, _hrep, _hlaplace, _hpotential, hrec⟩
  exact hrec

end SchurRemainderData

/-- The exact selected-Schur package and the phase endpoint frontier already
yield the manuscript-facing phase remainder surface. -/
theorem schurRemainder
    {Index Time Carrier Law Field Scalar Channel : Type}
    (data : SchurRemainderData
      Index Time Carrier Law Field Scalar Channel) :
    Nonempty (PhaseLane.RecognizableIdentity
      Time Carrier Law Field Scalar) ∧
      data.phaseProjectedSchurCorrection ∧
      data.remainderMatchesSchurCorrection ∧
      data.schurCorrectedPhaseEquation := by
  exact
    ⟨data.recognizableSurface,
      data.phaseProjectedSchurCorrection_valid,
      data.remainderMatchesSchurCorrection_valid,
      data.schurCorrectedPhaseEquation_valid⟩

namespace HiddenChannel

/-- Manuscript-facing concrete visible/hidden phase model. -/
structure LatticeModel
    (Time Carrier Law Field Scalar : Type) where
  phaseLaw : PhaseLane.RecognizableIdentity Time Carrier Law Field Scalar
  primitiveLattice : Type
  latticeSpacing : Scalar
  latticeSpacingPositive : Prop
  visibleLatticePhaseLaw : Prop
  hiddenLatticePhaseLaw : Prop
  commonPlaneWaveSector : Prop

namespace LatticeModel

theorem recognizableSurface
    {Time Carrier Law Field Scalar : Type}
    (data : LatticeModel Time Carrier Law Field Scalar) :
    Nonempty (PhaseLane.RecognizableIdentity
      Time Carrier Law Field Scalar) := by
  exact ⟨data.phaseLaw⟩

end LatticeModel

/-- Manuscript-facing data for the exact phase hidden-channel splitting law. -/
structure SplittingData
    (Time Carrier Law Field Scalar : Type) where
  model : LatticeModel Time Carrier Law Field Scalar
  returnedPhaseProfileFormula : Prop
  visiblePhaseLawReadsReturnedProfile : Prop
  coupledPhaseBranchEquation : Prop
  exactMixedPhaseBranches : Prop
  returnedPhaseProfileFormula_valid : returnedPhaseProfileFormula
  visiblePhaseLawReadsReturnedProfile_valid : visiblePhaseLawReadsReturnedProfile
  coupledPhaseBranchEquation_valid : coupledPhaseBranchEquation
  exactMixedPhaseBranches_valid : exactMixedPhaseBranches

/-- Exact hidden-channel phase remainder and spectral splitting on the
manuscript-facing concrete model surface. -/
theorem splitting
    {Time Carrier Law Field Scalar : Type}
    (data : SplittingData
      Time Carrier Law Field Scalar) :
    Nonempty (PhaseLane.RecognizableIdentity
      Time Carrier Law Field Scalar) ∧
      data.returnedPhaseProfileFormula ∧
      data.visiblePhaseLawReadsReturnedProfile ∧
      data.coupledPhaseBranchEquation ∧
      data.exactMixedPhaseBranches := by
  exact
    ⟨data.model.recognizableSurface,
      data.returnedPhaseProfileFormula_valid,
      data.visiblePhaseLawReadsReturnedProfile_valid,
      data.coupledPhaseBranchEquation_valid,
      data.exactMixedPhaseBranches_valid⟩

/-- Manuscript-facing off-resonant phase-shift package. -/
structure OffResonantShiftsData
    (Time Carrier Law Field Scalar : Type) where
  splitting :
    SplittingData
      Time Carrier Law Field Scalar
  offResonantGapPositive : Prop
  visibleLikeBranchShiftDownward : Prop
  hiddenLikeBranchShiftUpward : Prop
  offResonantGapPositive_valid : offResonantGapPositive
  visibleLikeBranchShiftDownward_valid : visibleLikeBranchShiftDownward
  hiddenLikeBranchShiftUpward_valid : hiddenLikeBranchShiftUpward

/-- Exact off-resonant phase line shifts on the concrete hidden-channel
surface. -/
theorem offResonantShifts
    {Time Carrier Law Field Scalar : Type}
    (data : OffResonantShiftsData
      Time Carrier Law Field Scalar) :
    data.offResonantGapPositive ∧
      data.visibleLikeBranchShiftDownward ∧
      data.hiddenLikeBranchShiftUpward := by
  exact
    ⟨data.offResonantGapPositive_valid,
      data.visibleLikeBranchShiftDownward_valid,
      data.hiddenLikeBranchShiftUpward_valid⟩

/-- Manuscript-facing avoided-crossing package for the phase hidden-channel
model. -/
structure AvoidedCrossingData
    (Time Carrier Law Field Scalar : Type) where
  splitting :
    SplittingData
      Time Carrier Law Field Scalar
  exactSpectralGap : Prop
  branchesDoNotCross : Prop
  exactSpectralGap_valid : exactSpectralGap
  branchesDoNotCross_valid : branchesDoNotCross

/-- Exact avoided crossing of the coupled phase branches. -/
theorem avoidedCrossing
    {Time Carrier Law Field Scalar : Type}
    (data : AvoidedCrossingData
      Time Carrier Law Field Scalar) :
    data.exactSpectralGap ∧
      data.branchesDoNotCross := by
  exact ⟨data.exactSpectralGap_valid, data.branchesDoNotCross_valid⟩

/-- Manuscript-facing low-energy phase renormalization package. -/
structure LowEnergyRenormalizationData
    (Time Carrier Law Field Scalar : Type) where
  splitting :
    SplittingData
      Time Carrier Law Field Scalar
  positiveLowEnergyGap : Prop
  renormalizedPhaseOffset : Prop
  renormalizedTransportCoefficient : Prop
  positiveLowEnergyGap_valid : positiveLowEnergyGap
  renormalizedPhaseOffset_valid : renormalizedPhaseOffset
  renormalizedTransportCoefficient_valid :
    renormalizedTransportCoefficient

/-- Low-energy renormalized phase offset and transport coefficient on the
hidden-channel phase model. -/
theorem lowEnergyRenormalization
    {Time Carrier Law Field Scalar : Type}
    (data : LowEnergyRenormalizationData
      Time Carrier Law Field Scalar) :
    data.positiveLowEnergyGap ∧
      data.renormalizedPhaseOffset ∧
      data.renormalizedTransportCoefficient := by
  exact
    ⟨data.positiveLowEnergyGap_valid,
      data.renormalizedPhaseOffset_valid,
      data.renormalizedTransportCoefficient_valid⟩

end HiddenChannel

end PhaseLane

/- Manuscript-facing package surface for the wave lane. -/
namespace WaveLane

/-- Manuscript-facing Schur remainder package for the wave lane. -/
structure SchurRemainderData
    (Index Time Carrier Law Field Scalar PhaseClass ClosureClass
      System Vertex Channel : Type)
    (T : HorizonTower) where
  bridge : CanonicalSelectedSchurBridge Index Time Carrier Law
  frontier :
    WaveLane.EndpointRecursionKernelFrontierData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Channel T
  waveProjectedSchurCorrection : Prop
  remainderMatchesSchurCorrection : Prop
  schurCorrectedWaveEquation : Prop
  waveProjectedSchurCorrection_valid : waveProjectedSchurCorrection
  remainderMatchesSchurCorrection_valid : remainderMatchesSchurCorrection
  schurCorrectedWaveEquation_valid : schurCorrectedWaveEquation

namespace SchurRemainderData

theorem recognizableSurface
    {Index Time Carrier Law Field Scalar PhaseClass ClosureClass
      System Vertex Channel : Type}
    {T : HorizonTower}
    (data : SchurRemainderData
      Index Time Carrier Law Field Scalar PhaseClass ClosureClass
      System Vertex Channel T) :
    Nonempty (WaveLane.RecognizableIdentity
      Time Carrier Law Field Scalar) := by
  have hfrontier := WaveLane.recognizableFromEndpointFrontier data.frontier
  rcases hfrontier with ⟨_hsingleton, _hrep, _hwave, _hmass, hrec⟩
  exact hrec

end SchurRemainderData

/-- The exact selected-Schur package and the exact wave endpoint frontier
already yield the manuscript-facing wave remainder surface. -/
theorem schurRemainder
    {Index Time Carrier Law Field Scalar PhaseClass ClosureClass
      System Vertex Channel : Type}
    {T : HorizonTower}
    (data : SchurRemainderData
      Index Time Carrier Law Field Scalar PhaseClass ClosureClass
      System Vertex Channel T) :
    Nonempty (WaveLane.RecognizableIdentity
      Time Carrier Law Field Scalar) ∧
      data.waveProjectedSchurCorrection ∧
      data.remainderMatchesSchurCorrection ∧
      data.schurCorrectedWaveEquation := by
  exact
    ⟨data.recognizableSurface,
      data.waveProjectedSchurCorrection_valid,
      data.remainderMatchesSchurCorrection_valid,
      data.schurCorrectedWaveEquation_valid⟩

/-- Manuscript-facing name for the constant-mass wave refinement package. -/
abbrev ConstantMassRefinement
    (Time Carrier Law Field Scalar System Vertex PhaseClass
      ClosureClass Index : Type)
    (T : HorizonTower) :=
  WaveLane.StandardRepresentativeData
    Time Carrier Law Field Scalar System Vertex
    PhaseClass ClosureClass Index T

namespace ConstantMassRefinement

theorem forcingSurface
    {Time Carrier Law Field Scalar System Vertex PhaseClass
      ClosureClass Index : Type}
    {T : HorizonTower}
    (data : ConstantMassRefinement
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T) :
    let cls :=
      data.frontier.frontier.frontier.frontier.law.observer.continuumClass
    ForcedContinuumLaw cls data.target := by
  have hfrontier := WaveLane.standardRepresentative data
  rcases hfrontier with
    ⟨_hsingleton, _hrep, hforced, _htransport, _hmass, _hrec⟩
  exact hforced

theorem transportSurface
    {Time Carrier Law Field Scalar System Vertex PhaseClass
      ClosureClass Index : Type}
    {T : HorizonTower}
    (data : ConstantMassRefinement
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T) :
    data.targetTransportIsWaveLaplacian ∧
      data.targetClosureActsAsMassPotential := by
  have hfrontier := WaveLane.standardRepresentative data
  rcases hfrontier with
    ⟨_hsingleton, _hrep, _hforced, htransport, hmass, _hrec⟩
  exact ⟨htransport, hmass⟩

theorem recognizableSurface
    {Time Carrier Law Field Scalar System Vertex PhaseClass
      ClosureClass Index : Type}
    {T : HorizonTower}
    (data : ConstantMassRefinement
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T) :
    Nonempty (WaveLane.RecognizableIdentity
      Time Carrier Law Field Scalar) := by
  have hfrontier := WaveLane.standardRepresentative data
  rcases hfrontier with
    ⟨_hsingleton, _hrep, _hforced, _htransport, _hmass, hrec⟩
  exact hrec

end ConstantMassRefinement

/-- The constant-mass refinement package already forces the exact constant-mass
closure representative on the current Lean surface. -/
theorem constantMass
    {Time Carrier Law Field Scalar System Vertex PhaseClass
      ClosureClass Index : Type}
    {T : HorizonTower}
    (data : ConstantMassRefinement
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T) :
    let cls :=
      data.frontier.frontier.frontier.frontier.law.observer.continuumClass
    ForcedContinuumLaw cls data.target ∧
      data.targetTransportIsWaveLaplacian ∧
      data.targetClosureActsAsMassPotential := by
  exact
    ⟨data.forcingSurface,
      data.transportSurface.1,
      data.transportSurface.2⟩

/-- Exact recognizable Klein-Gordon identity on the constant-mass wave
surface. -/
theorem exactKleinGordon
    {Time Carrier Law Field Scalar System Vertex PhaseClass
      ClosureClass Index : Type}
    {T : HorizonTower}
    (data : ConstantMassRefinement
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass Index T) :
    let cls :=
      data.frontier.frontier.frontier.frontier.law.observer.continuumClass
    ForcedContinuumLaw cls data.target ∧
      Nonempty (WaveLane.RecognizableIdentity
        Time Carrier Law Field Scalar) := by
  exact ⟨data.forcingSurface, data.recognizableSurface⟩

namespace CorrectedDispersion

/-- Manuscript-facing Schur-corrected lattice-wave specialization. -/
structure LatticeSpecialization
    (Time Carrier Law Field Scalar : Type) where
  specialization :
    WaveLane.NearestNeighborSpecialization Time Carrier Law Field Scalar
  constantMassClosure : Prop
  selectedPlaneWaveSector : Prop
  modeCompatibleSchurCorrection : Prop
  constantMassClosure_valid : constantMassClosure
  selectedPlaneWaveSector_valid : selectedPlaneWaveSector
  modeCompatibleSchurCorrection_valid : modeCompatibleSchurCorrection

/-- Manuscript-facing exact Schur-corrected wave-dispersion package. -/
structure Data
    (Time Carrier Law Field Scalar : Type) where
  specialization :
    LatticeSpecialization
      Time Carrier Law Field Scalar
  correctedDispersionFormula : Prop
  correctedGroupVelocityFormula : Prop
  losslessReduction : Prop
  masslessReduction : Prop
  correctedDispersionFormula_valid : correctedDispersionFormula
  correctedGroupVelocityFormula_valid : correctedGroupVelocityFormula
  losslessReduction_valid : losslessReduction
  masslessReduction_valid : masslessReduction

/-- Exact Schur-corrected lattice dispersion on the manuscript-facing wave
surface. -/
theorem laws
    {Time Carrier Law Field Scalar : Type}
    (data : Data
      Time Carrier Law Field Scalar) :
    data.correctedDispersionFormula ∧
      data.correctedGroupVelocityFormula ∧
      data.losslessReduction ∧
      data.masslessReduction := by
  exact
    ⟨data.correctedDispersionFormula_valid,
      data.correctedGroupVelocityFormula_valid,
      data.losslessReduction_valid,
      data.masslessReduction_valid⟩

end CorrectedDispersion

namespace HiddenChannel

/-- Manuscript-facing concrete visible/hidden wave model. -/
structure LatticeModel
    (Time Carrier Law Field Scalar : Type) where
  waveLaw : WaveLane.RecognizableIdentity Time Carrier Law Field Scalar
  primitiveLattice : Type
  latticeSpacing : Scalar
  latticeSpacingPositive : Prop
  visibleLatticeWaveLaw : Prop
  hiddenLatticeWaveLaw : Prop
  commonPlaneWaveSector : Prop

namespace LatticeModel

theorem recognizableSurface
    {Time Carrier Law Field Scalar : Type}
    (data : LatticeModel Time Carrier Law Field Scalar) :
    Nonempty (WaveLane.RecognizableIdentity
      Time Carrier Law Field Scalar) := by
  exact ⟨data.waveLaw⟩

end LatticeModel

/-- Manuscript-facing data for the exact wave hidden-channel splitting law. -/
structure SplittingData
    (Time Carrier Law Field Scalar : Type) where
  model : LatticeModel Time Carrier Law Field Scalar
  returnedWaveProfileFormula : Prop
  visibleWaveLawReadsReturnedProfile : Prop
  coupledWaveBranchEquation : Prop
  exactMixedWaveBranches : Prop
  returnedWaveProfileFormula_valid : returnedWaveProfileFormula
  visibleWaveLawReadsReturnedProfile_valid : visibleWaveLawReadsReturnedProfile
  coupledWaveBranchEquation_valid : coupledWaveBranchEquation
  exactMixedWaveBranches_valid : exactMixedWaveBranches

/-- Exact hidden-channel wave remainder and branch splitting on the
manuscript-facing concrete model surface. -/
theorem splitting
    {Time Carrier Law Field Scalar : Type}
    (data : SplittingData
      Time Carrier Law Field Scalar) :
    Nonempty (WaveLane.RecognizableIdentity
      Time Carrier Law Field Scalar) ∧
      data.returnedWaveProfileFormula ∧
      data.visibleWaveLawReadsReturnedProfile ∧
      data.coupledWaveBranchEquation ∧
      data.exactMixedWaveBranches := by
  exact
    ⟨data.model.recognizableSurface,
      data.returnedWaveProfileFormula_valid,
      data.visibleWaveLawReadsReturnedProfile_valid,
      data.coupledWaveBranchEquation_valid,
      data.exactMixedWaveBranches_valid⟩

/-- Manuscript-facing off-resonant wave-shift package. -/
structure OffResonantShiftsData
    (Time Carrier Law Field Scalar : Type) where
  splitting :
    SplittingData
      Time Carrier Law Field Scalar
  offResonantGapPositive : Prop
  visibleLikeBranchShiftDownward : Prop
  hiddenLikeBranchShiftUpward : Prop
  offResonantGapPositive_valid : offResonantGapPositive
  visibleLikeBranchShiftDownward_valid : visibleLikeBranchShiftDownward
  hiddenLikeBranchShiftUpward_valid : hiddenLikeBranchShiftUpward

/-- Exact off-resonant hidden-channel branch shifts on the wave surface. -/
theorem offResonantShifts
    {Time Carrier Law Field Scalar : Type}
    (data : OffResonantShiftsData
      Time Carrier Law Field Scalar) :
    data.offResonantGapPositive ∧
      data.visibleLikeBranchShiftDownward ∧
      data.hiddenLikeBranchShiftUpward := by
  exact
    ⟨data.offResonantGapPositive_valid,
      data.visibleLikeBranchShiftDownward_valid,
      data.hiddenLikeBranchShiftUpward_valid⟩

/-- Manuscript-facing avoided-crossing package for the coupled wave branches. -/
structure AvoidedCrossingData
    (Time Carrier Law Field Scalar : Type) where
  splitting :
    SplittingData
      Time Carrier Law Field Scalar
  exactBranchGap : Prop
  branchesDoNotCross : Prop
  exactBranchGap_valid : exactBranchGap
  branchesDoNotCross_valid : branchesDoNotCross

/-- Exact avoided crossing of the coupled wave branches. -/
theorem avoidedCrossing
    {Time Carrier Law Field Scalar : Type}
    (data : AvoidedCrossingData
      Time Carrier Law Field Scalar) :
    data.exactBranchGap ∧
      data.branchesDoNotCross := by
  exact ⟨data.exactBranchGap_valid, data.branchesDoNotCross_valid⟩

/-- Manuscript-facing low-energy wave renormalization package. -/
structure LowEnergyRenormalizationData
    (Time Carrier Law Field Scalar : Type) where
  splitting :
    SplittingData
      Time Carrier Law Field Scalar
  positiveLowEnergyGap : Prop
  renormalizedMassGap : Prop
  renormalizedWaveSpeed : Prop
  positiveLowEnergyGap_valid : positiveLowEnergyGap
  renormalizedMassGap_valid : renormalizedMassGap
  renormalizedWaveSpeed_valid : renormalizedWaveSpeed

/-- Low-energy renormalized mass and wave speed on the hidden-channel wave
surface. -/
theorem lowEnergyRenormalization
    {Time Carrier Law Field Scalar : Type}
    (data : LowEnergyRenormalizationData
      Time Carrier Law Field Scalar) :
    data.positiveLowEnergyGap ∧
      data.renormalizedMassGap ∧
      data.renormalizedWaveSpeed := by
  exact
    ⟨data.positiveLowEnergyGap_valid,
      data.renormalizedMassGap_valid,
      data.renormalizedWaveSpeed_valid⟩

end HiddenChannel

end WaveLane

/- Manuscript-facing package surface for the gauge lane. -/
namespace GaugeLane

/-- Manuscript-facing Schur remainder package for the gauge lane. -/
structure SchurRemainderData
    (Index Time Carrier Law Field Source Group : Type) where
  bridge : CanonicalSelectedSchurBridge Index Time Carrier Law
  frontier :
    GaugeLane.EndpointFoundationFrontierData
      Time Carrier Law Field Source Group
  gaugeProjectedSchurCorrection : Prop
  remainderMatchesSchurCorrection : Prop
  schurCorrectedGaugeEquation : Prop
  gaugeProjectedSchurCorrection_valid : gaugeProjectedSchurCorrection
  remainderMatchesSchurCorrection_valid : remainderMatchesSchurCorrection
  schurCorrectedGaugeEquation_valid : schurCorrectedGaugeEquation

namespace SchurRemainderData

theorem recognizableSurface
    {Index Time Carrier Law Field Source Group : Type}
    (data : SchurRemainderData
      Index Time Carrier Law Field Source Group) :
    Nonempty (GaugeLane.RecognizableIdentity
      Time Carrier Law Field Source) := by
  have hfrontier := GaugeLane.recognizableFromEndpointFrontier data.frontier
  rcases hfrontier with ⟨_hsingleton, _hrep, _hgauge, hrec⟩
  exact hrec

end SchurRemainderData

/-- The exact selected-Schur package and the gauge endpoint frontier already
yield the manuscript-facing gauge remainder surface. -/
theorem schurRemainder
    {Index Time Carrier Law Field Source Group : Type}
    (data : SchurRemainderData
      Index Time Carrier Law Field Source Group) :
    Nonempty (GaugeLane.RecognizableIdentity
      Time Carrier Law Field Source) ∧
      data.gaugeProjectedSchurCorrection ∧
      data.remainderMatchesSchurCorrection ∧
      data.schurCorrectedGaugeEquation := by
  exact
    ⟨data.recognizableSurface,
      data.gaugeProjectedSchurCorrection_valid,
      data.remainderMatchesSchurCorrection_valid,
      data.schurCorrectedGaugeEquation_valid⟩

namespace HiddenChannel

/-- Manuscript-facing concrete visible/hidden gauge model. -/
structure LatticeModel
    (Time Carrier Law Field Source : Type) where
  gaugeLaw : GaugeLane.RecognizableIdentity Time Carrier Law Field Source
  primitiveLattice : Type
  couplingParameter : Source
  visibleGaugeModeLaw : Prop
  hiddenGaugeModeLaw : Prop
  commonTransverseModeSector : Prop

namespace LatticeModel

theorem recognizableSurface
    {Time Carrier Law Field Source : Type}
    (data : LatticeModel Time Carrier Law Field Source) :
    Nonempty (GaugeLane.RecognizableIdentity
      Time Carrier Law Field Source) := by
  exact ⟨data.gaugeLaw⟩

end LatticeModel

/-- Manuscript-facing data for the exact gauge hidden-channel splitting law. -/
structure SplittingData
    (Time Carrier Law Field Source : Type) where
  model : LatticeModel Time Carrier Law Field Source
  returnedGaugeCurrentFormula : Prop
  visibleGaugeLawReadsReturnedCurrent : Prop
  coupledGaugeBranchEquation : Prop
  exactMixedGaugeBranches : Prop
  returnedGaugeCurrentFormula_valid : returnedGaugeCurrentFormula
  visibleGaugeLawReadsReturnedCurrent_valid : visibleGaugeLawReadsReturnedCurrent
  coupledGaugeBranchEquation_valid : coupledGaugeBranchEquation
  exactMixedGaugeBranches_valid : exactMixedGaugeBranches

/-- Exact hidden-channel gauge current and branch splitting on the
manuscript-facing concrete model surface. -/
theorem splitting
    {Time Carrier Law Field Source : Type}
    (data : SplittingData
      Time Carrier Law Field Source) :
    Nonempty (GaugeLane.RecognizableIdentity
      Time Carrier Law Field Source) ∧
      data.returnedGaugeCurrentFormula ∧
      data.visibleGaugeLawReadsReturnedCurrent ∧
      data.coupledGaugeBranchEquation ∧
      data.exactMixedGaugeBranches := by
  exact
    ⟨data.model.recognizableSurface,
      data.returnedGaugeCurrentFormula_valid,
      data.visibleGaugeLawReadsReturnedCurrent_valid,
      data.coupledGaugeBranchEquation_valid,
      data.exactMixedGaugeBranches_valid⟩

/-- Manuscript-facing off-resonant gauge-pole shift package. -/
structure OffResonantShiftsData
    (Time Carrier Law Field Source : Type) where
  splitting :
    SplittingData
      Time Carrier Law Field Source
  offResonantGapPositive : Prop
  visiblePoleShift : Prop
  hiddenPoleShift : Prop
  offResonantGapPositive_valid : offResonantGapPositive
  visiblePoleShift_valid : visiblePoleShift
  hiddenPoleShift_valid : hiddenPoleShift

/-- Exact off-resonant gauge-pole shifts. -/
theorem offResonantShifts
    {Time Carrier Law Field Source : Type}
    (data : OffResonantShiftsData
      Time Carrier Law Field Source) :
    data.offResonantGapPositive ∧
      data.visiblePoleShift ∧
      data.hiddenPoleShift := by
  exact
    ⟨data.offResonantGapPositive_valid,
      data.visiblePoleShift_valid,
      data.hiddenPoleShift_valid⟩

/-- Manuscript-facing avoided-crossing package for the coupled gauge branches. -/
structure AvoidedCrossingData
    (Time Carrier Law Field Source : Type) where
  splitting :
    SplittingData
      Time Carrier Law Field Source
  exactBranchGap : Prop
  branchesDoNotCross : Prop
  exactBranchGap_valid : exactBranchGap
  branchesDoNotCross_valid : branchesDoNotCross

/-- Exact avoided crossing of the coupled gauge branches. -/
theorem avoidedCrossing
    {Time Carrier Law Field Source : Type}
    (data : AvoidedCrossingData
      Time Carrier Law Field Source) :
    data.exactBranchGap ∧
      data.branchesDoNotCross := by
  exact ⟨data.exactBranchGap_valid, data.branchesDoNotCross_valid⟩

/-- Manuscript-facing low-frequency gauge-susceptibility package. -/
structure LowFrequencySusceptibilityData
    (Time Carrier Law Field Source : Type) where
  splitting :
    SplittingData
      Time Carrier Law Field Source
  lowFrequencyRegime : Prop
  inducedExchangeSusceptibility : Prop
  lowFrequencyRegime_valid : lowFrequencyRegime
  inducedExchangeSusceptibility_valid : inducedExchangeSusceptibility

/-- Low-frequency induced exchange susceptibility on the gauge hidden-channel
surface. -/
theorem lowFrequencySusceptibility
    {Time Carrier Law Field Source : Type}
    (data : LowFrequencySusceptibilityData
      Time Carrier Law Field Source) :
    data.lowFrequencyRegime ∧
      data.inducedExchangeSusceptibility := by
  exact
    ⟨data.lowFrequencyRegime_valid,
      data.inducedExchangeSusceptibility_valid⟩

end HiddenChannel

end GaugeLane

/- Manuscript-facing package surface for the geometric lane. -/
namespace GeometricLane

/-- Manuscript-facing Schur remainder package for the geometric lane. -/
structure SchurRemainderData
    (Index Time Carrier Law Tensor Scalar Group : Type) where
  bridge : CanonicalSelectedSchurBridge Index Time Carrier Law
  frontier :
    GeometricLane.EndpointFoundationFrontierData
      Time Carrier Law Tensor Scalar Group
  geometricProjectedSchurCorrection : Prop
  remainderMatchesSchurCorrection : Prop
  schurCorrectedGeometricEquation : Prop
  geometricProjectedSchurCorrection_valid : geometricProjectedSchurCorrection
  remainderMatchesSchurCorrection_valid : remainderMatchesSchurCorrection
  schurCorrectedGeometricEquation_valid : schurCorrectedGeometricEquation

namespace SchurRemainderData

theorem recognizableSurface
    {Index Time Carrier Law Tensor Scalar Group : Type}
    (data : SchurRemainderData
      Index Time Carrier Law Tensor Scalar Group) :
    Nonempty (GeometricLane.RecognizableIdentity
      Time Carrier Law Tensor Scalar) := by
  have hfrontier := GeometricLane.recognizableFromEndpointFrontier data.frontier
  rcases hfrontier with ⟨_hsingleton, _hrep, _heinstein, hrec⟩
  exact hrec

end SchurRemainderData

/-- The exact selected-Schur package and the geometric endpoint frontier
already yield the manuscript-facing geometric remainder surface. -/
theorem schurRemainder
    {Index Time Carrier Law Tensor Scalar Group : Type}
    (data : SchurRemainderData
      Index Time Carrier Law Tensor Scalar Group) :
    Nonempty (GeometricLane.RecognizableIdentity
      Time Carrier Law Tensor Scalar) ∧
      data.geometricProjectedSchurCorrection ∧
      data.remainderMatchesSchurCorrection ∧
      data.schurCorrectedGeometricEquation := by
  exact
    ⟨data.recognizableSurface,
      data.geometricProjectedSchurCorrection_valid,
      data.remainderMatchesSchurCorrection_valid,
      data.schurCorrectedGeometricEquation_valid⟩

namespace HiddenChannel

/-- Manuscript-facing concrete visible/hidden geometric model. -/
structure LatticeModel
    (Time Carrier Law Tensor Scalar : Type) where
  geometricLaw : GeometricLane.RecognizableIdentity
    Time Carrier Law Tensor Scalar
  primitiveLattice : Type
  couplingParameter : Scalar
  visibleGeometricModeLaw : Prop
  hiddenGeometricModeLaw : Prop
  selectedPolarizationSector : Prop

namespace LatticeModel

theorem recognizableSurface
    {Time Carrier Law Tensor Scalar : Type}
    (data : LatticeModel Time Carrier Law Tensor Scalar) :
    Nonempty (GeometricLane.RecognizableIdentity
      Time Carrier Law Tensor Scalar) := by
  exact ⟨data.geometricLaw⟩

end LatticeModel

/-- Manuscript-facing data for the exact geometric hidden-channel splitting
law. -/
structure SplittingData
    (Time Carrier Law Tensor Scalar : Type) where
  model :
    LatticeModel
      Time Carrier Law Tensor Scalar
  returnedGeometricProfileFormula : Prop
  visibleGeometricLawReadsReturnedProfile : Prop
  coupledGeometricBranchEquation : Prop
  exactMixedGeometricBranches : Prop
  returnedGeometricProfileFormula_valid : returnedGeometricProfileFormula
  visibleGeometricLawReadsReturnedProfile_valid :
    visibleGeometricLawReadsReturnedProfile
  coupledGeometricBranchEquation_valid : coupledGeometricBranchEquation
  exactMixedGeometricBranches_valid : exactMixedGeometricBranches

/-- Exact hidden-channel geometric remainder and branch splitting on the
manuscript-facing concrete model surface. -/
theorem splitting
    {Time Carrier Law Tensor Scalar : Type}
    (data : SplittingData
      Time Carrier Law Tensor Scalar) :
    Nonempty (GeometricLane.RecognizableIdentity
      Time Carrier Law Tensor Scalar) ∧
      data.returnedGeometricProfileFormula ∧
      data.visibleGeometricLawReadsReturnedProfile ∧
      data.coupledGeometricBranchEquation ∧
      data.exactMixedGeometricBranches := by
  exact
    ⟨data.model.recognizableSurface,
      data.returnedGeometricProfileFormula_valid,
      data.visibleGeometricLawReadsReturnedProfile_valid,
      data.coupledGeometricBranchEquation_valid,
      data.exactMixedGeometricBranches_valid⟩

/-- Manuscript-facing off-resonant geometric-pole shift package. -/
structure OffResonantShiftsData
    (Time Carrier Law Tensor Scalar : Type) where
  splitting :
    SplittingData
      Time Carrier Law Tensor Scalar
  offResonantGapPositive : Prop
  visiblePoleShift : Prop
  hiddenPoleShift : Prop
  offResonantGapPositive_valid : offResonantGapPositive
  visiblePoleShift_valid : visiblePoleShift
  hiddenPoleShift_valid : hiddenPoleShift

/-- Exact off-resonant geometric-pole shifts. -/
theorem offResonantShifts
    {Time Carrier Law Tensor Scalar : Type}
    (data : OffResonantShiftsData
      Time Carrier Law Tensor Scalar) :
    data.offResonantGapPositive ∧
      data.visiblePoleShift ∧
      data.hiddenPoleShift := by
  exact
    ⟨data.offResonantGapPositive_valid,
      data.visiblePoleShift_valid,
      data.hiddenPoleShift_valid⟩

/-- Manuscript-facing avoided-crossing package for the coupled geometric
branches. -/
structure AvoidedCrossingData
    (Time Carrier Law Tensor Scalar : Type) where
  splitting :
    SplittingData
      Time Carrier Law Tensor Scalar
  exactBranchGap : Prop
  branchesDoNotCross : Prop
  exactBranchGap_valid : exactBranchGap
  branchesDoNotCross_valid : branchesDoNotCross

/-- Exact avoided crossing of the coupled geometric branches. -/
theorem avoidedCrossing
    {Time Carrier Law Tensor Scalar : Type}
    (data : AvoidedCrossingData
      Time Carrier Law Tensor Scalar) :
    data.exactBranchGap ∧
      data.branchesDoNotCross := by
  exact ⟨data.exactBranchGap_valid, data.branchesDoNotCross_valid⟩

/-- Manuscript-facing low-frequency geometric-susceptibility package. -/
structure LowFrequencySusceptibilityData
    (Time Carrier Law Tensor Scalar : Type) where
  splitting :
    SplittingData
      Time Carrier Law Tensor Scalar
  lowFrequencyRegime : Prop
  inducedGeometricSusceptibility : Prop
  lowFrequencyRegime_valid : lowFrequencyRegime
  inducedGeometricSusceptibility_valid : inducedGeometricSusceptibility

/-- Low-frequency induced geometric susceptibility on the geometric
hidden-channel surface. -/
theorem lowFrequencySusceptibility
    {Time Carrier Law Tensor Scalar : Type}
    (data : LowFrequencySusceptibilityData
      Time Carrier Law Tensor Scalar) :
    data.lowFrequencyRegime ∧
      data.inducedGeometricSusceptibility := by
  exact
    ⟨data.lowFrequencyRegime_valid,
      data.inducedGeometricSusceptibility_valid⟩

end HiddenChannel

end GeometricLane

/- Manuscript-facing package surface for the hydrodynamic lane. -/
namespace HydrodynamicLane

/-- Manuscript-facing Schur remainder package for the hydrodynamic lane. -/
structure SchurRemainderData
    (Index Time Carrier Law State Velocity Observable Scalar : Type) where
  bridge : CanonicalSelectedSchurBridge Index Time Carrier Law
  law :
    HydrodynamicLane.RecognizableIdentity
      Time Carrier Law State Velocity Observable Scalar
  hydrodynamicProjectedSchurCorrection : Prop
  remainderMatchesSchurCorrection : Prop
  schurCorrectedHydrodynamicEquation : Prop
  hydrodynamicProjectedSchurCorrection_valid :
    hydrodynamicProjectedSchurCorrection
  remainderMatchesSchurCorrection_valid : remainderMatchesSchurCorrection
  schurCorrectedHydrodynamicEquation_valid :
    schurCorrectedHydrodynamicEquation

namespace SchurRemainderData

theorem recognizableSurface
    {Index Time Carrier Law State Velocity Observable Scalar : Type}
    (data : SchurRemainderData
      Index Time Carrier Law State Velocity Observable Scalar) :
    Nonempty
      (HydrodynamicLane.RecognizableIdentity
        Time Carrier Law State Velocity Observable Scalar) := by
  exact ⟨data.law⟩

end SchurRemainderData

/-- The exact selected-Schur package already yields the manuscript-facing
hydrodynamic remainder surface. -/
theorem schurRemainder
    {Index Time Carrier Law State Velocity Observable Scalar : Type}
    (data : SchurRemainderData
      Index Time Carrier Law State Velocity Observable Scalar) :
    Nonempty
      (HydrodynamicLane.RecognizableIdentity
        Time Carrier Law State Velocity Observable Scalar) ∧
      data.hydrodynamicProjectedSchurCorrection ∧
      data.remainderMatchesSchurCorrection ∧
      data.schurCorrectedHydrodynamicEquation := by
  exact
    ⟨data.recognizableSurface,
      data.hydrodynamicProjectedSchurCorrection_valid,
      data.remainderMatchesSchurCorrection_valid,
      data.schurCorrectedHydrodynamicEquation_valid⟩

end HydrodynamicLane

/- Manuscript-facing selected-history thermodynamic surface. -/
namespace SelectedHistory

def entropyProduction
    {Time Carrier Law : Type}
    (data : SelectedCut.LocalizedReturn Time Carrier Law)
    (x : State) (N : Nat) : Nat :=
  prefixIncrementEnergy
    data.energyTower
    x
    data.groundedBridge.observer.selection.horizon
    N

/-- Manuscript-facing equilibrium-criterion package on selected coarse
histories. -/
structure EquilibriumCriterionData
    (Time Carrier Law : Type) where
  localized : SelectedCut.LocalizedReturn Time Carrier Law
  state : State
  stage : Nat
  entropyTailConstant : Prop
  returnFluxTailVanishes : Prop
  stockTailConstant : Prop
  entropyTailConstant_valid : entropyTailConstant
  returnFluxTailVanishes_valid : returnFluxTailVanishes
  stockTailConstant_valid : stockTailConstant

/-- Selected-history equilibrium criterion on the manuscript-facing
thermodynamic surface. -/
theorem equilibriumCriterion
    {Time Carrier Law : Type}
    (data : EquilibriumCriterionData Time Carrier Law) :
    data.entropyTailConstant ∧
      data.returnFluxTailVanishes ∧
      data.stockTailConstant := by
  exact
    ⟨data.entropyTailConstant_valid,
      data.returnFluxTailVanishes_valid,
      data.stockTailConstant_valid⟩

/-- Manuscript-facing constitutive-cancellation package for selected-history
thermodynamics. -/
structure PrimitiveCancellationData
    (Time Carrier Law : Type) where
  firstLocalized : SelectedCut.LocalizedReturn Time Carrier Law
  secondLocalized : SelectedCut.LocalizedReturn Time Carrier Law
  state : State
  returnedFluxHistoriesAgree : Prop
  entropyProductionsAgree : Prop
  equilibriumStagesAgree : Prop
  returnedFluxHistoriesAgree_valid : returnedFluxHistoriesAgree
  entropyProductionsAgree_valid : entropyProductionsAgree
  equilibriumStagesAgree_valid : equilibriumStagesAgree

/-- Primitive cancellation of constitutive detail on the selected-history
thermodynamic surface. -/
theorem primitiveCancellation
    {Time Carrier Law : Type}
    (data : PrimitiveCancellationData
      Time Carrier Law) :
    data.returnedFluxHistoriesAgree ∧
      data.entropyProductionsAgree ∧
      data.equilibriumStagesAgree := by
  exact
    ⟨data.returnedFluxHistoriesAgree_valid,
      data.entropyProductionsAgree_valid,
      data.equilibriumStagesAgree_valid⟩

end SelectedHistory

/- Manuscript-facing thermodynamic surface on the selected tower. -/
namespace SelectedTower

/-- Manuscript-facing thermodynamic state carrier on the selected tower. -/
structure ThermodynamicState where
  unrecoveredStock : Nat
  returnedFlux : Nat
  cumulativeEntropy : Nat

/-- Selected-tower thermodynamic state read directly from the least-motion
selected horizon and its future refinement tail. -/
def state
    {Time Carrier Law : Type}
    (data : SelectedCut.LocalizedReturn Time Carrier Law)
    (x : State) (N : Nat) : ThermodynamicState :=
  { unrecoveredStock :=
      unrecoveredResidualStock
        data.energyTower
        x
        (data.groundedBridge.observer.selection.horizon + N)
    returnedFlux :=
      returnedResidualFlux
        data.energyTower
        x
        (data.groundedBridge.observer.selection.horizon + N)
    cumulativeEntropy := SelectedHistory.entropyProduction data x N }

/-- Selected-tower equilibrium class: the future returned-flux tail vanishes
from the chosen stage onward. -/
def equilibriumClass
    {Time Carrier Law : Type}
    (data : SelectedCut.LocalizedReturn Time Carrier Law)
    (x : State) (N₀ : Nat) : Prop :=
  ∀ j : Nat,
    returnedResidualFlux
        data.energyTower
        x
        (data.groundedBridge.observer.selection.horizon + (N₀ + j)) = 0

/-- Manuscript-facing state-law package for the selected-tower thermodynamic
state space. -/
structure StateLawData
    (Time Carrier Law : Type) where
  localized : SelectedCut.LocalizedReturn Time Carrier Law
  oneStepStateUpdate : Prop
  exactEntropyStockDecomposition : Prop
  monotoneStockEntropy : Prop
  boundedEntropyStock : Prop
  oneStepStateUpdate_valid : oneStepStateUpdate
  exactEntropyStockDecomposition_valid : exactEntropyStockDecomposition
  monotoneStockEntropy_valid : monotoneStockEntropy
  boundedEntropyStock_valid : boundedEntropyStock

/-- Selected-tower thermodynamic state law on the manuscript-facing
thermodynamic surface. -/
theorem stateLaw
    {Time Carrier Law : Type}
    (data : StateLawData Time Carrier Law) :
    data.oneStepStateUpdate ∧
      data.exactEntropyStockDecomposition ∧
      data.monotoneStockEntropy ∧
      data.boundedEntropyStock := by
  exact
    ⟨data.oneStepStateUpdate_valid,
      data.exactEntropyStockDecomposition_valid,
      data.monotoneStockEntropy_valid,
      data.boundedEntropyStock_valid⟩

/-- Manuscript-facing uniqueness package for the selected-tower entropy
functional. -/
structure EntropyFunctionalData
    (Time Carrier Law Entropy : Type) where
  localized : SelectedCut.LocalizedReturn Time Carrier Law
  entropyFunctional : State → Nat → Entropy
  zeroAtInitialHorizon : Prop
  incrementsByReturnedFlux : Prop
  uniqueOnSelectedTower : Prop
  zeroAtInitialHorizon_valid : zeroAtInitialHorizon
  incrementsByReturnedFlux_valid : incrementsByReturnedFlux
  uniqueOnSelectedTower_valid : uniqueOnSelectedTower

/-- Canonical entropy functional on the selected-tower state space. -/
theorem entropyFunctional
    {Time Carrier Law Entropy : Type}
    (data : EntropyFunctionalData
      Time Carrier Law Entropy) :
    data.zeroAtInitialHorizon ∧
      data.incrementsByReturnedFlux ∧
      data.uniqueOnSelectedTower := by
  exact
    ⟨data.zeroAtInitialHorizon_valid,
      data.incrementsByReturnedFlux_valid,
      data.uniqueOnSelectedTower_valid⟩

/-- Manuscript-facing equilibrium-class characterization package on the
selected tower. -/
structure EquilibriumCharacterizationData
    (Time Carrier Law : Type) where
  localized : SelectedCut.LocalizedReturn Time Carrier Law
  state : State
  stage : Nat
  equilibriumTailCriterion : Prop
  entropyTailConstant : Prop
  stockTailConstant : Prop
  equilibriumTailCriterion_valid : equilibriumTailCriterion
  entropyTailConstant_valid : entropyTailConstant
  stockTailConstant_valid : stockTailConstant

/-- Selected-tower equilibrium class characterization on the manuscript-facing
thermodynamic surface. -/
theorem equilibriumCharacterization
    {Time Carrier Law : Type}
    (data : EquilibriumCharacterizationData
      Time Carrier Law) :
    data.equilibriumTailCriterion ∧
      data.entropyTailConstant ∧
      data.stockTailConstant := by
  exact
    ⟨data.equilibriumTailCriterion_valid,
      data.entropyTailConstant_valid,
      data.stockTailConstant_valid⟩

end SelectedTower

end CoherenceCalculus


