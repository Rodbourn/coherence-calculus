import CoherenceCalculus.Foundation.BridgeObservableCore

/-!
# Foundation.BridgeObservableCorollaryCore

Structural Chapter 7 corollaries for the early observable/phase bridge.

These declarations package the witness data named in the manuscript and expose
the corresponding forcing statements as proposition-valued theorems.
-/

namespace CoherenceCalculus

/-- Explicit witness for intrinsic-equivariant forcing on the canonical carrier. -/
structure IntrinsicEquivariantForcingData (Index Time : Type)
    extends IntrinsicallyEquivariantRealizedClass Index Time where
  singletonReducedSelectionWitness : Prop
  intrinsicThreeParameterLaw : Prop
  forcedChannelEigenvalues : Prop
  intrinsicThreeParameterLaw_valid : intrinsicThreeParameterLaw
  forcedChannelEigenvalues_valid : forcedChannelEigenvalues

/-- Intrinsic-equivariant realized classes carry the forced three-parameter
canonical law and its channel eigenvalues. -/
theorem intrinsic_equivariant_forcing
    {Index Time : Type}
    (data : IntrinsicEquivariantForcingData Index Time) :
    data.intrinsicThreeParameterLaw ∧ data.forcedChannelEigenvalues := by
  exact ⟨data.intrinsicThreeParameterLaw_valid, data.forcedChannelEigenvalues_valid⟩

/-- Explicit witness for finite subgroup-broken selection on the canonical
carrier. -/
structure FiniteSubgroupBrokenSelectionData (Index Time : Type)
    extends SubgroupBrokenRealizedClass Index Time where
  blockwiseIsotypicDecomposition : Prop
  finiteReducedChannelProblem : Prop
  atMostSixLocalChannels : Prop
  recoversIntrinsicThreeParameterLaw : Prop
  blockwiseIsotypicDecomposition_valid : blockwiseIsotypicDecomposition
  finiteReducedChannelProblem_valid : finiteReducedChannelProblem
  atMostSixLocalChannels_valid : atMostSixLocalChannels
  recoversIntrinsicThreeParameterLaw_valid : recoversIntrinsicThreeParameterLaw

/-- Subgroup-broken selected laws still admit a finite blockwise reduction. -/
theorem finite_subgroup_broken_selection
    {Index Time : Type}
    (data : FiniteSubgroupBrokenSelectionData Index Time) :
    data.blockwiseIsotypicDecomposition ∧
      data.finiteReducedChannelProblem ∧
      data.atMostSixLocalChannels ∧
      data.recoversIntrinsicThreeParameterLaw := by
  exact ⟨data.blockwiseIsotypicDecomposition_valid,
    data.finiteReducedChannelProblem_valid, data.atMostSixLocalChannels_valid,
    data.recoversIntrinsicThreeParameterLaw_valid⟩

/-- Explicit witness for realized phase-class forcing on a complex-type class. -/
structure RealizedPhaseClassForcingData (Index Time Channel : Type)
    extends ComplexTypeRealizedClass Index Time Channel where
  singletonReducedSelectionWitness : Prop
  forcedPhaseCarrierClass : Prop
  forcedPhaseCarrierClass_valid : forcedPhaseCarrierClass

/-- Complex-type realized classes with scalar multiplicity commutant carry a
forced phase-carrier class. -/
theorem realized_phase_class_forcing
    {Index Time Channel : Type}
    (data : RealizedPhaseClassForcingData Index Time Channel) :
    data.forcedPhaseCarrierClass := by
  exact data.forcedPhaseCarrierClass_valid

/-- Explicit witness for scalarization on observable-irreducible channels. -/
structure RealizedSelfAdjointScalarizationData (Index Time Channel : Type)
    extends ObservableIrreducibleRealizedClass Index Time Channel where
  selectedSelfAdjointOperatorsScalar : Prop
  selectedSelfAdjointOperatorsScalar_valid : selectedSelfAdjointOperatorsScalar

/-- Observable-irreducible selected channels force self-adjoint scalarization. -/
theorem realized_self_adjoint_scalarization
    {Index Time Channel : Type}
    (data : RealizedSelfAdjointScalarizationData Index Time Channel) :
    data.selectedSelfAdjointOperatorsScalar := by
  exact data.selectedSelfAdjointOperatorsScalar_valid

/-- Explicit witness for isotropic symmetric-response scalarization. -/
structure RealizedIsotropicSymmetricResponseScalarizationData where
  orthogonalConjugationEquivariance : Prop
  twoScalarResponseDecomposition : Prop
  intrinsicScalarChannels : Prop
  twoScalarResponseDecomposition_valid : twoScalarResponseDecomposition
  intrinsicScalarChannels_valid : intrinsicScalarChannels

/-- Orthogonally equivariant symmetric responses split into the trace and
traceless scalar channels. -/
theorem realized_isotropic_symmetric_response_scalarization
    (data : RealizedIsotropicSymmetricResponseScalarizationData) :
    data.twoScalarResponseDecomposition ∧ data.intrinsicScalarChannels := by
  exact ⟨data.twoScalarResponseDecomposition_valid,
    data.intrinsicScalarChannels_valid⟩

/-- Explicit witness for phase forcing from real-type observable irreducibility. -/
structure RealTypePhaseForcingData (Index Time Channel : Type)
    extends ComplexTypeRealizedClass Index Time Channel where
  realTypeObservableIrreducibilityWitness : Prop
  singletonReducedSelectionWitness : Prop
  forcedPhaseCarrierClass : Prop
  forcedPhaseCarrierClass_valid : forcedPhaseCarrierClass

/-- Real-type observable irreducibility forces a phase-carrier class. -/
theorem realized_phase_from_real_type
    {Index Time Channel : Type}
    (data : RealTypePhaseForcingData Index Time Channel) :
    data.forcedPhaseCarrierClass := by
  exact data.forcedPhaseCarrierClass_valid

/-- Explicit witness for phase forcing from adjoint-closed real type. -/
structure AdjointClosedRealTypePhaseForcingData (Index Time Channel : Type)
    extends ComplexTypeRealizedClass Index Time Channel where
  adjointClosedRealTypeWitness : Prop
  singletonReducedSelectionWitness : Prop
  forcedPhaseCarrierClass : Prop
  forcedPhaseCarrierClass_valid : forcedPhaseCarrierClass

/-- Adjoint-closed real type forces a phase-carrier class. -/
theorem realized_phase_from_adjoint_closed_real_type
    {Index Time Channel : Type}
    (data : AdjointClosedRealTypePhaseForcingData Index Time Channel) :
    data.forcedPhaseCarrierClass := by
  exact data.forcedPhaseCarrierClass_valid

/-- Explicit witness for phase forcing from a rank-one observable seed. -/
structure RankOneSeedPhaseForcingData (Index Time Channel : Type)
    extends ComplexTypeRealizedClass Index Time Channel where
  rankOneObservableSeedWitness : Prop
  singletonReducedSelectionWitness : Prop
  forcedPhaseCarrierClass : Prop
  forcedPhaseCarrierClass_valid : forcedPhaseCarrierClass

/-- Rank-one observable seeds force a phase-carrier class. -/
theorem realized_phase_from_rank_one_seed
    {Index Time Channel : Type}
    (data : RankOneSeedPhaseForcingData Index Time Channel) :
    data.forcedPhaseCarrierClass := by
  exact data.forcedPhaseCarrierClass_valid

/-- Explicit witness for phase forcing from simple spectrum. -/
structure SimpleSpectrumPhaseForcingData (Index Time Channel : Type)
    extends ComplexTypeRealizedClass Index Time Channel where
  simpleSpectrumWitness : Prop
  singletonReducedSelectionWitness : Prop
  forcedPhaseCarrierClass : Prop
  forcedPhaseCarrierClass_valid : forcedPhaseCarrierClass

/-- Simple-spectrum observable data force a phase-carrier class. -/
theorem realized_phase_from_simple_spectrum
    {Index Time Channel : Type}
    (data : SimpleSpectrumPhaseForcingData Index Time Channel) :
    data.forcedPhaseCarrierClass := by
  exact data.forcedPhaseCarrierClass_valid

/-- Explicit witness for phase forcing from observable completeness. -/
structure ObservableCompletenessPhaseForcingData (Index Time Channel : Type)
    extends ComplexTypeRealizedClass Index Time Channel where
  observableCompletenessWitness : Prop
  singletonReducedSelectionWitness : Prop
  forcedPhaseCarrierClass : Prop
  forcedPhaseCarrierClass_valid : forcedPhaseCarrierClass

/-- Observable completeness forces a phase-carrier class. -/
theorem realized_phase_from_observable_completeness
    {Index Time Channel : Type}
    (data : ObservableCompletenessPhaseForcingData Index Time Channel) :
    data.forcedPhaseCarrierClass := by
  exact data.forcedPhaseCarrierClass_valid

/-- Explicit witness for phase forcing from a matrix-unit scaffold. -/
structure MatrixUnitPhaseForcingData (Index Time Channel : Type)
    extends ComplexTypeRealizedClass Index Time Channel where
  matrixUnitScaffoldWitness : Prop
  singletonReducedSelectionWitness : Prop
  forcedPhaseCarrierClass : Prop
  forcedPhaseCarrierClass_valid : forcedPhaseCarrierClass

/-- Matrix-unit scaffolds force a phase-carrier class. -/
theorem realized_phase_from_matrix_units
    {Index Time Channel : Type}
    (data : MatrixUnitPhaseForcingData Index Time Channel) :
    data.forcedPhaseCarrierClass := by
  exact data.forcedPhaseCarrierClass_valid

/-- Explicit witness for finite observable rigidity and phase forcing. -/
structure FiniteObservableRigidityPhaseForcingData (Index Time Channel : Type)
    extends ComplexTypeRealizedClass Index Time Channel where
  finiteObservableRigidityWitness : Prop
  singletonReducedSelectionWitness : Prop
  fullFiniteObservableRigidityPackage : Prop
  forcedPhaseCarrierClass : Prop
  fullFiniteObservableRigidityPackage_valid : fullFiniteObservableRigidityPackage
  forcedPhaseCarrierClass_valid : forcedPhaseCarrierClass

/-- Finite observable rigidity forces both the full rigidity package and the
phase-carrier class. -/
theorem realized_finite_observable_rigidity
    {Index Time Channel : Type}
    (data : FiniteObservableRigidityPhaseForcingData Index Time Channel) :
    data.fullFiniteObservableRigidityPackage ∧ data.forcedPhaseCarrierClass := by
  exact ⟨data.fullFiniteObservableRigidityPackage_valid,
    data.forcedPhaseCarrierClass_valid⟩

/-- Explicit witness that phase-generated realized classes force a phase-carrier
class. -/
structure PhaseGeneratedForcingData (Index Time Channel : Type)
    extends PhaseGeneratedRealizedClass Index Time Channel where
  forcedPhaseCarrierClass : Prop
  forcedPhaseCarrierClass_valid : forcedPhaseCarrierClass

/-- Phase-generated realized classes carry a forced phase-carrier class. -/
theorem realized_phase_generation_forcing
    {Index Time Channel : Type}
    (data : PhaseGeneratedForcingData Index Time Channel) :
    data.forcedPhaseCarrierClass := by
  exact data.forcedPhaseCarrierClass_valid

/-- Explicit witness that phase-generated realized classes are phase-rigid. -/
structure PhaseGenerationRigidityData (Index Time Channel : Type)
    extends PhaseRigidRealizedClass Index Time Channel where
  phaseGeneratedWitness : Prop

/-- Phase-generated realized classes are phase-rigid. -/
theorem realized_phase_generation_implies_rigidity
    {Index Time Channel : Type}
    (data : PhaseGenerationRigidityData Index Time Channel) :
    Nonempty (PhaseRigidRealizedClass Index Time Channel) := by
  exact ⟨data.toPhaseRigidRealizedClass⟩

/-- Explicit witness that phase-rigid realized classes force a phase-carrier
class. -/
structure PhaseRigidityForcingData (Index Time Channel : Type)
    extends PhaseRigidRealizedClass Index Time Channel where
  forcedPhaseCarrierClass : Prop
  forcedPhaseCarrierClass_valid : forcedPhaseCarrierClass

/-- Phase-rigid realized classes carry a forced phase-carrier class. -/
theorem realized_phase_rigidity_forcing
    {Index Time Channel : Type}
    (data : PhaseRigidityForcingData Index Time Channel) :
    data.forcedPhaseCarrierClass := by
  exact data.forcedPhaseCarrierClass_valid

/-- Explicit witness that observable-complete classes are observable-rigid. -/
structure ObservableCompleteObservableRigidityData (Index Time : Type)
    extends ObservableRigidRealizedClass Index Time where
  observableCompletenessWitness : Prop

/-- Observable-complete classes are observable-rigid. -/
theorem observable_complete_implies_observable_rigid
    {Index Time : Type}
    (data : ObservableCompleteObservableRigidityData Index Time) :
    Nonempty (ObservableRigidRealizedClass Index Time) := by
  exact ⟨data.toObservableRigidRealizedClass⟩

/-- Explicit witness that finite observable rigidity yields observable
rigidity. -/
structure FiniteObservableRigidityObservableRigidData (Index Time : Type)
    extends ObservableRigidRealizedClass Index Time where
  finiteObservableRigidityWitness : Prop

/-- Finite-observable-rigidity classes are observable-rigid. -/
theorem finite_observable_rigidity_implies_observable_rigid
    {Index Time : Type}
    (data : FiniteObservableRigidityObservableRigidData Index Time) :
    Nonempty (ObservableRigidRealizedClass Index Time) := by
  exact ⟨data.toObservableRigidRealizedClass⟩

/-- Explicit witness that observable-orbit generation yields observable
rigidity. -/
structure ObservableOrbitGeneratedObservableRigidData (Index Time : Type)
    extends ObservableRigidRealizedClass Index Time where
  observableOrbitGeneratedWitness : Prop

/-- Observable-orbit generated classes are observable-rigid. -/
theorem observable_orbit_generated_implies_observable_rigid
    {Index Time : Type}
    (data : ObservableOrbitGeneratedObservableRigidData Index Time) :
    Nonempty (ObservableRigidRealizedClass Index Time) := by
  exact ⟨data.toObservableRigidRealizedClass⟩

/-- Explicit witness that adjoint-closed real type yields observable rigidity. -/
structure AdjointClosedRealTypeObservableRigidData (Index Time : Type)
    extends ObservableRigidRealizedClass Index Time where
  adjointClosedRealTypeWitness : Prop

/-- Adjoint-closed real-type classes are observable-rigid. -/
theorem adjoint_closed_real_type_implies_observable_rigid
    {Index Time : Type}
    (data : AdjointClosedRealTypeObservableRigidData Index Time) :
    Nonempty (ObservableRigidRealizedClass Index Time) := by
  exact ⟨data.toObservableRigidRealizedClass⟩

/-- Explicit witness that scalar-commutant complex-type data yield observable
rigidity. -/
structure ScalarCommutantComplexTypeObservableRigidData (Index Time : Type)
    extends ObservableRigidRealizedClass Index Time where
  scalarCommutantComplexTypeWitness : Prop
  observableIrreducibleWitness : Prop
  singletonReducedSelectionWitness : Prop

/-- Scalar-commutant complex-type classes are observable-rigid. -/
theorem scalar_commutant_complex_type_implies_observable_rigid
    {Index Time : Type}
    (data : ScalarCommutantComplexTypeObservableRigidData Index Time) :
    Nonempty (ObservableRigidRealizedClass Index Time) := by
  exact ⟨data.toObservableRigidRealizedClass⟩

/-- Explicit witness that generated observable data yield observable rigidity. -/
structure GeneratedObservableObservableRigidData (Index Time : Type)
    extends ObservableRigidRealizedClass Index Time where
  phaseGeneratedWitness : Prop
  observableIrreducibleWitness : Prop

/-- Phase-generated observable-irreducible classes are observable-rigid. -/
theorem generated_observable_implies_rigid
    {Index Time : Type}
    (data : GeneratedObservableObservableRigidData Index Time) :
    Nonempty (ObservableRigidRealizedClass Index Time) := by
  exact ⟨data.toObservableRigidRealizedClass⟩

end CoherenceCalculus
