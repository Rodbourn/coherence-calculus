import CoherenceCalculus.Foundation.ComplexCompatibilityInterfaceCore

/-!
# Foundation.ComplexCompatibilityCorollaryCore

Structural Chapter 5 theorem/corollary/remark wrappers for the complex
compatibility section.

Each declaration exposes the manuscript-facing conclusion as a proposition while
keeping all analytic, representation-theoretic, and gauge data explicit in the
input package.
-/

namespace CoherenceCalculus

/-- Interpretation remark for spurious harmonics. -/
structure SpuriousHarmonicsInterpretationData where
  spuriousHarmonicsAppear : Prop
  projectionDefectManifestation : Prop
  spuriousHarmonicsAppear_valid : spuriousHarmonicsAppear
  projectionDefectManifestation_valid : projectionDefectManifestation

theorem spurious_harmonics_interpretation
    (data : SpuriousHarmonicsInterpretationData) :
    data.spuriousHarmonicsAppear ∧ data.projectionDefectManifestation := by
  exact ⟨data.spuriousHarmonicsAppear_valid,
    data.projectionDefectManifestation_valid⟩

/-- Explicit phase-compatible Schur-tower data. -/
structure PhaseCompatibleSchurTowerData (A : AddMap) (P : Projection) where
  phaseCarrier : PhaseCarrier A P
  inducedPhaseUnitarySquaresNegIdentity : Prop
  schurCorrectionCompatibility : Prop
  effectiveOperatorCompatibility : Prop
  towerPhaseCompatibility : Prop
  inducedPhaseUnitarySquaresNegIdentity_valid :
    inducedPhaseUnitarySquaresNegIdentity
  schurCorrectionCompatibility_valid : schurCorrectionCompatibility
  effectiveOperatorCompatibility_valid : effectiveOperatorCompatibility
  towerPhaseCompatibility_valid : towerPhaseCompatibility

theorem phase_compatible_schur_tower
    {A : AddMap} {P : Projection}
    (data : PhaseCompatibleSchurTowerData A P) :
    data.inducedPhaseUnitarySquaresNegIdentity ∧
      data.schurCorrectionCompatibility ∧
      data.effectiveOperatorCompatibility ∧
      data.towerPhaseCompatibility := by
  exact ⟨data.inducedPhaseUnitarySquaresNegIdentity_valid,
    data.schurCorrectionCompatibility_valid,
    data.effectiveOperatorCompatibility_valid,
    data.towerPhaseCompatibility_valid⟩

/-- Explicit sign-rigidity data for multiplicity-free complex-type phase
carriers. -/
structure PhaseCarrierSignRigidityData (Group Channel : Type) where
  package : ComplexTypeSymmetryPackage Group Channel
  signRigidPhaseRestriction : Prop
  phaseEquivalentModuloChannelSigns : Prop
  signRigidPhaseRestriction_valid : signRigidPhaseRestriction
  phaseEquivalentModuloChannelSigns_valid : phaseEquivalentModuloChannelSigns

theorem phase_carrier_sign_rigidity
    {Group Channel : Type}
    (data : PhaseCarrierSignRigidityData Group Channel) :
    data.signRigidPhaseRestriction ∧
      data.phaseEquivalentModuloChannelSigns := by
  exact ⟨data.signRigidPhaseRestriction_valid,
    data.phaseEquivalentModuloChannelSigns_valid⟩

/-- Explicit forcing data for the phase-carrier class on a multiplicity-free
complex-type sector. -/
structure ForcedPhaseCarrierClassData (Group Channel : Type) where
  package : ComplexTypeSymmetryPackage Group Channel
  forcedPhaseCarrierClass : Prop
  forcedPhaseCarrierClass_valid : forcedPhaseCarrierClass

theorem forced_phase_carrier_class
    {Group Channel : Type}
    (data : ForcedPhaseCarrierClassData Group Channel) :
    data.forcedPhaseCarrierClass := by
  exact data.forcedPhaseCarrierClass_valid

/-- Explicit normal-form data for phase carriers on complex-type sectors with
multiplicity. -/
structure PhaseCarrierNormalFormMultiplicityData (Group Channel : Type) where
  package : ComplexTypeMultiplicityPackage Group Channel
  channelwiseNormalForm : Prop
  normalFormRelations : Prop
  channelwiseNormalForm_valid : channelwiseNormalForm
  normalFormRelations_valid : normalFormRelations

theorem phase_carrier_normal_form_multiplicity
    {Group Channel : Type}
    (data : PhaseCarrierNormalFormMultiplicityData Group Channel) :
    data.channelwiseNormalForm ∧ data.normalFormRelations := by
  exact ⟨data.channelwiseNormalForm_valid, data.normalFormRelations_valid⟩

/-- Explicit scalar-commutant phase-collapse data. -/
structure ScalarCommutantPhaseCollapseData (Channel : Type) where
  scalarCommutant : ScalarMultiplicityCommutant Channel
  forcedPhaseCarrierClass : Prop
  forcedPhaseCarrierClass_valid : forcedPhaseCarrierClass

theorem scalar_commutant_collapses_phase_gauge
    {Channel : Type}
    (data : ScalarCommutantPhaseCollapseData Channel) :
    data.forcedPhaseCarrierClass := by
  exact data.forcedPhaseCarrierClass_valid

/-- Explicit remark data locating the residual phase obstruction in the
multiplicity commutant. -/
structure PhaseObstructionMultiplicityCommutantData where
  residualFreedomLivesInMultiplicityCommutant : Prop
  uniquenessFailsWithoutScalarCommutant : Prop
  residualFreedomLivesInMultiplicityCommutant_valid :
    residualFreedomLivesInMultiplicityCommutant
  uniquenessFailsWithoutScalarCommutant_valid :
    uniquenessFailsWithoutScalarCommutant

theorem phase_obstruction_multiplicity_commutant
    (data : PhaseObstructionMultiplicityCommutantData) :
    data.residualFreedomLivesInMultiplicityCommutant ∧
      data.uniquenessFailsWithoutScalarCommutant := by
  exact ⟨data.residualFreedomLivesInMultiplicityCommutant_valid,
    data.uniquenessFailsWithoutScalarCommutant_valid⟩

/-- Explicit commutant-trichotomy data for observable-irreducible families. -/
structure IrreducibleCommutantTrichotomyData (Space Operator : Type) where
  observableIrreducibility : ObservableIrreducibility Space Operator
  commutantIsDivisionAlgebra : Prop
  commutantIsRorCorH : Prop
  commutantIsDivisionAlgebra_valid : commutantIsDivisionAlgebra
  commutantIsRorCorH_valid : commutantIsRorCorH

theorem irreducible_commutant_trichotomy
    {Space Operator : Type}
    (data : IrreducibleCommutantTrichotomyData Space Operator) :
    data.commutantIsDivisionAlgebra ∧ data.commutantIsRorCorH := by
  exact ⟨data.commutantIsDivisionAlgebra_valid, data.commutantIsRorCorH_valid⟩

/-- Explicit self-adjoint scalarization data for irreducible commutants. -/
structure SelfAdjointCommutantScalarizationData (Space Operator : Type) where
  observableIrreducibility : ObservableIrreducibility Space Operator
  selfAdjointCommutantScalarization : Prop
  selfAdjointCommutantScalarization_valid : selfAdjointCommutantScalarization

theorem self_adjoint_commutant_scalarization
    {Space Operator : Type}
    (data : SelfAdjointCommutantScalarizationData Space Operator) :
    data.selfAdjointCommutantScalarization := by
  exact data.selfAdjointCommutantScalarization_valid

/-- Explicit real-type phase-collapse data. -/
structure RealTypePhaseCollapseData (Space Operator : Type) where
  realTypeChannel : RealTypeObservableChannel Space Operator
  forcedPhaseCarrierClass : Prop
  forcedPhaseCarrierClass_valid : forcedPhaseCarrierClass

theorem real_type_irreducibility_collapses_phase_gauge
    {Space Operator : Type}
    (data : RealTypePhaseCollapseData Space Operator) :
    data.forcedPhaseCarrierClass := by
  exact data.forcedPhaseCarrierClass_valid

/-- Explicit remark data separating irreducibility from phase rigidity. -/
structure IrreducibilityVersusPhaseData where
  irreducibilityDoesNotForceUniquePhaseClass : Prop
  selfAdjointPartStillScalarizes : Prop
  residualPhaseGaugeMayPersist : Prop
  irreducibilityDoesNotForceUniquePhaseClass_valid :
    irreducibilityDoesNotForceUniquePhaseClass
  selfAdjointPartStillScalarizes_valid : selfAdjointPartStillScalarizes
  residualPhaseGaugeMayPersist_valid : residualPhaseGaugeMayPersist

theorem irreducibility_versus_phase
    (data : IrreducibilityVersusPhaseData) :
    data.irreducibilityDoesNotForceUniquePhaseClass ∧
      data.selfAdjointPartStillScalarizes ∧
      data.residualPhaseGaugeMayPersist := by
  exact ⟨data.irreducibilityDoesNotForceUniquePhaseClass_valid,
    data.selfAdjointPartStillScalarizes_valid,
    data.residualPhaseGaugeMayPersist_valid⟩

/-- Explicit scalar-commutant data from observable completeness. -/
structure ObservableCompletenessScalarCommutantData (Space Operator : Type) where
  observableCompleteness : ObservableCompleteness Space Operator
  commutantIsScalar : Prop
  commutantIsScalar_valid : commutantIsScalar

theorem observable_completeness_scalar_commutant
    {Space Operator : Type}
    (data : ObservableCompletenessScalarCommutantData Space Operator) :
    data.commutantIsScalar := by
  exact data.commutantIsScalar_valid

/-- Explicit irreducibility data from observable completeness. -/
structure ObservableCompletenessIrreducibleData (Space Operator : Type) where
  observableCompleteness : ObservableCompleteness Space Operator
  observableIrreducible : Prop
  observableIrreducible_valid : observableIrreducible

theorem observable_completeness_irreducible
    {Space Operator : Type}
    (data : ObservableCompletenessIrreducibleData Space Operator) :
    data.observableIrreducible := by
  exact data.observableIrreducible_valid

/-- Explicit real-type witness from observable completeness. -/
structure ObservableCompletenessRealTypeData (Space Operator : Type)
    extends RealTypeObservableChannel Space Operator where
  observableCompletenessWitness : Prop

theorem observable_completeness_real_type
    {Space Operator : Type}
    (data : ObservableCompletenessRealTypeData Space Operator) :
    Nonempty (RealTypeObservableChannel Space Operator) := by
  exact ⟨data.toRealTypeObservableChannel⟩

/-- Explicit phase-collapse data from observable completeness. -/
structure ObservableCompletenessPhaseCollapseData (Space Operator : Type) where
  observableCompleteness : ObservableCompleteness Space Operator
  forcedPhaseCarrierClass : Prop
  forcedPhaseCarrierClass_valid : forcedPhaseCarrierClass

theorem observable_completeness_collapses_phase_gauge
    {Space Operator : Type}
    (data : ObservableCompletenessPhaseCollapseData Space Operator) :
    data.forcedPhaseCarrierClass := by
  exact data.forcedPhaseCarrierClass_valid

/-- Explicit completeness data from adjoint-closed real type. -/
structure AdjointClosedRealTypeCompleteData (Space Operator : Type) where
  adjointClosedRealType : AdjointClosedGeneratedObservableAlgebra Space Operator
  observableIrreducibleWitness : Prop
  realTypeWitness : Prop
  observableComplete : Prop
  observableComplete_valid : observableComplete

theorem adjoint_closed_real_type_complete
    {Space Operator : Type}
    (data : AdjointClosedRealTypeCompleteData Space Operator) :
    data.observableComplete := by
  exact data.observableComplete_valid

/-- Explicit matrix-unit witness from adjoint-closed real type. -/
structure AdjointClosedRealTypeMatrixUnitsData (Basis Operator : Type)
    extends MatrixUnitObservableScaffold Basis Operator where
  adjointClosedRealTypeWitness : Prop

theorem adjoint_closed_real_type_matrix_units
    {Basis Operator : Type}
    (data : AdjointClosedRealTypeMatrixUnitsData Basis Operator) :
    Nonempty (MatrixUnitObservableScaffold Basis Operator) := by
  exact ⟨data.toMatrixUnitObservableScaffold⟩

/-- Explicit phase-collapse data from adjoint-closed real type. -/
structure AdjointClosedRealTypePhaseData (Space Operator : Type) where
  adjointClosedRealType : AdjointClosedGeneratedObservableAlgebra Space Operator
  forcedPhaseCarrierClass : Prop
  forcedPhaseCarrierClass_valid : forcedPhaseCarrierClass

theorem adjoint_closed_real_type_phase
    {Space Operator : Type}
    (data : AdjointClosedRealTypePhaseData Space Operator) :
    data.forcedPhaseCarrierClass := by
  exact data.forcedPhaseCarrierClass_valid

/-- Explicit rank-one-seed witness from simple spectrum. -/
structure SimpleSpectrumRankOneSeedData (Space Scalar Operator : Type)
    extends RankOneObservableSeed Space Operator where
  simpleSpectrum : SimpleSpectrumObservable Space Scalar Operator

theorem simple_spectrum_gives_rank_one_seed
    {Space Scalar Operator : Type}
    (data : SimpleSpectrumRankOneSeedData Space Scalar Operator) :
    Nonempty (RankOneObservableSeed Space Operator) := by
  exact ⟨data.toRankOneObservableSeed⟩

/-- Explicit completeness data from simple spectrum. -/
structure SimpleSpectrumCompleteData (Space Operator : Type) where
  simpleSpectrumWitness : Prop
  observableComplete : Prop
  observableComplete_valid : observableComplete

theorem simple_spectrum_complete
    {Space Operator : Type}
    (data : SimpleSpectrumCompleteData Space Operator) :
    data.observableComplete := by
  exact data.observableComplete_valid

/-- Explicit phase-collapse data from simple spectrum. -/
structure SimpleSpectrumPhaseData (Space Operator : Type) where
  simpleSpectrumWitness : Prop
  forcedPhaseCarrierClass : Prop
  forcedPhaseCarrierClass_valid : forcedPhaseCarrierClass

theorem simple_spectrum_phase
    {Space Operator : Type}
    (data : SimpleSpectrumPhaseData Space Operator) :
    data.forcedPhaseCarrierClass := by
  exact data.forcedPhaseCarrierClass_valid

/-- Explicit completeness data from a rank-one observable seed. -/
structure RankOneSeedCompleteData (Space Operator : Type) where
  rankOneSeed : RankOneObservableSeed Space Operator
  observableIrreducibleWitness : Prop
  adjointClosedGeneratedWitness : Prop
  observableComplete : Prop
  observableComplete_valid : observableComplete

theorem rank_one_seed_forces_completeness
    {Space Operator : Type}
    (data : RankOneSeedCompleteData Space Operator) :
    data.observableComplete := by
  exact data.observableComplete_valid

/-- Explicit scalar-commutant data from a rank-one seed. -/
structure RankOneSeedScalarCommutantData (Space Operator : Type) where
  rankOneSeed : RankOneObservableSeed Space Operator
  commutantIsScalar : Prop
  commutantIsScalar_valid : commutantIsScalar

theorem rank_one_seed_scalar_commutant
    {Space Operator : Type}
    (data : RankOneSeedScalarCommutantData Space Operator) :
    data.commutantIsScalar := by
  exact data.commutantIsScalar_valid

/-- Explicit phase-collapse data from a rank-one seed. -/
structure RankOneSeedPhaseData (Space Operator : Type) where
  rankOneSeed : RankOneObservableSeed Space Operator
  forcedPhaseCarrierClass : Prop
  forcedPhaseCarrierClass_valid : forcedPhaseCarrierClass

theorem rank_one_seed_phase
    {Space Operator : Type}
    (data : RankOneSeedPhaseData Space Operator) :
    data.forcedPhaseCarrierClass := by
  exact data.forcedPhaseCarrierClass_valid

/-- Explicit invariant-subspace dichotomy data for a rank-one projector. -/
structure RankOneProjectionInvariantSubspaceData where
  invariantSubspaceDichotomy : Prop
  invariantSubspaceDichotomy_valid : invariantSubspaceDichotomy

theorem rank_one_projection_invariant_subspace
    (data : RankOneProjectionInvariantSubspaceData) :
    data.invariantSubspaceDichotomy := by
  exact data.invariantSubspaceDichotomy_valid

/-- Explicit observable-irreducibility witness from a connected rank-one orbit. -/
structure ConnectedRankOneOrbitIrreducibleData (Group Space Line : Type)
    extends ObservableIrreducibility Space (Line → Line) where
  orbitLineFamily : ObservableOrbitLineFamily Group Space Line

theorem connected_rank_one_orbit_irreducible
    {Group Space Line : Type}
    (data : ConnectedRankOneOrbitIrreducibleData Group Space Line) :
    Nonempty (ObservableIrreducibility Space (Line → Line)) := by
  exact ⟨data.toObservableIrreducibility⟩

/-- Explicit completeness witness from a sphere-transitive orbit family. -/
structure SphereTransitiveOrbitObservableCompletenessData
    (Group Space Line Operator : Type) where
  orbitLineFamily : ObservableOrbitLineFamily Group Space Line
  observableComplete : Prop
  observableComplete_valid : observableComplete

theorem sphere_transitive_orbit_observable_completeness
    {Group Space Line Operator : Type}
    (data : SphereTransitiveOrbitObservableCompletenessData
      Group Space Line Operator) :
    data.observableComplete := by
  exact data.observableComplete_valid

/-- Explicit completeness witness from a matrix-unit scaffold. -/
structure MatrixUnitScaffoldCompleteData (Basis Operator : Type) where
  scaffold : MatrixUnitObservableScaffold Basis Operator
  observableComplete : Prop
  observableComplete_valid : observableComplete

theorem matrix_unit_scaffold_complete
    {Basis Operator : Type}
    (data : MatrixUnitScaffoldCompleteData Basis Operator) :
    data.observableComplete := by
  exact data.observableComplete_valid

/-- Explicit phase-collapse data from a matrix-unit scaffold. -/
structure MatrixUnitScaffoldPhaseData (Basis Operator : Type) where
  scaffold : MatrixUnitObservableScaffold Basis Operator
  forcedPhaseCarrierClass : Prop
  forcedPhaseCarrierClass_valid : forcedPhaseCarrierClass

theorem matrix_unit_scaffold_phase
    {Basis Operator : Type}
    (data : MatrixUnitScaffoldPhaseData Basis Operator) :
    data.forcedPhaseCarrierClass := by
  exact data.forcedPhaseCarrierClass_valid

/-- Explicit finite observable rigidity package. -/
structure FiniteObservableRigidityData where
  observableComplete : Prop
  rankOneObservableSeed : Prop
  simpleSpectrumObservable : Prop
  matrixUnitObservableScaffold : Prop
  observableComplete_valid : observableComplete
  rankOneObservableSeed_valid : rankOneObservableSeed
  simpleSpectrumObservable_valid : simpleSpectrumObservable
  matrixUnitObservableScaffold_valid : matrixUnitObservableScaffold

theorem finite_observable_rigidity
    (data : FiniteObservableRigidityData) :
    data.observableComplete ∧
      data.rankOneObservableSeed ∧
      data.simpleSpectrumObservable ∧
      data.matrixUnitObservableScaffold := by
  exact ⟨data.observableComplete_valid, data.rankOneObservableSeed_valid,
    data.simpleSpectrumObservable_valid,
    data.matrixUnitObservableScaffold_valid⟩

/-- Explicit phase-collapse data from finite observable rigidity. -/
structure FiniteObservableRigidityPhaseData where
  finiteObservableRigidity : FiniteObservableRigidityData
  forcedPhaseCarrierClass : Prop
  forcedPhaseCarrierClass_valid : forcedPhaseCarrierClass

theorem finite_observable_rigidity_phase
    (data : FiniteObservableRigidityPhaseData) :
    data.forcedPhaseCarrierClass := by
  exact data.forcedPhaseCarrierClass_valid

/-- Explicit real-type witness from finite observable rigidity. -/
structure FiniteObservableRigidityRealTypeData (Space Operator : Type)
    extends RealTypeObservableChannel Space Operator where
  finiteObservableRigidityWitness : Prop

theorem finite_observable_rigidity_real_type
    {Space Operator : Type}
    (data : FiniteObservableRigidityRealTypeData Space Operator) :
    Nonempty (RealTypeObservableChannel Space Operator) := by
  exact ⟨data.toRealTypeObservableChannel⟩

/-- Explicit phase-collapse data from phase rigidity. -/
structure PhaseRigidityCollapseData (Space Operator : Type) where
  phaseRigidFamily : PhaseRigidObservableFamily Space Operator
  forcedPhaseCarrierClass : Prop
  forcedPhaseCarrierClass_valid : forcedPhaseCarrierClass

theorem phase_rigidity_collapses_phase_gauge
    {Space Operator : Type}
    (data : PhaseRigidityCollapseData Space Operator) :
    data.forcedPhaseCarrierClass := by
  exact data.forcedPhaseCarrierClass_valid

/-- Explicit phase-class witness from phase generation. -/
structure PhaseGenerationPhaseClassData (Space Operator : Type) where
  phaseGeneratingFamily : PhaseGeneratingObservableFamily Space Operator
  forcedPhaseCarrierClass : Prop
  forcedPhaseCarrierClass_valid : forcedPhaseCarrierClass

theorem phase_generation_forces_phase_class
    {Space Operator : Type}
    (data : PhaseGenerationPhaseClassData Space Operator) :
    data.forcedPhaseCarrierClass := by
  exact data.forcedPhaseCarrierClass_valid

/-- Explicit phase-rigidity witness from phase generation. -/
structure PhaseGenerationPhaseRigidityData (Space Operator : Type) where
  phaseGeneratingFamily : PhaseGeneratingObservableFamily Space Operator
  phaseRigidMultiplictyFamily : Prop
  phaseRigidMultiplictyFamily_valid : phaseRigidMultiplictyFamily

theorem phase_generation_forces_phase_rigidity
    {Space Operator : Type}
    (data : PhaseGenerationPhaseRigidityData Space Operator) :
    data.phaseRigidMultiplictyFamily := by
  exact data.phaseRigidMultiplictyFamily_valid

/-- Explicit local unitary covariance data for a channel transport network. -/
structure LocalUnitaryCovarianceData (Graph : ChannelTransportGraph) where
  transportEnergy : ChannelTransportEnergy Graph
  localUnitaryGaugeCovariance : Prop
  localUnitaryGaugeCovariance_valid : localUnitaryGaugeCovariance

theorem local_unitary_covariance
    {Graph : ChannelTransportGraph}
    (data : LocalUnitaryCovarianceData Graph) :
    data.localUnitaryGaugeCovariance := by
  exact data.localUnitaryGaugeCovariance_valid

/-- Explicit unimodular reduction data for a channel transport network. -/
structure UnimodularChannelReductionData (Graph : ChannelTransportGraph) where
  transportEnergy : ChannelTransportEnergy Graph
  unimodularReduction : Prop
  unimodularReduction_valid : unimodularReduction

theorem unimodular_channel_reduction
    {Graph : ChannelTransportGraph}
    (data : UnimodularChannelReductionData Graph) :
    data.unimodularReduction := by
  exact data.unimodularReduction_valid

/-- Explicit remark data for the purely mathematical gauge mechanism. -/
structure MathematicalGaugeMechanismData where
  structuralGaugeCovarianceOnly : Prop
  noPhysicalGaugeFieldIdentified : Prop
  structuralGaugeCovarianceOnly_valid : structuralGaugeCovarianceOnly
  noPhysicalGaugeFieldIdentified_valid : noPhysicalGaugeFieldIdentified

theorem mathematical_gauge_mechanism
    (data : MathematicalGaugeMechanismData) :
    data.structuralGaugeCovarianceOnly ∧
      data.noPhysicalGaugeFieldIdentified := by
  exact ⟨data.structuralGaugeCovarianceOnly_valid,
    data.noPhysicalGaugeFieldIdentified_valid⟩

end CoherenceCalculus
