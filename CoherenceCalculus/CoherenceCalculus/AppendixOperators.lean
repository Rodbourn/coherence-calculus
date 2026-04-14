import CoherenceCalculus.Foundation.TowerCalculusCore

namespace CoherenceCalculus
namespace AppendixOperators

/-!
This detached appendix lane is intentionally interface-heavy.

Where an appendix claim is pure additive horizon algebra, it is rebuilt
directly over the active `HorizonTower` / `AddMap` surface. Where an appendix
claim needs genuinely extra finite-dimensional, trace, polar, spectral, or SVD
data, that dependence is packaged as an explicit local datum here rather than
being smuggled in through archived files.
-/

/-- Appendix horizon restriction on the rebuilt additive operator spine. -/
def horizonRestrict (T : HorizonTower) (h : Nat) (A : AddMap) : AddMap :=
  AddMap.observedMap T h A

/-- Appendix horizon flow on the rebuilt additive operator spine. -/
def horizonFlow (T : HorizonTower) (h : Nat) (A : AddMap) : AddMap :=
  AddMap.sub (horizonRestrict T (h + 1) A) (horizonRestrict T h A)

/-- Horizon flow is additive in the operator input, pointwise on states. -/
theorem horizonFlow_add (T : HorizonTower) (h : Nat) (A B : AddMap) (x : State) :
    horizonFlow T h (AddMap.add A B) x =
      State.add (horizonFlow T h A x) (horizonFlow T h B x) := by
  change
    State.sub
      ((T.π (h + 1)).toFun
        (State.add (A ((T.π (h + 1)).toFun x)) (B ((T.π (h + 1)).toFun x))))
      ((T.π h).toFun (State.add (A ((T.π h).toFun x)) (B ((T.π h).toFun x)))) =
    State.add
      (State.sub
        ((T.π (h + 1)).toFun (A ((T.π (h + 1)).toFun x)))
        ((T.π h).toFun (A ((T.π h).toFun x))))
      (State.sub
        ((T.π (h + 1)).toFun (B ((T.π (h + 1)).toFun x)))
        ((T.π h).toFun (B ((T.π h).toFun x))))
  rw [(T.π (h + 1)).map_add, (T.π h).map_add]
  exact
    State.sub_add_distrib
      ((T.π (h + 1)).toFun (A ((T.π (h + 1)).toFun x)))
      ((T.π (h + 1)).toFun (B ((T.π (h + 1)).toFun x)))
      ((T.π h).toFun (A ((T.π h).toFun x)))
      ((T.π h).toFun (B ((T.π h).toFun x)))

/-- The horizon flow of the identity map is the adjacent increment band, pointwise. -/
theorem horizonFlow_id_eq_increment (T : HorizonTower) (h : Nat) (x : State) :
    horizonFlow T h AddMap.id x = incrementProj T (h + 1) x := by
  change
    State.sub
      ((T.π (h + 1)).toFun ((T.π (h + 1)).toFun x))
      ((T.π h).toFun ((T.π h).toFun x)) =
    State.sub ((T.π (h + 1)).toFun x) ((T.π h).toFun x)
  rw [(T.π (h + 1)).idem x, (T.π h).idem x]

/-- The horizon flow of the horizon projector vanishes at the same level, pointwise. -/
theorem horizonFlow_proj_zero (T : HorizonTower) (h : Nat) (x : State) :
    horizonFlow T h (AddMap.ofProjection (T.π h)) x = State.zero := by
  unfold horizonFlow horizonRestrict AddMap.observedMap AddMap.sub
  change
    State.sub
      ((T.π (h + 1)).toFun ((T.π h).toFun ((T.π (h + 1)).toFun x)))
      ((T.π h).toFun ((T.π h).toFun ((T.π h).toFun x))) =
    State.zero
  rw [nested_proj_comp_ge T (h + 1) h (Nat.le_succ h) ((T.π (h + 1)).toFun x)]
  rw [nested_proj_comp T h (h + 1) (Nat.le_succ h) x]
  rw [(T.π h).idem ((T.π h).toFun x), (T.π h).idem x]
  exact State.sub_self ((T.π h).toFun x)

/-- A local witness for a continuous scale derivative package. -/
structure ContinuousScaleDerivativeDatum (Scale : Type) where
  derivative : Scale → AddMap → AddMap

/-- A detached scale-derivative interface used for the appendix remark. -/
def continuousScaleDerivative {Scale : Type}
    (datum : ContinuousScaleDerivativeDatum Scale) :
    Scale → AddMap → AddMap :=
  datum.derivative

/-- Explicit selector laws for a spectral-selection package. -/
structure SpectralSelectorDatum (Spectrum : Type) where
  selector : Spectrum → AddMap
  meet : Spectrum → Spectrum → Spectrum
  join : Spectrum → Spectrum → Spectrum
  disjoint : Spectrum → Spectrum → Prop
  whole : Spectrum
  empty : Spectrum
  idem : ∀ s, AddMap.comp (selector s) (selector s) = selector s
  meet_law : ∀ s t, AddMap.comp (selector s) (selector t) = selector (meet s t)
  disjoint_join :
    ∀ s t, disjoint s t → selector (join s t) = AddMap.add (selector s) (selector t)
  whole_law : selector whole = AddMap.id
  empty_law : selector empty = AddMap.zero

/-- The appendix spectral selector under explicit local selector data. -/
def spectralSelector {Spectrum : Type}
    (datum : SpectralSelectorDatum Spectrum) :
    Spectrum → AddMap :=
  datum.selector

/-- Idempotence of the explicit spectral selector package. -/
theorem spectralSelector_idem {Spectrum : Type}
    (datum : SpectralSelectorDatum Spectrum) (s : Spectrum) :
    AddMap.comp (spectralSelector datum s) (spectralSelector datum s) =
      spectralSelector datum s :=
  datum.idem s

/-- Composition law for the explicit spectral selector package. -/
theorem spectralSelector_meet {Spectrum : Type}
    (datum : SpectralSelectorDatum Spectrum) (s t : Spectrum) :
    AddMap.comp (spectralSelector datum s) (spectralSelector datum t) =
      spectralSelector datum (datum.meet s t) :=
  datum.meet_law s t

/-- Disjoint-union law for the explicit spectral selector package. -/
theorem spectralSelector_disjoint_join {Spectrum : Type}
    (datum : SpectralSelectorDatum Spectrum) (s t : Spectrum)
    (hdis : datum.disjoint s t) :
    spectralSelector datum (datum.join s t) =
      AddMap.add (spectralSelector datum s) (spectralSelector datum t) :=
  datum.disjoint_join s t hdis

/-- Whole-spectrum law for the explicit spectral selector package. -/
theorem spectralSelector_whole {Spectrum : Type}
    (datum : SpectralSelectorDatum Spectrum) :
    spectralSelector datum datum.whole = AddMap.id :=
  datum.whole_law

/-- Empty-spectrum law for the explicit spectral selector package. -/
theorem spectralSelector_empty {Spectrum : Type}
    (datum : SpectralSelectorDatum Spectrum) :
    spectralSelector datum datum.empty = AddMap.zero :=
  datum.empty_law

/-- A concrete finite-dimensional spectral-selection example package. -/
structure finite_quantization_example where
  selectedSubspaceWitness : Prop
  diagonalFormWitness : Prop

/-- A documentary selection-rule carrier for the appendix remark. -/
structure selectionRule where
  admissibleSpectrum : Type
  admissibilityWitness : admissibleSpectrum → Prop

/-- Explicit trace package for horizon traces. -/
structure HorizonTraceDatum where
  trace : Nat → AddMap → Nat
  add_law : ∀ h A B, trace h (AddMap.add A B) = trace h A + trace h B
  monotone_law : ∀ h h', h ≤ h' → ∀ A, trace h A ≤ trace h' A
  consistency_law :
    ∀ (T : HorizonTower) (h : Nat), trace h (AddMap.ofProjection (T.π h)) = trace h AddMap.id

/-- Appendix horizon trace under explicit local trace data. -/
def horizonTrace (datum : HorizonTraceDatum) (h : Nat) (A : AddMap) : Nat :=
  datum.trace h A

/-- Additivity of the appendix horizon trace. -/
theorem horizonTrace_add (datum : HorizonTraceDatum) (h : Nat) (A B : AddMap) :
    horizonTrace datum h (AddMap.add A B) =
      horizonTrace datum h A + horizonTrace datum h B :=
  datum.add_law h A B

/-- Monotonicity of the appendix horizon trace. -/
theorem horizonTrace_monotone_statement
    (datum : HorizonTraceDatum) (h h' : Nat) (hle : h ≤ h') (A : AddMap) :
    horizonTrace datum h A ≤ horizonTrace datum h' A :=
  datum.monotone_law h h' hle A

/-- Consistency of the appendix horizon trace on the horizon projector. -/
theorem horizonTrace_consistency
    (datum : HorizonTraceDatum) (T : HorizonTower) (h : Nat) :
    horizonTrace datum h (AddMap.ofProjection (T.π h)) =
      horizonTrace datum h AddMap.id :=
  datum.consistency_law T h

/-- Explicit supertrace package for the appendix graded trace surface. -/
structure CoherenceSupertraceDatum where
  supertrace : AddMap → Nat
  add_law : ∀ A B, supertrace (AddMap.add A B) = supertrace A + supertrace B

/-- Appendix coherence supertrace under explicit local supertrace data. -/
def coherenceSupertrace (datum : CoherenceSupertraceDatum) (A : AddMap) : Nat :=
  datum.supertrace A

/-- Additivity of the appendix coherence supertrace. -/
theorem coherenceSupertrace_add
    (datum : CoherenceSupertraceDatum) (A B : AddMap) :
    coherenceSupertrace datum (AddMap.add A B) =
      coherenceSupertrace datum A + coherenceSupertrace datum B :=
  datum.add_law A B

/-- Explicit polar-decomposition data for the appendix aliasing discussion. -/
structure PolarDecompositionDatum where
  carrier : Type
  leakageMagnitudeSquared : carrier → Nat
  aliasingProjectorDomain : carrier → Prop
  leakageMagnitude_observable : carrier → Nat
  isometry_property : ∀ x, aliasingProjectorDomain x →
    leakageMagnitude_observable x = leakageMagnitudeSquared x
  leakage_norm_eq_abs_norm : ∀ x, leakageMagnitude_observable x = leakageMagnitudeSquared x

/-- Appendix leakage-magnitude carrier. -/
def leakageMagnitudeSquared (datum : PolarDecompositionDatum) : datum.carrier → Nat :=
  datum.leakageMagnitudeSquared

/-- Appendix aliasing-domain carrier. -/
def aliasingProjectorDomain (datum : PolarDecompositionDatum) : datum.carrier → Prop :=
  datum.aliasingProjectorDomain

/-- Appendix observable leakage-magnitude carrier. -/
def leakageMagnitude_observable (datum : PolarDecompositionDatum) : datum.carrier → Nat :=
  datum.leakageMagnitude_observable

/-- Appendix aliasing isometry law. -/
theorem isometry_property
    (datum : PolarDecompositionDatum) (x : datum.carrier)
    (hx : aliasingProjectorDomain datum x) :
    leakageMagnitude_observable datum x = leakageMagnitudeSquared datum x :=
  datum.isometry_property x hx

/-- Appendix aliasing norm law. -/
theorem leakage_norm_eq_abs_norm
    (datum : PolarDecompositionDatum) (x : datum.carrier) :
    leakageMagnitude_observable datum x = leakageMagnitudeSquared datum x :=
  datum.leakage_norm_eq_abs_norm x

/-- Documentary remark package for the defect-energy / aliasing-direction note. -/
structure defect_energy_aliasing_direction where
  statement : Prop

/-- A finite group action used in the appendix symmetry package. -/
structure GroupAction (Group Carrier : Type) where
  act : Group → Carrier → Carrier

/-- An appendix isotypic-projector package with explicit orthogonality data. -/
structure AppendixIsotypicProjector (Group Carrier : Type) where
  projector : Carrier → Carrier
  orthogonal_idempotent : Prop

/-- Appendix projector-law package for the symmetry section. -/
structure IsotypicProperties (Group Carrier : Type) where
  projectorFamily : Group → Carrier → Carrier
  pairwiseOrthogonal : Prop
  complete : Prop

/-- Appendix invariant-dimension package. -/
structure invariantDimension where
  value : Nat
  traceFormula : Prop

/-- The `S_2` appendix example package. -/
structure s2_projectors_example where
  trivialBlockWitness : Prop
  signBlockWitness : Prop

/-- Appendix density package for a horizon. -/
structure horizonDensity where
  rank : Nat
  normalized : Prop

/-- Appendix entropy package for a horizon. -/
structure horizonEntropy where
  value : Nat

/-- The entropy of a projection is carried explicitly on the appendix entropy surface. -/
structure projection_entropy where
  rank : Nat
  entropyValue : Nat
  exact_log_rank : Prop

/-- Documentary refinement note for the appendix entropy discussion. -/
structure entropy_horizon_refinement where
  monotoneCapacity : Prop

/-- Appendix defect-corrected entropy package. -/
structure defectCorrectedEntropy where
  value : Nat
  penaltyWitness : Prop

/-- Appendix cohomology-dimension package. -/
structure topologicalSpectrograph where
  grades : Nat → Nat

/-- Appendix weighted graded-volume package. -/
structure gradedVolume where
  value : Nat
  weightWitness : Prop

/-- Additivity package for the appendix topological spectrograph. -/
structure spectrograph_additivity where
  spectrographAdditive : Prop
  volumeAdditive : Prop

/-- Documentary exactness note for the appendix topological spectrograph. -/
structure exact_complex_spectrograph_zero where
  statement : Prop

/-- Appendix iteration-map surface. -/
structure IterationMap (StateSpace : Type) where
  map : StateSpace → StateSpace

/-- Fixed-point predicate on the appendix iteration-map surface. -/
def isFixedPoint {StateSpace : Type}
    (F : IterationMap StateSpace) (x : StateSpace) : Prop :=
  F.map x = x

/-- Appendix linearization surface. -/
structure Linearization (StateSpace : Type) where
  jacobian : StateSpace → StateSpace

/-- Appendix stability-index package. -/
structure stabilityIndex where
  unstableDirections : Nat

/-- Appendix stable-type package. -/
structure isStableFixedPoint where
  witness : Prop

/-- Appendix unstable-type package. -/
structure isUnstableFixedPoint where
  witness : Prop

/-- Explicit linear stability criterion package. -/
structure stability_criterion where
  attractingWitness : Prop

/-- Explicit linear instability criterion package. -/
structure instability_criterion where
  repellingWitness : Prop

/-- The one-dimensional linear iteration example package. -/
structure linear_stability_example where
  stableCase : Prop
  unstableCase : Prop

/-- Documentary alternative-index note for the appendix stability discussion. -/
structure alternative_stability_indices where
  statement : Prop

/-- Explicit principal-angle data for the appendix SVD discussion. -/
structure PrincipalAngleDatum (Subspace Angle Singular Operator : Type) where
  principalAngles : Subspace → Subspace → List Angle
  principalAngleOp : Subspace → Subspace → Operator
  singularValues : Subspace → Subspace → List Singular
  svdSpec : ∀ (U V : Subspace), True
  inclusionCriterion : ∀ (U V : Subspace), Prop
  orthogonalCriterion : ∀ (U V : Subspace), Prop
  equalityCriterion : ∀ (U V : Subspace), Prop

/-- Appendix principal-angle carrier. -/
def principalAngles {Subspace Angle Singular Operator : Type}
    (datum : PrincipalAngleDatum Subspace Angle Singular Operator) :
    Subspace → Subspace → List Angle :=
  datum.principalAngles

/-- Appendix principal-angle-operator carrier. -/
def principalAngleOp {Subspace Angle Singular Operator : Type}
    (datum : PrincipalAngleDatum Subspace Angle Singular Operator) :
    Subspace → Subspace → Operator :=
  datum.principalAngleOp

/-- Appendix SVD-principal-angle theorem surface. -/
theorem svd_principal_angles
    {Subspace Angle Singular Operator : Type}
    (datum : PrincipalAngleDatum Subspace Angle Singular Operator)
    (U V : Subspace) :
    True :=
  datum.svdSpec U V

/-- Appendix frustration-tensor carrier. -/
def frustrationTensor {Subspace Angle Singular Operator : Type}
    (datum : PrincipalAngleDatum Subspace Angle Singular Operator)
    (U V : Subspace) : List Singular :=
  datum.singularValues U V

/-- Appendix inclusion criterion for principal-angle data. -/
def subspace_inclusion_iff_angles_zero
    {Subspace Angle Singular Operator : Type}
    (datum : PrincipalAngleDatum Subspace Angle Singular Operator)
    (U V : Subspace) : Prop :=
  datum.inclusionCriterion U V

/-- Appendix orthogonality criterion for principal-angle data. -/
def subspace_orthogonal_iff_angles_max
    {Subspace Angle Singular Operator : Type}
    (datum : PrincipalAngleDatum Subspace Angle Singular Operator)
    (U V : Subspace) : Prop :=
  datum.orthogonalCriterion U V

/-- Appendix equality criterion for principal-angle data. -/
def subspace_equality_iff_all_ones
    {Subspace Angle Singular Operator : Type}
    (datum : PrincipalAngleDatum Subspace Angle Singular Operator)
    (U V : Subspace) : Prop :=
  datum.equalityCriterion U V

/-- The two-lines-in-`R^2` appendix example package. -/
structure lines_r2_example where
  principalAngleWitness : Prop

/-- Appendix observable-algebra carrier. -/
structure ObservableAlgebra (Carrier : Type) where
  mem : Carrier → Prop

/-- Appendix invariant-subalgebra package. -/
structure invariantSubalgebra (Group Carrier : Type) where
  mem : Carrier → Prop

/-- Appendix invariant-filter package. -/
structure InvariantFilterDatum (Group Carrier : Type) where
  filter : Carrier → Carrier
  linear : Prop
  idempotent : Prop
  rangeWitness : Prop
  fixedPoints : Prop
  starPreserving : Prop

/-- Appendix invariant filter. -/
def invariantFilter {Group Carrier : Type}
    (datum : InvariantFilterDatum Group Carrier) : Carrier → Carrier :=
  datum.filter

/-- Documentary linearity witness for the appendix invariant filter. -/
def invariantFilter_linear {Group Carrier : Type}
    (datum : InvariantFilterDatum Group Carrier) : Prop :=
  datum.linear

/-- Idempotence witness for the appendix invariant filter. -/
def invariantFilter_idempotent {Group Carrier : Type}
    (datum : InvariantFilterDatum Group Carrier) : Prop :=
  datum.idempotent

/-- Range witness for the appendix invariant filter. -/
def invariantFilter_range {Group Carrier : Type}
    (datum : InvariantFilterDatum Group Carrier) : Prop :=
  datum.rangeWitness

/-- Fixed-point witness for the appendix invariant filter. -/
def invariantFilter_fixed_points {Group Carrier : Type}
    (datum : InvariantFilterDatum Group Carrier) : Prop :=
  datum.fixedPoints

/-- `*`-preservation witness for the appendix invariant filter. -/
def invariantFilter_preserves_star {Group Carrier : Type}
    (datum : InvariantFilterDatum Group Carrier) : Prop :=
  datum.starPreserving

/-- The appendix conjugation-filter example package. -/
structure conjugation_filter_example where
  realPartWitness : Prop

/-- The appendix diagonal-filter example package. -/
structure diagonal_filter_example where
  invariantBlockWitness : Prop

/-- Observable/shadow decomposition on the rebuilt state space. -/
def obsShadowDecomp (T : HorizonTower) (h : Nat) (x : State) : State × State :=
  ((T.π h).toFun x, shadowProj T h x)

/-- Appendix Pythagorean splitting is recorded as explicit local energy data. -/
structure PythagoreanSplittingDatum where
  energy : State → Nat
  split : ∀ T h x,
    energy x = energy (obsShadowDecomp T h x).1 + energy (obsShadowDecomp T h x).2

/-- Appendix Pythagorean splitting law. -/
theorem pythagorean_splitting
    (datum : PythagoreanSplittingDatum) (T : HorizonTower) (h : Nat) (x : State) :
    datum.energy x =
      datum.energy (obsShadowDecomp T h x).1 + datum.energy (obsShadowDecomp T h x).2 :=
  datum.split T h x

/-- Documentary defect-energy carrier for the unity section. -/
structure defectEnergy_eq_leakage_norm where
  statement : Prop

/-- Documentary defect-energy decomposition carrier for the unity section. -/
structure defect_energy_decomposition where
  statement : Prop

/-- Documentary norm-bound carrier for the unity section. -/
structure norm_bound_observed_statement where
  statement : Prop

/-- Documentary norm-equality criterion carrier for the unity section. -/
structure norm_bound_equality_iff where
  statement : Prop

/-- Documentary polar-decomposition carrier for the unity section. -/
structure PolarDecomp where
  statement : Prop

/-- The three-dimensional norm-accounting appendix example package. -/
structure norm_r3_example where
  decompositionWitness : Prop

/-- Appendix orthogonality-projector surface. -/
structure OrthogonalityProjector (Carrier : Type) where
  project : Carrier → Carrier

/-- Explicit Procrustes-optimality datum for the appendix orthogonality discussion. -/
structure procrustes_optimality_statement where
  witness : Prop

/-- Fixed-point package for the appendix orthogonality projector. -/
structure orthogonality_fixed_point where
  witness : Prop

/-- The `2 × 2` orthogonality-projection appendix example package. -/
structure orthogonality_2x2_example where
  diagonalWitness : Prop
  swapWitness : Prop

/-- Shadow commutator on the rebuilt additive operator spine. -/
def shadowCommutator (T : HorizonTower) (h : Nat) (A : AddMap) : AddMap :=
  AddMap.sub
    (AddMap.comp A (AddMap.ofProjection (T.π h)))
    (AddMap.comp (AddMap.ofProjection (T.π h)) A)

/-- Vanishing commutator data for the appendix shadow-commutator discussion. -/
structure shadowCommutator_vanish_iff where
  witness : Prop

/-- Decomposition data for the appendix shadow commutator. -/
structure shadowCommutator_decomposition_statement where
  witness : Prop

/-- The off-diagonal shadow-commutator appendix example package. -/
structure shadow_commutator_example where
  nonzeroWitness : Prop

/-- The appendix interference-kernel carrier for four operators. -/
structure interferenceKernel4 (Carrier : Type) where
  kernel : Carrier → Carrier

/-- Common fixed-point carrier for the appendix interference-kernel discussion. -/
structure isCommonFixedPoint4 (Carrier : Type) where
  witness : Carrier → Prop

/-- Forward fixed-point inclusion for the appendix interference kernel. -/
structure fixed_implies_kernel_eigenvector4 where
  witness : Prop

/-- Spectral-bound package for the appendix interference kernel. -/
structure kernel_spectral_bound_statement where
  witness : Prop

/-- Eigenspace characterization package for the appendix interference kernel. -/
structure kernel_eigenspace_forward4 where
  witness : Prop

/-- The reflection example package for the appendix interference kernel. -/
structure interference_reflections_example where
  axisFixedWitness : Prop

/-- Appendix constraint-map surface. -/
structure ConstraintMap (Source Target : Type) where
  map : Source → Target

/-- Appendix defect-projector surface. -/
structure defectProjector (Source : Type) where
  project : Source → Source

/-- Appendix defect-projector characterization package. -/
structure defect_projector_characterization where
  witness : Prop

/-- Documentary homeless-modes note for the appendix boundary section. -/
structure boundary_homeless_modes where
  statement : Prop

/-- Documentary infinite-dimensional-extension note for the appendix boundary section. -/
structure boundary_infinite_dimensional_extension where
  statement : Prop

/-- Documentary boundary-defect-functional note for the appendix boundary section. -/
structure boundary_defect_functional where
  statement : Prop

end AppendixOperators
end CoherenceCalculus
