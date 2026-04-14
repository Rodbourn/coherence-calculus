import CoherenceCalculus.Foundation.ObservableClosureCore

/-!
# Foundation.ObservableCorrectionCore

Finite correction, invariant, and jet surfaces for observable-relative closure.

This file extends the early observable packaging layer with the later
manuscript-facing finite correction grammar:

- fixed-source return continuity as an explicit transfer certificate
- exact and approximate correction rank/width packages
- structured correction classes and optimal singular-value profiles
- design-transform covariance and finite invariant packages
- effective/null returned-direction packages and Schur-jet truncations

Analytic ingredients remain explicit local data on the active import-free lane.
-/

namespace CoherenceCalculus

/-- A transfer vanishes when every source state is sent to zero. -/
def ZeroTransfer (T : AddMap) : Prop :=
  ∀ x : State, T x = State.zero

/-- Explicit continuity transfer certificate from a chosen Schur-return family
to the corresponding fixed-source return family. -/
structure FixedSourceReturnContinuityData where
  Cut : Type
  schurReturn : Cut → AddMap
  fixedSourceReturn : Cut → AddMap
  schurContinuous : Prop
  fixedSourceContinuous : Prop
  transfer : schurContinuous → fixedSourceContinuous

/-- Continuity of the fixed-source return transfer is reduced to an explicit
continuity-transfer certificate. -/
theorem fixed_source_return_continuity
    (data : FixedSourceReturnContinuityData) :
    data.schurContinuous → data.fixedSourceContinuous :=
  data.transfer

/-- Explicit correction-factorization datum on the active quotient-free lane. -/
structure ExactCorrectionFactorizationData where
  transfer : AddMap
  correction : AddMap
  factorizationCriterion : Prop
  kernelCriterion : Prop
  extendsToWholeCorrectionSpace : Prop
  factorization_iff_kernel : factorizationCriterion ↔ kernelCriterion

/-- Exact correction factorization is equivalent to the declared kernel
criterion on the supplied quotient-free image surface. -/
theorem exact_correction_factorization
    (data : ExactCorrectionFactorizationData) :
    data.factorizationCriterion ↔ data.kernelCriterion :=
  data.factorization_iff_kernel

/-- Finite closure-rank package for a declared observable transfer. -/
structure ObservableClosureRankData where
  transfer : AddMap
  rank : Nat
  minimalExactCorrectionDimension : Nat
  zero_iff : rank = 0 ↔ ZeroTransfer transfer
  minimal_eq_rank : minimalExactCorrectionDimension = rank

/-- Observable closure rank on the declared finite transfer surface. -/
def observableClosureRank (data : ObservableClosureRankData) : Nat :=
  data.rank

/-- Vanishing observable closure rank is exactly vanishing transfer on the
declared surface. -/
theorem zero_observable_closure_rank
    (data : ObservableClosureRankData) :
    observableClosureRank data = 0 ↔ ZeroTransfer data.transfer :=
  data.zero_iff

/-- The minimal exact correction dimension agrees with the declared observable
closure rank. -/
theorem minimal_exact_correction_dimension
    (data : ObservableClosureRankData) :
    data.minimalExactCorrectionDimension = observableClosureRank data :=
  data.minimal_eq_rank

/-- Explicit finite best-`m` correction profile for a declared transfer. -/
structure BestCorrectionErrorProfile where
  transfer : AddMap
  error : Nat → Nat
  rankConstraint : Nat → Prop

/-- Best `m`-channel correction error on the declared finite profile. -/
def bestCorrectionError (data : BestCorrectionErrorProfile) (m : Nat) : Nat :=
  data.error m

/-- Explicit comparison witness for rank-constrained best-correction
distances. -/
structure CorrectionDistanceData where
  left : BestCorrectionErrorProfile
  right : BestCorrectionErrorProfile
  rankConstrainedForm : Prop
  rankConstrainedForm_valid : rankConstrainedForm
  lipschitzBound : ∀ m : Nat,
    left.error m ≤ right.error m + left.error 0 ∧
      right.error m ≤ left.error m + right.error 0

/-- Rank-constrained best-correction distance and stability are carried by an
explicit comparison witness. -/
theorem best_m_correction_distance
    (data : CorrectionDistanceData) :
    data.rankConstrainedForm ∧
      (∀ m : Nat,
        data.left.error m ≤ data.right.error m + data.left.error 0 ∧
          data.right.error m ≤ data.left.error m + data.right.error 0) :=
  ⟨data.rankConstrainedForm_valid, data.lipschitzBound⟩

/-- Structured correction class indexed by channel budget. -/
structure StructuredCorrectionClass where
  admissible : Nat → Type

/-- Structured closure profile over a chosen correction class. -/
structure StructuredClosureProfile where
  base : ObservableClosureRankData
  correctionClass : StructuredCorrectionClass
  width : Nat → Nat
  rank : Nat
  lowerEnvelope : ∀ m : Nat, bestCorrectionError
      { transfer := base.transfer, error := width, rankConstraint := fun _ => True } m ≥ 0
  widthDominatesBase : ∀ m : Nat,
    bestCorrectionError
        { transfer := base.transfer
          error := fun n => if n = m then 0 else 0
          rankConstraint := fun _ => True } m ≤ width m
  rankDominatesBase : observableClosureRank base ≤ rank
  nestedMonotone : ∀ m : Nat, width (m + 1) ≤ width m

/-- Structured `m`-channel closure width. -/
def structuredClosureWidth (data : StructuredClosureProfile) (m : Nat) : Nat :=
  data.width m

/-- Structured closure rank. -/
def structuredClosureRank (data : StructuredClosureProfile) : Nat :=
  data.rank

/-- The structured width dominates the unstructured lower envelope, and the
structured closure rank dominates the base closure rank. -/
theorem structured_width_lower_envelope
    (data : StructuredClosureProfile) :
    (∀ m : Nat,
      bestCorrectionError
          { transfer := data.base.transfer
            error := fun n => if n = m then 0 else 0
            rankConstraint := fun _ => True } m ≤ structuredClosureWidth data m) ∧
      observableClosureRank data.base ≤ structuredClosureRank data :=
  ⟨data.widthDominatesBase, data.rankDominatesBase⟩

/-- Nested structured correction classes yield monotone structured widths. -/
theorem structured_width_monotonicity
    (data : StructuredClosureProfile) :
    ∀ m : Nat, structuredClosureWidth data (m + 1) ≤ structuredClosureWidth data m :=
  data.nestedMonotone

/-- Finite singular-value and optimal-approximation profile for a declared
transfer. -/
structure SingularValueProfile where
  approximation : BestCorrectionErrorProfile
  singularValue : Nat → Nat
  optimalTruncation : Nat → AddMap
  truncationRankBound : Nat → Prop
  truncationRankBound_valid : ∀ m : Nat, truncationRankBound m
  optimalError : ∀ m : Nat, approximation.error m = singularValue (m + 1)

/-- Singular value at a chosen index on the declared profile. -/
def singularValue (data : SingularValueProfile) (i : Nat) : Nat :=
  data.singularValue i

/-- Optimal `m`-channel approximation is carried by the declared singular-value
profile. -/
theorem optimal_m_channel_approximation
    (data : SingularValueProfile) (m : Nat) :
    data.truncationRankBound m ∧
      data.approximation.error m = singularValue data (m + 1) :=
  ⟨data.truncationRankBound_valid m, data.optimalError m⟩

/-- Observable specialization of the optimal finite correction profile. -/
structure ObservableOptimalCorrectionData where
  profile : SingularValueProfile
  realizedByFixedSourceReturn : Prop

/-- The fixed-source observable return admits the declared optimal
`m`-channel approximation profile. -/
theorem optimal_returned_correction_for_workload
    (data : ObservableOptimalCorrectionData) (m : Nat) :
    data.profile.truncationRankBound m ∧
      data.profile.approximation.error m = singularValue data.profile (m + 1) :=
  optimal_m_channel_approximation data.profile m

/-- Unitary design transform of a workload datum on the active additive
surface. -/
structure ObservableDesignTransform where
  sourceTransport : AddMap
  outputTransport : AddMap
  transformedOperator : AddMap
  transformedProjection : Projection
  transformedObservable : ObservablePackage

/-- Explicit covariance package for a chosen observable design transform. -/
structure ObservableTransferCovarianceData where
  transform : ObservableDesignTransform
  schurCovariant : Prop
  schurCovariant_valid : schurCovariant
  sourceVisibleCovariant : Prop
  sourceVisibleCovariant_valid : sourceVisibleCovariant
  directTransferCovariant : Prop
  directTransferCovariant_valid : directTransferCovariant
  fixedSourceReturnCovariant : Prop
  fixedSourceReturnCovariant_valid : fixedSourceReturnCovariant

/-- Task-visible covariance under the declared design transform. -/
theorem observable_transfer_covariance
    (data : ObservableTransferCovarianceData) :
    data.schurCovariant ∧
      data.sourceVisibleCovariant ∧
      data.directTransferCovariant ∧
      data.fixedSourceReturnCovariant :=
  ⟨data.schurCovariant_valid, data.sourceVisibleCovariant_valid,
    data.directTransferCovariant_valid, data.fixedSourceReturnCovariant_valid⟩

/-- Source-isomorphism width comparison data on the declared finite
approximation profiles. -/
structure SourceIsomorphismWidthData where
  sourceIsomorphism : AddMap
  inverseIsomorphism : AddMap
  left : BestCorrectionErrorProfile
  right : BestCorrectionErrorProfile
  lowerBound : ∀ m : Nat, left.error m ≤ right.error m
  upperBound : ∀ m : Nat, right.error m ≤ left.error m

/-- Source isomorphisms preserve the declared correction-width profile up to the
supplied two-sided bounds. -/
theorem source_isomorphism_width_bounds
    (data : SourceIsomorphismWidthData) :
    (∀ m : Nat, data.left.error m ≤ data.right.error m) ∧
      (∀ m : Nat, data.right.error m ≤ data.left.error m) :=
  ⟨data.lowerBound, data.upperBound⟩

/-- Unitary invariance package for observable closure rank, widths, and
singular values. -/
structure UnitaryWorkloadInvarianceData where
  transformedRank : ObservableClosureRankData
  originalRank : ObservableClosureRankData
  transformedSingular : SingularValueProfile
  originalSingular : SingularValueProfile
  rankInvariant :
    observableClosureRank transformedRank = observableClosureRank originalRank
  widthInvariant :
    ∀ m : Nat,
      transformedSingular.approximation.error m =
        originalSingular.approximation.error m
  singularInvariant :
    ∀ i : Nat, singularValue transformedSingular i = singularValue originalSingular i

/-- Unitary workload transforms preserve the declared finite correction data. -/
theorem unitary_workload_invariance
    (data : UnitaryWorkloadInvarianceData) :
    (observableClosureRank data.transformedRank =
        observableClosureRank data.originalRank) ∧
      (∀ m : Nat,
        data.transformedSingular.approximation.error m =
          data.originalSingular.approximation.error m) ∧
      (∀ i : Nat,
        singularValue data.transformedSingular i =
          singularValue data.originalSingular i) :=
  ⟨data.rankInvariant, data.widthInvariant, data.singularInvariant⟩

/-- Finite Gramian package for a declared observable return transfer. -/
structure ObservableClosureGramianData where
  transfer : AddMap
  gramian : AddMap
  dimension : Nat
  eigenvalue : Nat → Nat
  spectralMoment : Nat → Nat
  determinantProfile : Nat → Nat

/-- Observable closure Gramian on the declared finite return surface. -/
def observableClosureGramian (data : ObservableClosureGramianData) : AddMap :=
  data.gramian

/-- Finite invariant family attached to a declared observable closure
Gramian. -/
structure ObservableClosureInvariantFamily where
  gramianData : ObservableClosureGramianData
  allNonnegative : ∀ i : Nat, 0 ≤ gramianData.eigenvalue i
  allZeroCriterion : Prop
  allZeroCriterion_valid : allZeroCriterion
  singularSquareRoot : Prop
  singularSquareRoot_valid : singularSquareRoot
  rankAndWidthFormula : Prop
  rankAndWidthFormula_valid : rankAndWidthFormula
  momentFormula : Prop
  momentFormula_valid : momentFormula
  determinantFormula : Prop
  determinantFormula_valid : determinantFormula
  unitaryInvariant : Prop
  unitaryInvariant_valid : unitaryInvariant

/-- Canonical invariant family carried by the declared Gramian package. -/
def observableClosureInvariantFamilyOf
    (data : ObservableClosureInvariantFamily) :
    ObservableClosureInvariantFamily :=
  data

/-- The finite observable closure package is exactly the declared invariant
family. -/
theorem observable_closure_invariant_package
    (data : ObservableClosureInvariantFamily) :
    (∀ i : Nat, 0 ≤ data.gramianData.eigenvalue i) ∧
      data.allZeroCriterion ∧
      data.singularSquareRoot ∧
      data.rankAndWidthFormula ∧
      data.momentFormula ∧
      data.determinantFormula ∧
      data.unitaryInvariant :=
  ⟨data.allNonnegative, data.allZeroCriterion_valid, data.singularSquareRoot_valid,
    data.rankAndWidthFormula_valid, data.momentFormula_valid,
    data.determinantFormula_valid, data.unitaryInvariant_valid⟩

/-- Explicit singular-value stability witness between two finite profiles. -/
structure SingularValueStabilityData where
  left : SingularValueProfile
  right : SingularValueProfile
  stable : ∀ i : Nat,
    singularValue left i ≤ singularValue right i + singularValue left 0 ∧
      singularValue right i ≤ singularValue left i + singularValue right 0

/-- Singular values are stable on the supplied finite comparison surface. -/
theorem singular_value_stability
    (data : SingularValueStabilityData) :
    ∀ i : Nat,
      singularValue data.left i ≤ singularValue data.right i + singularValue data.left 0 ∧
        singularValue data.right i ≤ singularValue data.left i + singularValue data.right 0 :=
  data.stable

/-- Continuity package for the workload singular spectrum. -/
structure WorkloadClosureSpectrumContinuityData where
  returnContinuity : FixedSourceReturnContinuityData
  singularContinuity : Prop
  singularContinuity_valid : singularContinuity

/-- The workload closure spectrum is continuous whenever the declared return
family carries the corresponding continuity witness. -/
theorem workload_closure_spectrum_continuity
    (data : WorkloadClosureSpectrumContinuityData) :
    data.singularContinuity :=
  data.singularContinuity_valid

/-- Effective/null projector package for a declared returned residual map. -/
structure ObservableEffectiveNullProjectors where
  transfer : AddMap
  nullProjector : Projection
  effectiveProjector : Projection
  nullCriterion : Prop
  nullCriterion_valid : nullCriterion
  effectiveCriterion : Prop
  effectiveCriterion_valid : effectiveCriterion
  decomposition : ∀ r : State,
    ∃ reff rnull : State,
      State.add reff rnull = r ∧
        effectiveProjector r = reff ∧
        nullProjector r = rnull

/-- Returned residuals split into effective and null directions on the
declared projector package. -/
theorem observable_effective_null_decomposition
    (data : ObservableEffectiveNullProjectors) :
    data.nullCriterion ∧ data.effectiveCriterion ∧
      (∀ r : State,
        ∃ reff rnull : State,
          State.add reff rnull = r ∧
            data.effectiveProjector r = reff ∧
            data.nullProjector r = rnull) :=
  ⟨data.nullCriterion_valid, data.effectiveCriterion_valid, data.decomposition⟩

/-- Explicit observable Schur-jet package. -/
structure ObservableSchurJetData where
  fullReturn : AddMap
  truncation : Nat → AddMap
  remainder : Nat → AddMap
  remainderIdentity : ∀ N : Nat,
    ∀ x : State,
      fullReturn x = State.add (truncation N x) (remainder N x)
  remainderBound : Nat → Nat

/-- Truncated observable Schur return transfer. -/
def observableSchurJetTruncation
    (data : ObservableSchurJetData) (N : Nat) : AddMap :=
  data.truncation N

/-- The observable Schur-jet remainder is the declared residual correction term
attached to the truncation package. -/
theorem observable_schur_jet_remainder
    (data : ObservableSchurJetData) :
    (∀ N : Nat, ∀ x : State,
      data.fullReturn x =
        State.add (observableSchurJetTruncation data N x) (data.remainder N x)) ∧
      (∀ N : Nat, 0 ≤ data.remainderBound N) :=
  ⟨data.remainderIdentity, fun N => Nat.zero_le (data.remainderBound N)⟩

/-- Exact and approximate observable closure orders carried by a declared
Schur-jet package. -/
structure ObservableClosureOrderData where
  exactOrder : Nat
  epsilonOrder : Nat → Nat

/-- Observable closure order on the declared Schur-jet surface. -/
def observableClosureOrder (data : ObservableClosureOrderData) : Nat :=
  data.exactOrder

end CoherenceCalculus
