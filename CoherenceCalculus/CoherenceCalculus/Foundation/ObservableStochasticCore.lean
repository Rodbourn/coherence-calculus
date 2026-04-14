import CoherenceCalculus.Foundation.ObservableCorrectionCore

/-!
# Foundation.ObservableStochasticCore

Finite stochastic and coded closure surfaces for observable-relative closure.

This file keeps the stochastic/coded tail of the observable-relative closure
chapter on the active import-free lane. The deterministic transfer remains the
primary object. The stochastic layer is recorded only through explicit local
certificates for workload support, kernels, rate profiles, entropy bounds,
finite seed charging, covariance bookkeeping, and observable returned
corrections.
-/

namespace CoherenceCalculus

/-- Explicit support workload datum for a selected transfer target. -/
structure SupportWorkloadData where
  support : State → Prop

/-- Explicit probabilistic workload datum with a declared finite second-moment
bound. -/
structure ProbabilisticWorkloadData where
  support : State → Prop
  finiteSecondMoment : Prop

/-- Stochastic closure kernel with explicit mean and covariance fields on the
active additive state space. -/
structure StochasticClosureKernel where
  support : State → Prop
  mean : State → State
  covariance : State → AddMap
  finiteSecondMoment : ∀ x : State, support x → Prop

/-- Pointwise bias/variance package for a chosen stochastic closure kernel and
target law. -/
structure StochasticBiasVarianceData where
  kernel : StochasticClosureKernel
  target : State → State
  pointwiseError : State → Nat
  squaredBias : State → Nat
  traceCovariance : State → Nat
  identity : ∀ x : State, kernel.support x →
    pointwiseError x = squaredBias x + traceCovariance x

/-- Pointwise stochastic closure error splits into squared bias and covariance
trace on the declared kernel package. -/
theorem pointwise_bias_variance
    (data : StochasticBiasVarianceData) (x : State) (hx : data.kernel.support x) :
    data.pointwiseError x = data.squaredBias x + data.traceCovariance x :=
  data.identity x hx

/-- Integrated bias/variance package for a probabilistic workload. -/
structure IntegratedBiasVarianceData where
  kernel : StochasticClosureKernel
  totalError : Nat
  totalBias : Nat
  totalTrace : Nat
  identity : totalError = totalBias + totalTrace

/-- Integrated stochastic closure error splits into total bias and total
covariance trace on the declared workload package. -/
theorem integrated_bias_variance
    (data : IntegratedBiasVarianceData) :
    data.totalError = data.totalBias + data.totalTrace :=
  data.identity

/-- Zero-covariance versus deterministic-at-the-mean criterion for a chosen
kernel field. -/
structure ZeroCovarianceCriterionData where
  kernel : StochasticClosureKernel
  covarianceZero : State → Prop
  deterministicAtMean : State → Prop
  criterion : ∀ x : State, kernel.support x →
    (covarianceZero x ↔ deterministicAtMean x)

/-- Vanishing covariance is equivalent to deterministic concentration at the
mean on the declared kernel surface. -/
theorem zero_covariance_criterion
    (data : ZeroCovarianceCriterionData) (x : State) (hx : data.kernel.support x) :
    data.covarianceZero x ↔ data.deterministicAtMean x := by
  have hcriterion :
      data.kernel.support x →
        (data.covarianceZero x ↔ data.deterministicAtMean x) :=
    data.criterion x
  exact hcriterion hx

/-- Exactness versus unbiasedness-plus-zero-noise package for a fixed target
law. -/
structure DeterministicZeroNoiseData where
  kernel : StochasticClosureKernel
  target : State → State
  exact : Prop
  unbiased : Prop
  zeroCovariance : Prop
  exact_iff : exact ↔ unbiased ∧ zeroCovariance

/-- Deterministic closure is exactly the unbiased zero-noise edge on the
declared kernel package. -/
theorem deterministic_zero_noise_edge
    (data : DeterministicZeroNoiseData) :
    data.exact ↔ data.unbiased ∧ data.zeroCovariance :=
  data.exact_iff

/-- Seeded coded stochastic closure datum on the active additive state space. -/
structure SeededClosureCode where
  support : State → Prop
  Seed : Type
  Alphabet : Type
  decoder : Alphabet → Seed → State
  length : Alphabet → Nat
  kraft : Prop
  mean : State → State
  covariance : State → AddMap
  pointwiseLength : State → Nat

/-- Pointwise, worst-case, and probabilistic rate profile for a chosen coded
closure datum. -/
structure ClosureRateProfile where
  code : SeededClosureCode
  worstCaseLength : Nat
  meanLength : Nat
  worstCaseBound : ∀ x : State, code.support x → code.pointwiseLength x ≤ worstCaseLength
  meanLengthBound : Prop

/-- Pointwise expected code length on the declared coded closure surface. -/
def pointwiseCodeLength (data : ClosureRateProfile) (x : State) : Nat :=
  data.code.pointwiseLength x

/-- Worst-case code length on the declared support workload. -/
def worstCaseCodeLength (data : ClosureRateProfile) : Nat :=
  data.worstCaseLength

/-- Probabilistic mean code length on the declared workload datum. -/
def meanCodeLength (data : ClosureRateProfile) : Nat :=
  data.meanLength

/-- Worst-case and mean-square stochastic closure widths, with and without the
unbiasedness constraint. -/
structure ClosureWidthProfile where
  worstCase : Nat → Nat
  meanSquare : Nat → Nat
  worstCaseUnbiased : Nat → Nat
  meanSquareUnbiased : Nat → Nat

/-- Worst-case stochastic closure width at the chosen rate budget. -/
def worstCaseClosureWidth (data : ClosureWidthProfile) (b : Nat) : Nat :=
  data.worstCase b

/-- Mean-square stochastic closure width at the chosen rate budget. -/
def meanSquareClosureWidth (data : ClosureWidthProfile) (b : Nat) : Nat :=
  data.meanSquare b

/-- Worst-case unbiased stochastic closure width at the chosen rate budget. -/
def worstCaseUnbiasedClosureWidth (data : ClosureWidthProfile) (b : Nat) : Nat :=
  data.worstCaseUnbiased b

/-- Mean-square unbiased stochastic closure width at the chosen rate budget. -/
def meanSquareUnbiasedClosureWidth (data : ClosureWidthProfile) (b : Nat) : Nat :=
  data.meanSquareUnbiased b

/-- Monotonicity package for stochastic closure widths under larger budgets and
larger admissible classes. -/
structure StochasticWidthMonotonicityData where
  base : ClosureWidthProfile
  expanded : ClosureWidthProfile
  budgetMonotone : ∀ {b b' : Nat}, b ≤ b' →
    worstCaseClosureWidth base b' ≤ worstCaseClosureWidth base b ∧
      meanSquareClosureWidth base b' ≤ meanSquareClosureWidth base b ∧
      worstCaseUnbiasedClosureWidth base b' ≤ worstCaseUnbiasedClosureWidth base b ∧
      meanSquareUnbiasedClosureWidth base b' ≤ meanSquareUnbiasedClosureWidth base b
  classMonotone : ∀ b : Nat,
    worstCaseClosureWidth expanded b ≤ worstCaseClosureWidth base b ∧
      meanSquareClosureWidth expanded b ≤ meanSquareClosureWidth base b ∧
      worstCaseUnbiasedClosureWidth expanded b ≤ worstCaseUnbiasedClosureWidth base b ∧
      meanSquareUnbiasedClosureWidth expanded b ≤ meanSquareUnbiasedClosureWidth base b

/-- Stochastic closure widths are monotone in the rate budget and decrease when
the admissible class enlarges. -/
theorem stochastic_width_monotonicity
    (data : StochasticWidthMonotonicityData) :
    (∀ {b b' : Nat}, b ≤ b' →
      worstCaseClosureWidth data.base b' ≤ worstCaseClosureWidth data.base b ∧
        meanSquareClosureWidth data.base b' ≤ meanSquareClosureWidth data.base b ∧
        worstCaseUnbiasedClosureWidth data.base b' ≤
          worstCaseUnbiasedClosureWidth data.base b ∧
        meanSquareUnbiasedClosureWidth data.base b' ≤
          meanSquareUnbiasedClosureWidth data.base b) ∧
      (∀ b : Nat,
        worstCaseClosureWidth data.expanded b ≤ worstCaseClosureWidth data.base b ∧
          meanSquareClosureWidth data.expanded b ≤ meanSquareClosureWidth data.base b ∧
          worstCaseUnbiasedClosureWidth data.expanded b ≤
            worstCaseUnbiasedClosureWidth data.base b ∧
          meanSquareUnbiasedClosureWidth data.expanded b ≤
            meanSquareUnbiasedClosureWidth data.base b) :=
  ⟨data.budgetMonotone, data.classMonotone⟩

/-- Unseeded finite codebook datum with an explicit barycentric selector. -/
structure UnseededCodebook where
  support : State → Prop
  alphabetSize : Nat
  decoderAtom : Nat → State
  barycentricSelector : State → Nat → Nat
  barycentricSelector_valid : Prop

/-- Exactness of unseeded finite-alphabet unbiased codes is equivalent to the
existence of an explicit barycentric selector. -/
structure BarycentricExactnessData where
  target : State → State
  alphabetSize : Nat
  hasUnseededUnbiasedCode : Prop
  hasBarycentricSelector : Prop
  criterion : hasUnseededUnbiasedCode ↔ hasBarycentricSelector

/-- Barycentric selector data is exactly the declared unseeded unbiased coding
criterion. -/
theorem barycentric_exactness_criterion
    (data : BarycentricExactnessData) :
    data.hasUnseededUnbiasedCode ↔ data.hasBarycentricSelector :=
  data.criterion

/-- Explicit closure-hull-rank package for a target law. -/
structure ClosureHullRankData where
  target : State → State
  rank : Nat
  finiteWitness : Prop
  minimality : Prop

/-- Closure hull rank on the declared target surface. -/
def closureHullRank (data : ClosureHullRankData) : Nat :=
  data.rank

/-- Fixed-length exact-rate package derived from a finite closure hull rank. -/
structure FixedLengthRateData where
  hull : ClosureHullRankData
  exactBits : Nat
  exactCodeExists : Prop
  noShorterCode : Prop
  exactCodeExists_valid : exactCodeExists
  noShorterCode_valid : noShorterCode

/-- Finite closure hull rank forces the declared exact fixed-length rate and
its lower bound. -/
theorem exact_fixed_length_stochastic_rate
    (data : FixedLengthRateData) :
    data.exactCodeExists ∧ data.noShorterCode := by
  exact ⟨data.exactCodeExists_valid, data.noShorterCode_valid⟩

/-- Explicit one-bit unbiased scalar closure example package. -/
structure OneBitUnbiasedScalarClosureData where
  oneBit : Prop
  exactInExpectation : Prop
  varianceLaw : Prop
  oneBit_valid : oneBit
  exactInExpectation_valid : exactInExpectation
  varianceLaw_valid : varianceLaw

/-- The one-bit scalar closure example carries the declared unbiasedness and
variance profile. -/
theorem one_bit_unbiased_scalar_closure
    (data : OneBitUnbiasedScalarClosureData) :
    data.oneBit ∧ data.exactInExpectation ∧ data.varianceLaw := by
  exact ⟨data.oneBit_valid, data.exactInExpectation_valid, data.varianceLaw_valid⟩

/-- Entropy profile attached to a seeded coded stochastic closure datum. -/
structure ClosureEntropyProfile where
  rate : ClosureRateProfile
  entropy : State → Nat
  meanEntropy : Nat
  pointwiseBound : ∀ x : State, entropy x ≤ pointwiseCodeLength rate x
  integratedBound : meanEntropy ≤ meanCodeLength rate

/-- Pointwise closure entropy on the declared coded closure profile. -/
def closureEntropy (data : ClosureEntropyProfile) (x : State) : Nat :=
  data.entropy x

/-- Shannon-style entropy is bounded above by code length on the declared rate
profile. -/
theorem entropy_lower_bound
    (data : ClosureEntropyProfile) :
    (∀ x : State, closureEntropy data x ≤ pointwiseCodeLength data.rate x) ∧
      data.meanEntropy ≤ meanCodeLength data.rate :=
  ⟨data.pointwiseBound, data.integratedBound⟩

/-- Finite-seed charging package collapsing a finite shared seed into the
alphabet. -/
structure FiniteSeedChargingData where
  original : SeededClosureCode
  charged : SeededClosureCode
  onePointSeed : Prop
  sameDecodedLaw : Prop
  chargedLengths : Prop
  kraftPreserved : Prop
  onePointSeed_valid : onePointSeed
  sameDecodedLaw_valid : sameDecodedLaw
  chargedLengths_valid : chargedLengths
  kraftPreserved_valid : kraftPreserved

/-- Finite shared seeds can be charged into the output alphabet on the declared
coded closure surface. -/
theorem finite_seed_charging
    (data : FiniteSeedChargingData) :
    data.onePointSeed ∧ data.sameDecodedLaw ∧
      data.chargedLengths ∧ data.kraftPreserved := by
  exact ⟨data.onePointSeed_valid, data.sameDecodedLaw_valid,
    data.chargedLengths_valid, data.kraftPreserved_valid⟩

/-- Linear output-composition package for a coded stochastic closure datum. -/
structure LinearOutputCompositionData where
  original : SeededClosureCode
  composed : SeededClosureCode
  meanFormula : Prop
  covarianceFormula : Prop
  worstCaseRatePreserved : Prop
  meanRatePreserved : Prop
  meanFormula_valid : meanFormula
  covarianceFormula_valid : covarianceFormula
  worstCaseRatePreserved_valid : worstCaseRatePreserved
  meanRatePreserved_valid : meanRatePreserved

/-- Linear output composition preserves the declared mean, covariance, and rate
profiles. -/
theorem linear_output_composition
    (data : LinearOutputCompositionData) :
    data.meanFormula ∧ data.covarianceFormula ∧
      data.worstCaseRatePreserved ∧ data.meanRatePreserved := by
  exact ⟨data.meanFormula_valid, data.covarianceFormula_valid,
    data.worstCaseRatePreserved_valid, data.meanRatePreserved_valid⟩

/-- Unitary source/output covariance package for a coded stochastic closure
datum. -/
structure UnitaryCodedClosureCovarianceData where
  original : SeededClosureCode
  transformed : SeededClosureCode
  meanFormula : Prop
  covarianceFormula : Prop
  pointwiseRatePreserved : Prop
  workloadRatePreserved : Prop
  meanErrorInvariant : Prop
  integratedCovarianceInvariant : Prop
  meanFormula_valid : meanFormula
  covarianceFormula_valid : covarianceFormula
  pointwiseRatePreserved_valid : pointwiseRatePreserved
  workloadRatePreserved_valid : workloadRatePreserved
  meanErrorInvariant_valid : meanErrorInvariant
  integratedCovarianceInvariant_valid : integratedCovarianceInvariant

/-- Unitary source/output transforms preserve the declared coded closure
statistics. -/
theorem unitary_coded_closure_covariance
    (data : UnitaryCodedClosureCovarianceData) :
    data.meanFormula ∧ data.covarianceFormula ∧
      data.pointwiseRatePreserved ∧ data.workloadRatePreserved ∧
      data.meanErrorInvariant ∧ data.integratedCovarianceInvariant := by
  exact ⟨data.meanFormula_valid, data.covarianceFormula_valid,
    data.pointwiseRatePreserved_valid, data.workloadRatePreserved_valid,
    data.meanErrorInvariant_valid, data.integratedCovarianceInvariant_valid⟩

/-- Closure covariance operator and integrated error package for a coded
stochastic closure datum. -/
structure ClosureCovarianceOperatorData where
  code : SeededClosureCode
  workload : ProbabilisticWorkloadData
  operator : AddMap
  positiveSemidefinite : Prop
  totalError : Nat
  totalBias : Nat
  totalTrace : Nat
  identity : totalError = totalBias + totalTrace
  unbiased : Prop
  unbiasedIdentity : unbiased → totalError = totalTrace
  positiveSemidefinite_valid : positiveSemidefinite

/-- Closure covariance operator on the declared probabilistic workload. -/
def closureCovarianceOperator (data : ClosureCovarianceOperatorData) : AddMap :=
  data.operator

/-- The declared closure covariance operator is positive semidefinite. -/
theorem closure_covariance_positive
    (data : ClosureCovarianceOperatorData) :
    data.positiveSemidefinite := by
  exact data.positiveSemidefinite_valid

/-- Integrated stochastic closure error is exactly the declared bias/covariance
split, with a trace-only specialization on the unbiased lane. -/
theorem integrated_stochastic_closure_error
    (data : ClosureCovarianceOperatorData) :
    data.totalError = data.totalBias + data.totalTrace ∧
      (data.unbiased → data.totalError = data.totalTrace) :=
  ⟨data.identity, data.unbiasedIdentity⟩

/-- Observable returned-closure code on the active additive state space. -/
structure ObservableReturnedClosureCode where
  baseObservable : AddMap
  returnedTarget : State → State
  correctedEstimator : State → State
  scaleSq : Nat
  unbiased : Prop
  unbiased_valid : unbiased
  expectationFormula : ∀ x : State,
    correctedEstimator x =
      State.add (baseObservable x) (returnedTarget x)
  meanSquareError : State → Nat
  returnedError : State → Nat
  meanSquareFormula : ∀ x : State,
    meanSquareError x = scaleSq * returnedError x

/-- Unbiased returned correction recovers the declared corrected observable law
in expectation. -/
theorem unbiased_returned_correction
    (data : ObservableReturnedClosureCode) :
    data.unbiased ∧
      (∀ x : State,
        data.correctedEstimator x =
          State.add (data.baseObservable x) (data.returnedTarget x)) := by
  exact ⟨data.unbiased_valid, data.expectationFormula⟩

/-- Observable mean-square error is exactly the declared scaled returned-error
profile. -/
theorem observable_mean_square_error
    (data : ObservableReturnedClosureCode) :
    ∀ x : State, data.meanSquareError x = data.scaleSq * data.returnedError x :=
  data.meanSquareFormula

end CoherenceCalculus
