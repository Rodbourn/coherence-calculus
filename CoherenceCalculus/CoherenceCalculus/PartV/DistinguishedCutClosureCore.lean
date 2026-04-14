import CoherenceCalculus.PartV.RankTwoCompressionCore

/-!
# PartV.DistinguishedCutClosureCore

Detached Part V closure packages built on the generic rank-two compression
surface.

This file does not add new foundational content. It organizes the local
closure-route data into a reader-facing family of packages:

- determinant-anchored strict-compiler consequences
- distinguished-cut certificate packages
- single-inequality frontier consequences
- collapse-defect strictness outcomes

The public surface is intended to read as a small hierarchy of mathematical
objects and consequences rather than as proof-assembly history.
-/

namespace CoherenceCalculus

/-- The closure route needs a small amount of extra scalar arithmetic beyond the
rank-two compression package: determinant-residue, collapse-defect, and the
preferred branch-ratio readouts from those exact local faces. -/
structure DistinguishedCutClosureArithmetic
    {Scalar : Type} (arith : RankTwoCompressionArithmetic Scalar) where
  determinantResidueFromCompression :
    RankTwoSchurCompressionCoordinates arith → Scalar
  branchRatioFromDeterminantResidue : Scalar → Scalar
  collapseDefectFromMoments : Scalar → Scalar → Scalar
  balanceFromCollapseDefectAndTrace : Scalar → Scalar → Scalar
  betaFromCollapseDefectAndTrace : Scalar → Scalar → Scalar
  determinantResidueFromCollapseDefectAndTrace : Scalar → Scalar → Scalar
  gammaFromCollapseDefectAndTrace : Scalar → Scalar → Scalar
  branchRatioFromCollapseDefectAndTrace : Scalar → Scalar → Scalar

/-- The strict-compiler output singled out by the determinant-anchored closure
route. -/
structure StrictTwoChannelCompilerOutcome
    {Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    (closureArith : DistinguishedCutClosureArithmetic arith)
    (determinantResidue : Scalar) where
  distinguishedCutStrict : Prop
  strictRegime : Prop
  branchRatio : Scalar
  branchRatio_exact :
    branchRatio =
      closureArith.branchRatioFromDeterminantResidue determinantResidue
  exactScalarFaceReduction : Prop
  coordinateIndependentTrichotomy : Prop

/-- The determinant-anchored strict compiler corollary retains only the scalar
face reduction and coordinate-independence clauses of the full strict-compiler
package. -/
structure DeterminantAnchoredStrictTwoChannelCompilerOutcome where
  exactScalarFaceReduction : Prop
  coordinateIndependentTrichotomy : Prop

/-- The proper closure route keeps only the strict-regime and scalar-face
reduction clauses needed by the frontier corollary. -/
structure ProperClosureRouteCurrentTwoChannelFrontierOutcome where
  strictRegime : Prop
  exactScalarFaceReduction : Prop

/-- A canonically anchored determinant-positive witness datum consists of a
distinguished local compression package together with a positive determinant
residue and the strict-compiler consequences carried there. -/
structure CanonicallyAnchoredDeterminantPositiveTwoChannelWitnessDatum
    {Channel Horizon Scalar : Type}
    (surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar)
    (arith : RankTwoCompressionArithmetic Scalar)
    (closureArith : DistinguishedCutClosureArithmetic arith) where
  distinguishedCompression : RankTwoSchurCompressionDatum surface arith
  determinantResidue : Scalar
  determinantResidue_exact :
    determinantResidue =
      closureArith.determinantResidueFromCompression
        distinguishedCompression.coordinates
  determinantResiduePositive : Prop
  distinguishedCutStrict : Prop
  strictRegime : Prop
  branchRatio : Scalar
  branchRatio_exact :
    branchRatio =
      closureArith.branchRatioFromDeterminantResidue determinantResidue
  exactScalarFaceReduction : Prop
  coordinateIndependentTrichotomy : Prop

namespace CanonicallyAnchoredDeterminantPositiveTwoChannelWitnessDatum

/-- The strict-compiler output carried by a determinant-positive anchored
witness datum. -/
def strictCompilerOutcome
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveTwoChannelWitnessDatum
      surface arith closureArith) :
    StrictTwoChannelCompilerOutcome closureArith datum.determinantResidue := by
  refine
    { distinguishedCutStrict := datum.distinguishedCutStrict
      strictRegime := datum.strictRegime
      branchRatio := datum.branchRatio
      branchRatio_exact := datum.branchRatio_exact
      exactScalarFaceReduction := datum.exactScalarFaceReduction
      coordinateIndependentTrichotomy := datum.coordinateIndependentTrichotomy }

/-- A determinant-positive anchored witness therefore forces the strict
two-channel compiler package on that same local surface. -/
theorem strictCompiler_nonempty
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveTwoChannelWitnessDatum
      surface arith closureArith) :
    Nonempty
      (StrictTwoChannelCompilerOutcome closureArith datum.determinantResidue) := by
  exact ⟨datum.strictCompilerOutcome⟩

/-- The strict-compiler output keeps exactly the strictness and scalar-face
consequences already carried by the anchored witness datum. -/
theorem strictCutSurface
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveTwoChannelWitnessDatum
      surface arith closureArith) :
    datum.strictCompilerOutcome.distinguishedCutStrict =
      datum.distinguishedCutStrict := by
  rfl

theorem strictRegimeSurface
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveTwoChannelWitnessDatum
      surface arith closureArith) :
    datum.strictCompilerOutcome.strictRegime = datum.strictRegime := by
  rfl

/-- The strict-compiler output keeps exactly the strictness and scalar-face
consequences already carried by the anchored witness datum. -/
theorem strictnessReadoutSurface
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveTwoChannelWitnessDatum
      surface arith closureArith) :
    datum.strictCompilerOutcome.distinguishedCutStrict = datum.distinguishedCutStrict ∧
      datum.strictCompilerOutcome.strictRegime = datum.strictRegime := by
  exact ⟨datum.strictCutSurface, datum.strictRegimeSurface⟩

/-- The same strict-compiler output also keeps the scalar-face readout already
carried by the anchored witness datum. -/
theorem branchRatioSurface
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveTwoChannelWitnessDatum
      surface arith closureArith) :
    datum.strictCompilerOutcome.branchRatio = datum.branchRatio := by
  rfl

theorem exactScalarFaceSurface
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveTwoChannelWitnessDatum
      surface arith closureArith) :
    datum.strictCompilerOutcome.exactScalarFaceReduction =
      datum.exactScalarFaceReduction := by
  rfl

theorem strictTrichotomySurface
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveTwoChannelWitnessDatum
      surface arith closureArith) :
    datum.strictCompilerOutcome.coordinateIndependentTrichotomy =
      datum.coordinateIndependentTrichotomy := by
  rfl

/-- The same strict-compiler output also keeps the scalar-face readout already
carried by the anchored witness datum. -/
theorem scalarFaceReadoutSurface
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveTwoChannelWitnessDatum
      surface arith closureArith) :
    datum.strictCompilerOutcome.branchRatio = datum.branchRatio ∧
      datum.strictCompilerOutcome.exactScalarFaceReduction =
        datum.exactScalarFaceReduction ∧
      datum.strictCompilerOutcome.coordinateIndependentTrichotomy =
        datum.coordinateIndependentTrichotomy := by
  exact
    ⟨datum.branchRatioSurface,
      datum.exactScalarFaceSurface,
      datum.strictTrichotomySurface⟩

/-- The strict-compiler output keeps exactly the strictness and scalar-face
consequences already carried by the anchored witness datum. -/
theorem strictCompilerSurface
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveTwoChannelWitnessDatum
      surface arith closureArith) :
    datum.strictCompilerOutcome.distinguishedCutStrict = datum.distinguishedCutStrict ∧
      datum.strictCompilerOutcome.strictRegime = datum.strictRegime ∧
      datum.strictCompilerOutcome.branchRatio = datum.branchRatio ∧
      datum.strictCompilerOutcome.exactScalarFaceReduction =
        datum.exactScalarFaceReduction ∧
      datum.strictCompilerOutcome.coordinateIndependentTrichotomy =
        datum.coordinateIndependentTrichotomy := by
  have hstrict := datum.strictnessReadoutSurface
  have hscalar := datum.scalarFaceReadoutSurface
  rcases hstrict with ⟨hcut, hregime⟩
  rcases hscalar with ⟨hratio, hface, htrichotomy⟩
  exact ⟨hcut, hregime, hratio, hface, htrichotomy⟩

/-- The anchored witness datum already carries both the strict-compiler readout
surface and the corresponding strict-compiler object. -/
theorem strictCompilerWitnessSurface
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveTwoChannelWitnessDatum
      surface arith closureArith) :
    (datum.strictCompilerOutcome.distinguishedCutStrict =
        datum.distinguishedCutStrict ∧
      datum.strictCompilerOutcome.strictRegime = datum.strictRegime ∧
      datum.strictCompilerOutcome.branchRatio = datum.branchRatio ∧
      datum.strictCompilerOutcome.exactScalarFaceReduction =
        datum.exactScalarFaceReduction ∧
      datum.strictCompilerOutcome.coordinateIndependentTrichotomy =
        datum.coordinateIndependentTrichotomy) ∧
      Nonempty
        (StrictTwoChannelCompilerOutcome
          closureArith datum.determinantResidue) := by
  exact ⟨datum.strictCompilerSurface, datum.strictCompiler_nonempty⟩

/-- The determinant-anchored strict compiler corollary is the scalar-face
reduction consequence of the anchored strict-compiler package. -/
def compilerCorollary
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveTwoChannelWitnessDatum
      surface arith closureArith) :
    DeterminantAnchoredStrictTwoChannelCompilerOutcome := by
  exact
    { exactScalarFaceReduction := datum.exactScalarFaceReduction
      coordinateIndependentTrichotomy :=
        datum.coordinateIndependentTrichotomy }

/-- The determinant-anchored corollary keeps exactly the scalar-face reduction
and coordinate-independence clauses carried by the strict witness datum. -/
theorem scalarReductionSurface
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveTwoChannelWitnessDatum
      surface arith closureArith) :
    datum.compilerCorollary.exactScalarFaceReduction = datum.exactScalarFaceReduction := by
  rfl

/-- The same determinant-anchored corollary also keeps the coordinate-free
trichotomy clause carried by the strict witness datum. -/
theorem trichotomySurface
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveTwoChannelWitnessDatum
      surface arith closureArith) :
    datum.compilerCorollary.coordinateIndependentTrichotomy =
        datum.coordinateIndependentTrichotomy := by
  rfl

/-- The determinant-anchored corollary keeps exactly the scalar-face reduction
and coordinate-independence clauses carried by the strict witness datum. -/
theorem compilerCorollarySurface
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveTwoChannelWitnessDatum
      surface arith closureArith) :
    datum.compilerCorollary.exactScalarFaceReduction = datum.exactScalarFaceReduction ∧
    datum.compilerCorollary.coordinateIndependentTrichotomy =
        datum.coordinateIndependentTrichotomy := by
  exact ⟨datum.scalarReductionSurface, datum.trichotomySurface⟩

/-- The anchored witness datum already carries both the determinant-anchored
compiler-corollary readout and the corresponding corollary object. -/
theorem compilerCorollaryWitnessSurface
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveTwoChannelWitnessDatum
      surface arith closureArith) :
    (datum.compilerCorollary.exactScalarFaceReduction =
        datum.exactScalarFaceReduction ∧
      datum.compilerCorollary.coordinateIndependentTrichotomy =
        datum.coordinateIndependentTrichotomy) ∧
      Nonempty DeterminantAnchoredStrictTwoChannelCompilerOutcome := by
  exact ⟨datum.compilerCorollarySurface, ⟨datum.compilerCorollary⟩⟩

/-- The determinant-anchored strict compiler corollary is the scalar-face
reduction consequence of the anchored strict-compiler package. -/
theorem compilerCorollary_nonempty
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveTwoChannelWitnessDatum
      surface arith closureArith) :
    Nonempty DeterminantAnchoredStrictTwoChannelCompilerOutcome := by
  exact ⟨datum.compilerCorollary⟩

end CanonicallyAnchoredDeterminantPositiveTwoChannelWitnessDatum

/-- A distinguished nondegenerate rank-two cut is just a distinguished local
compression package together with positive trace on that same cut. -/
structure DistinguishedNondegenerateRankTwoTwoChannelCut
    {Channel Horizon Scalar : Type}
    (surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar)
    (arith : RankTwoCompressionArithmetic Scalar) where
  distinguishedCompression : RankTwoSchurCompressionDatum surface arith
  positiveTrace : Prop

/-- The certificate package carried by a distinguished nondegenerate rank-two
cut: equivalent strictness criteria together with the strict-compiler
consequences they trigger. -/
structure DistinguishedCutClosureCertificatePackage
    {Channel Horizon Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    (surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar)
    (cut : DistinguishedNondegenerateRankTwoTwoChannelCut surface arith)
    (closureArith : DistinguishedCutClosureArithmetic arith) where
  strictWitness : Prop
  betaStrict : Prop
  balancePositive : Prop
  gammaStrict : Prop
  determinantResiduePositive : Prop
  lowerRootPositive : Prop
  strict_iff_beta : strictWitness ↔ betaStrict
  beta_iff_balance : betaStrict ↔ balancePositive
  beta_iff_gamma : betaStrict ↔ gammaStrict
  beta_iff_determinantResidue : betaStrict ↔ determinantResiduePositive
  beta_iff_lowerRoot : betaStrict ↔ lowerRootPositive
  strictRegime : Prop
  branchRatio : Scalar
  exactScalarFaceReduction : Prop

namespace DistinguishedCutClosureCertificatePackage

/-- Once the distinguished-cut certificate package is supplied, the equivalent
constructive closure criteria and their strict-compiler consequences are fixed. -/
theorem nonempty
    {Channel Horizon Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {cut : DistinguishedNondegenerateRankTwoTwoChannelCut surface arith}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (package : DistinguishedCutClosureCertificatePackage surface cut closureArith) :
    Nonempty
      (DistinguishedCutClosureCertificatePackage surface cut closureArith) := by
  exact ⟨package⟩

/-- The distinguished-cut certificate package already fixes the full strictness
equivalence ladder on that local cut. -/
theorem strictCriterionSurface
    {Channel Horizon Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {cut : DistinguishedNondegenerateRankTwoTwoChannelCut surface arith}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (package : DistinguishedCutClosureCertificatePackage surface cut closureArith) :
    package.strictWitness ↔ package.betaStrict := by
  exact package.strict_iff_beta

/-- The same certificate package also fixes the spectral and residue faces that
are equivalent to `beta`-strictness on that cut. -/
theorem spectralCriterionSurface
    {Channel Horizon Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {cut : DistinguishedNondegenerateRankTwoTwoChannelCut surface arith}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (package : DistinguishedCutClosureCertificatePackage surface cut closureArith) :
    (package.betaStrict ↔ package.balancePositive) ∧
      (package.betaStrict ↔ package.gammaStrict) ∧
      (package.betaStrict ↔ package.determinantResiduePositive) ∧
      (package.betaStrict ↔ package.lowerRootPositive) := by
  exact
    ⟨package.beta_iff_balance,
      package.beta_iff_gamma,
      package.beta_iff_determinantResidue,
      package.beta_iff_lowerRoot⟩

/-- The distinguished-cut certificate package already fixes the full strictness
equivalence ladder on that local cut. -/
theorem criteriaEquivalences
    {Channel Horizon Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {cut : DistinguishedNondegenerateRankTwoTwoChannelCut surface arith}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (package : DistinguishedCutClosureCertificatePackage surface cut closureArith) :
    (package.strictWitness ↔ package.betaStrict) ∧
      (package.betaStrict ↔ package.balancePositive) ∧
      (package.betaStrict ↔ package.gammaStrict) ∧
      (package.betaStrict ↔ package.determinantResiduePositive) ∧
      (package.betaStrict ↔ package.lowerRootPositive) := by
  have hstrict := package.strictCriterionSurface
  have hspectral := package.spectralCriterionSurface
  rcases hspectral with ⟨hbalance, hgamma, hresidue, hroot⟩
  exact
    ⟨hstrict, hbalance, hgamma, hresidue, hroot⟩

end DistinguishedCutClosureCertificatePackage

/-- The single-inequality closure route is the moment-inequality face of the
same distinguished-cut certificate package. -/
structure SingleInequalityClosureCriterionDatum
    {Channel Horizon Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    (surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar)
    (cut : DistinguishedNondegenerateRankTwoTwoChannelCut surface arith)
    (closureArith : DistinguishedCutClosureArithmetic arith) where
  certificates : DistinguishedCutClosureCertificatePackage surface cut closureArith
  strictMomentInequality : Prop
  moment_iff_beta : strictMomentInequality ↔ certificates.betaStrict

namespace SingleInequalityClosureCriterionDatum

/-- The single-inequality criterion is enough to recover the same strict
branch-level consequences on the distinguished cut. -/
theorem strictMomentInequality_iff_betaStrict
    {Channel Horizon Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {cut : DistinguishedNondegenerateRankTwoTwoChannelCut surface arith}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : SingleInequalityClosureCriterionDatum surface cut closureArith) :
    datum.strictMomentInequality ↔ datum.certificates.betaStrict := by
  exact datum.moment_iff_beta

def frontierOutcome
    {Channel Horizon Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {cut : DistinguishedNondegenerateRankTwoTwoChannelCut surface arith}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : SingleInequalityClosureCriterionDatum surface cut closureArith) :
    ProperClosureRouteCurrentTwoChannelFrontierOutcome := by
  exact
    { strictRegime := datum.certificates.strictRegime
      exactScalarFaceReduction := datum.certificates.exactScalarFaceReduction }

/-- The frontier readout keeps exactly the strict-regime and scalar-face
reduction clauses carried by the distinguished-cut certificates. -/
theorem strictRegimeSurface
    {Channel Horizon Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {cut : DistinguishedNondegenerateRankTwoTwoChannelCut surface arith}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : SingleInequalityClosureCriterionDatum surface cut closureArith) :
    datum.frontierOutcome.strictRegime = datum.certificates.strictRegime := by
  rfl

/-- The same frontier readout also keeps the exact scalar-face reduction
clause carried by the distinguished-cut certificates. -/
theorem scalarReductionSurface
    {Channel Horizon Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {cut : DistinguishedNondegenerateRankTwoTwoChannelCut surface arith}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : SingleInequalityClosureCriterionDatum surface cut closureArith) :
    datum.frontierOutcome.exactScalarFaceReduction =
        datum.certificates.exactScalarFaceReduction := by
  rfl

/-- The frontier readout keeps exactly the strict-regime and scalar-face
reduction clauses carried by the distinguished-cut certificates. -/
theorem frontierSurface
    {Channel Horizon Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {cut : DistinguishedNondegenerateRankTwoTwoChannelCut surface arith}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : SingleInequalityClosureCriterionDatum surface cut closureArith) :
    datum.frontierOutcome.strictRegime = datum.certificates.strictRegime ∧
    datum.frontierOutcome.exactScalarFaceReduction =
        datum.certificates.exactScalarFaceReduction := by
  exact ⟨datum.strictRegimeSurface, datum.scalarReductionSurface⟩

/-- Once the strict moment inequality is supplied, the single-inequality datum
already carries both the frontier readout and the corresponding frontier
object. -/
theorem frontierWitnessSurface
    {Channel Horizon Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {cut : DistinguishedNondegenerateRankTwoTwoChannelCut surface arith}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : SingleInequalityClosureCriterionDatum surface cut closureArith) :
    (datum.frontierOutcome.strictRegime = datum.certificates.strictRegime ∧
      datum.frontierOutcome.exactScalarFaceReduction =
        datum.certificates.exactScalarFaceReduction) ∧
      Nonempty ProperClosureRouteCurrentTwoChannelFrontierOutcome := by
  exact ⟨datum.frontierSurface, ⟨datum.frontierOutcome⟩⟩

/-- The proper closure route corollary is the direct strict-regime and
scalar-face reduction consequence of the single inequality. -/
theorem frontierOutcome_nonempty
    {Channel Horizon Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {cut : DistinguishedNondegenerateRankTwoTwoChannelCut surface arith}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : SingleInequalityClosureCriterionDatum surface cut closureArith) :
    datum.strictMomentInequality →
      Nonempty ProperClosureRouteCurrentTwoChannelFrontierOutcome := by
  intro _
  exact datum.frontierWitnessSurface.2

end SingleInequalityClosureCriterionDatum

/-- The one-channel collapse defect on a two-channel Schur cut is the exact
defect scalar read from the two local moments. -/
structure OneChannelCollapseDefectOnTwoChannelSchurCut
    {Channel Horizon Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    (surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar)
    (compression : RankTwoSchurCompressionDatum surface arith)
    (closureArith : DistinguishedCutClosureArithmetic arith) where
  value : Scalar
  value_exact :
    value =
      closureArith.collapseDefectFromMoments
        compression.coordinates.momentOne
        compression.coordinates.momentTwo

/-- Positive collapse defect is another exact strictness face on the same
distinguished cut. -/
structure PositiveCollapseDefectExactStrictnessDatum
    {Channel Horizon Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    (surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar)
    (cut : DistinguishedNondegenerateRankTwoTwoChannelCut surface arith)
    (closureArith : DistinguishedCutClosureArithmetic arith) where
  singleInequality : SingleInequalityClosureCriterionDatum surface cut closureArith
  collapseDefect :
    OneChannelCollapseDefectOnTwoChannelSchurCut
      surface cut.distinguishedCompression closureArith
  collapseDefectPositive : Prop
  defect_iff_moment :
    collapseDefectPositive ↔ singleInequality.strictMomentInequality

/-- The positive-collapse-defect route packages the exact strictness criterion
and the resulting scalar-face recoveries on the distinguished cut. -/
structure PositiveCollapseDefectStrictnessOutcome
    {Channel Horizon Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    (surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar)
    (cut : DistinguishedNondegenerateRankTwoTwoChannelCut surface arith)
    (closureArith : DistinguishedCutClosureArithmetic arith)
    (defect : OneChannelCollapseDefectOnTwoChannelSchurCut
      surface cut.distinguishedCompression closureArith) where
  defectPositive : Prop
  momentInequality : Prop
  defectPositive_iff_momentInequality :
    defectPositive ↔ momentInequality
  balance : Scalar
  beta : Scalar
  determinantResidue : Scalar
  gamma : Scalar
  branchRatio : Scalar
  balance_exact :
    balance =
      closureArith.balanceFromCollapseDefectAndTrace
        defect.value cut.distinguishedCompression.coordinates.trace
  beta_exact :
    beta =
      closureArith.betaFromCollapseDefectAndTrace
        defect.value cut.distinguishedCompression.coordinates.trace
  determinantResidue_exact :
    determinantResidue =
      closureArith.determinantResidueFromCollapseDefectAndTrace
        defect.value cut.distinguishedCompression.coordinates.trace
  gamma_exact :
    gamma =
      closureArith.gammaFromCollapseDefectAndTrace
        defect.value cut.distinguishedCompression.coordinates.trace
  branchRatio_exact :
    branchRatio =
      closureArith.branchRatioFromCollapseDefectAndTrace
        defect.value cut.distinguishedCompression.coordinates.trace
  exactScalarFaceReduction : Prop

namespace PositiveCollapseDefectExactStrictnessDatum

/-- Positive collapse defect is exactly the same strictness criterion as the
single-inequality face carried by the distinguished-cut package. -/
theorem strictnessCriterion
    {Channel Horizon Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {cut : DistinguishedNondegenerateRankTwoTwoChannelCut surface arith}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : PositiveCollapseDefectExactStrictnessDatum surface cut closureArith) :
    datum.collapseDefectPositive ↔ datum.singleInequality.strictMomentInequality := by
  exact datum.defect_iff_moment

/-- Positive collapse defect is therefore another exact strictness criterion on
the distinguished cut, with the corresponding scalar-face recovery package. -/
def strictnessOutcome
    {Channel Horizon Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {cut : DistinguishedNondegenerateRankTwoTwoChannelCut surface arith}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : PositiveCollapseDefectExactStrictnessDatum surface cut closureArith)
    (balance beta determinantResidue gamma branchRatio : Scalar)
    (balance_exact :
      balance =
        closureArith.balanceFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (beta_exact :
      beta =
        closureArith.betaFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (determinantResidue_exact :
      determinantResidue =
        closureArith.determinantResidueFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (gamma_exact :
      gamma =
        closureArith.gammaFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (branchRatio_exact :
      branchRatio =
        closureArith.branchRatioFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace) :
    PositiveCollapseDefectStrictnessOutcome
      surface cut closureArith datum.collapseDefect := by
  refine
    { defectPositive := datum.collapseDefectPositive
      momentInequality := datum.singleInequality.strictMomentInequality
      defectPositive_iff_momentInequality := datum.defect_iff_moment
      balance := balance
      beta := beta
      determinantResidue := determinantResidue
      gamma := gamma
      branchRatio := branchRatio
      balance_exact := balance_exact
      beta_exact := beta_exact
      determinantResidue_exact := determinantResidue_exact
      gamma_exact := gamma_exact
      branchRatio_exact := branchRatio_exact
      exactScalarFaceReduction :=
        datum.singleInequality.certificates.exactScalarFaceReduction }

/-- The positive-collapse-defect strictness package keeps exactly the defect
criterion, the moment inequality, and the scalar-face readout carried by the
distinguished-cut data. -/
theorem defectPositiveSurface
    {Channel Horizon Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {cut : DistinguishedNondegenerateRankTwoTwoChannelCut surface arith}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : PositiveCollapseDefectExactStrictnessDatum surface cut closureArith)
    (balance beta determinantResidue gamma branchRatio : Scalar)
    (balance_exact :
      balance =
        closureArith.balanceFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (beta_exact :
      beta =
        closureArith.betaFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (determinantResidue_exact :
      determinantResidue =
        closureArith.determinantResidueFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (gamma_exact :
      gamma =
        closureArith.gammaFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (branchRatio_exact :
      branchRatio =
        closureArith.branchRatioFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace) :
    (strictnessOutcome datum
        balance beta determinantResidue gamma branchRatio
        balance_exact beta_exact determinantResidue_exact gamma_exact
        branchRatio_exact).defectPositive = datum.collapseDefectPositive := by
  rfl

theorem momentInequalitySurface
    {Channel Horizon Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {cut : DistinguishedNondegenerateRankTwoTwoChannelCut surface arith}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : PositiveCollapseDefectExactStrictnessDatum surface cut closureArith)
    (balance beta determinantResidue gamma branchRatio : Scalar)
    (balance_exact :
      balance =
        closureArith.balanceFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (beta_exact :
      beta =
        closureArith.betaFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (determinantResidue_exact :
      determinantResidue =
        closureArith.determinantResidueFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (gamma_exact :
      gamma =
        closureArith.gammaFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (branchRatio_exact :
      branchRatio =
        closureArith.branchRatioFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace) :
    (strictnessOutcome datum
        balance beta determinantResidue gamma branchRatio
        balance_exact beta_exact determinantResidue_exact gamma_exact
        branchRatio_exact).momentInequality =
          datum.singleInequality.strictMomentInequality := by
  rfl

/-- The positive-collapse-defect strictness package keeps exactly the defect
criterion, the moment inequality, and the scalar-face readout carried by the
distinguished-cut data. -/
theorem criterionReadoutSurface
    {Channel Horizon Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {cut : DistinguishedNondegenerateRankTwoTwoChannelCut surface arith}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : PositiveCollapseDefectExactStrictnessDatum surface cut closureArith)
    (balance beta determinantResidue gamma branchRatio : Scalar)
    (balance_exact :
      balance =
        closureArith.balanceFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (beta_exact :
      beta =
        closureArith.betaFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (determinantResidue_exact :
      determinantResidue =
        closureArith.determinantResidueFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (gamma_exact :
      gamma =
        closureArith.gammaFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (branchRatio_exact :
      branchRatio =
        closureArith.branchRatioFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace) :
    (strictnessOutcome datum
        balance beta determinantResidue gamma branchRatio
        balance_exact beta_exact determinantResidue_exact gamma_exact
        branchRatio_exact).defectPositive = datum.collapseDefectPositive ∧
    (strictnessOutcome datum
        balance beta determinantResidue gamma branchRatio
        balance_exact beta_exact determinantResidue_exact gamma_exact
        branchRatio_exact).momentInequality =
          datum.singleInequality.strictMomentInequality := by
  exact
    ⟨defectPositiveSurface datum
        balance beta determinantResidue gamma branchRatio
        balance_exact beta_exact determinantResidue_exact gamma_exact
        branchRatio_exact,
      momentInequalitySurface datum
        balance beta determinantResidue gamma branchRatio
        balance_exact beta_exact determinantResidue_exact gamma_exact
        branchRatio_exact⟩

/-- The same positive-collapse-defect strictness package also keeps the exact
scalar-face reduction clause carried by the distinguished-cut data. -/
theorem scalarFaceReductionSurface
    {Channel Horizon Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {cut : DistinguishedNondegenerateRankTwoTwoChannelCut surface arith}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : PositiveCollapseDefectExactStrictnessDatum surface cut closureArith)
    (balance beta determinantResidue gamma branchRatio : Scalar)
    (balance_exact :
      balance =
        closureArith.balanceFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (beta_exact :
      beta =
        closureArith.betaFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (determinantResidue_exact :
      determinantResidue =
        closureArith.determinantResidueFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (gamma_exact :
      gamma =
        closureArith.gammaFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (branchRatio_exact :
      branchRatio =
        closureArith.branchRatioFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace) :
    (strictnessOutcome datum
        balance beta determinantResidue gamma branchRatio
        balance_exact beta_exact determinantResidue_exact gamma_exact
        branchRatio_exact).exactScalarFaceReduction =
          datum.singleInequality.certificates.exactScalarFaceReduction := by
  rfl

/-- The positive-collapse-defect strictness package keeps exactly the defect
criterion, the moment inequality, and the scalar-face readout carried by the
distinguished-cut data. -/
theorem strictnessSurface
    {Channel Horizon Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {cut : DistinguishedNondegenerateRankTwoTwoChannelCut surface arith}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : PositiveCollapseDefectExactStrictnessDatum surface cut closureArith)
    (balance beta determinantResidue gamma branchRatio : Scalar)
    (balance_exact :
      balance =
        closureArith.balanceFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (beta_exact :
      beta =
        closureArith.betaFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (determinantResidue_exact :
      determinantResidue =
        closureArith.determinantResidueFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (gamma_exact :
      gamma =
        closureArith.gammaFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (branchRatio_exact :
      branchRatio =
        closureArith.branchRatioFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace) :
    (strictnessOutcome datum
        balance beta determinantResidue gamma branchRatio
        balance_exact beta_exact determinantResidue_exact gamma_exact
        branchRatio_exact).defectPositive = datum.collapseDefectPositive ∧
      (strictnessOutcome datum
        balance beta determinantResidue gamma branchRatio
        balance_exact beta_exact determinantResidue_exact gamma_exact
        branchRatio_exact).momentInequality =
          datum.singleInequality.strictMomentInequality ∧
      (strictnessOutcome datum
        balance beta determinantResidue gamma branchRatio
        balance_exact beta_exact determinantResidue_exact gamma_exact
        branchRatio_exact).exactScalarFaceReduction =
          datum.singleInequality.certificates.exactScalarFaceReduction := by
  have hcriterion := criterionReadoutSurface datum
    balance beta determinantResidue gamma branchRatio
    balance_exact beta_exact determinantResidue_exact gamma_exact branchRatio_exact
  have hscalar := scalarFaceReductionSurface datum
    balance beta determinantResidue gamma branchRatio
    balance_exact beta_exact determinantResidue_exact gamma_exact branchRatio_exact
  rcases hcriterion with ⟨hdefect, hmoment⟩
  exact ⟨hdefect, hmoment, hscalar⟩

/-- Once the local defect-recovery formulas are supplied, the
positive-collapse-defect datum already carries both the strictness readout and
the corresponding strictness object. -/
theorem strictnessWitnessSurface
    {Channel Horizon Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {cut : DistinguishedNondegenerateRankTwoTwoChannelCut surface arith}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : PositiveCollapseDefectExactStrictnessDatum surface cut closureArith)
    (balance beta determinantResidue gamma branchRatio : Scalar)
    (balance_exact :
      balance =
        closureArith.balanceFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (beta_exact :
      beta =
        closureArith.betaFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (determinantResidue_exact :
      determinantResidue =
        closureArith.determinantResidueFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (gamma_exact :
      gamma =
        closureArith.gammaFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (branchRatio_exact :
      branchRatio =
        closureArith.branchRatioFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace) :
    ((strictnessOutcome datum
        balance beta determinantResidue gamma branchRatio
        balance_exact beta_exact determinantResidue_exact gamma_exact
        branchRatio_exact).defectPositive = datum.collapseDefectPositive ∧
      (strictnessOutcome datum
        balance beta determinantResidue gamma branchRatio
        balance_exact beta_exact determinantResidue_exact gamma_exact
        branchRatio_exact).momentInequality =
          datum.singleInequality.strictMomentInequality ∧
      (strictnessOutcome datum
        balance beta determinantResidue gamma branchRatio
        balance_exact beta_exact determinantResidue_exact gamma_exact
        branchRatio_exact).exactScalarFaceReduction =
          datum.singleInequality.certificates.exactScalarFaceReduction) ∧
      Nonempty
        (PositiveCollapseDefectStrictnessOutcome
          surface cut closureArith datum.collapseDefect) := by
  exact
    ⟨strictnessSurface datum
        balance beta determinantResidue gamma branchRatio
        balance_exact beta_exact determinantResidue_exact gamma_exact
        branchRatio_exact,
      ⟨strictnessOutcome datum
          balance beta determinantResidue gamma branchRatio
          balance_exact beta_exact determinantResidue_exact gamma_exact
          branchRatio_exact⟩⟩

/-- Positive collapse defect is the exact strictness criterion once the local
defect-recovery formulas are supplied on the distinguished cut. -/
theorem strictnessOutcome_nonempty
    {Channel Horizon Scalar : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {cut : DistinguishedNondegenerateRankTwoTwoChannelCut surface arith}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : PositiveCollapseDefectExactStrictnessDatum surface cut closureArith)
    (balance beta determinantResidue gamma branchRatio : Scalar)
    (balance_exact :
      balance =
        closureArith.balanceFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (beta_exact :
      beta =
        closureArith.betaFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (determinantResidue_exact :
      determinantResidue =
        closureArith.determinantResidueFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (gamma_exact :
      gamma =
        closureArith.gammaFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace)
    (branchRatio_exact :
      branchRatio =
        closureArith.branchRatioFromCollapseDefectAndTrace
          datum.collapseDefect.value cut.distinguishedCompression.coordinates.trace) :
    Nonempty
      (PositiveCollapseDefectStrictnessOutcome
        surface cut closureArith datum.collapseDefect) := by
  exact
    (strictnessWitnessSurface datum
      balance beta determinantResidue gamma branchRatio
      balance_exact beta_exact determinantResidue_exact gamma_exact
      branchRatio_exact).2

end PositiveCollapseDefectExactStrictnessDatum

end CoherenceCalculus
