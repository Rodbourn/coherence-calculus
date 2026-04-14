import CoherenceCalculus.PartV.CoherentRankTwoCompressionCore
import CoherenceCalculus.PartV.DistinguishedCutClosureCore

/-!
# PartV.CoherentDistinguishedCutClosureCore

Coherent specialization of the detached Part V distinguished-cut closure
packages.

This file reuses the generic distinguished-cut surface on coherent local cuts:

- anchored strict-compiler consequences
- coherent distinguished-cut data
- coherent collapse-defect readout
- coherent inheritance of the generic closure route
-/

namespace CoherenceCalculus

/-- A canonically anchored determinant-positive coherent witness datum is a
coherent local witness surface together with the generic anchored distinguished
cut package on its two-channel specialization and a mode-aligned coherent cut. -/
structure CanonicallyAnchoredDeterminantPositiveCoherentWitnessDatum
    {Channel State Threshold Profile Scalar Horizon : Type}
    (interface : CoherentDirectReturnInterface Channel Scalar)
    (arith : RankTwoCompressionArithmetic Scalar)
    (closureArith : DistinguishedCutClosureArithmetic arith) where
  witness : CoherentLocalSchurWitnessDatum
    (Channel := Channel) (State := State) (Threshold := Threshold)
    (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface
  anchored :
    CanonicallyAnchoredDeterminantPositiveTwoChannelWitnessDatum
      (coherentToTwoChannelSchurCandidateSurface
        (Channel := Channel) (State := State) (Threshold := Threshold)
        (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
        witness.surface)
      arith closureArith
  modeAligned : ModeAlignedTwoChannelCoherentSchurCut witness.surface

namespace CanonicallyAnchoredDeterminantPositiveCoherentWitnessDatum

/-- The coherent strict-compiler output is exactly the generic anchored
strict-compiler package read on the coherent specialization. -/
def strictCompilerOutcome
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveCoherentWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface arith closureArith) :
    StrictTwoChannelCompilerOutcome
      closureArith datum.anchored.determinantResidue := by
  exact datum.anchored.strictCompilerOutcome

/-- The coherent strict-compiler output is just the generic anchored
strict-compiler output read on the coherent specialization. -/
theorem strictCompiler_nonempty
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveCoherentWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface arith closureArith) :
    Nonempty
      (StrictTwoChannelCompilerOutcome
        closureArith datum.anchored.determinantResidue) := by
  exact ⟨datum.strictCompilerOutcome⟩

/-- The coherent strict-compiler output keeps exactly the strictness and
scalar-face clauses already carried by the generic anchored witness datum. -/
theorem strictCutSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveCoherentWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface arith closureArith) :
    datum.strictCompilerOutcome.distinguishedCutStrict =
      datum.anchored.distinguishedCutStrict := by
  exact datum.anchored.strictCutSurface

theorem strictRegimeSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveCoherentWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface arith closureArith) :
    datum.strictCompilerOutcome.strictRegime = datum.anchored.strictRegime := by
  exact datum.anchored.strictRegimeSurface

/-- The coherent strict-compiler output keeps exactly the strictness and
scalar-face clauses already carried by the generic anchored witness datum. -/
theorem strictnessReadoutSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveCoherentWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface arith closureArith) :
    datum.strictCompilerOutcome.distinguishedCutStrict =
        datum.anchored.distinguishedCutStrict ∧
      datum.strictCompilerOutcome.strictRegime = datum.anchored.strictRegime := by
  exact ⟨datum.strictCutSurface, datum.strictRegimeSurface⟩

/-- The same coherent strict-compiler output also keeps the scalar-face readout
already carried by the anchored witness datum. -/
theorem branchRatioSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveCoherentWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface arith closureArith) :
    datum.strictCompilerOutcome.branchRatio = datum.anchored.branchRatio := by
  exact datum.anchored.branchRatioSurface

theorem exactScalarFaceSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveCoherentWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface arith closureArith) :
    datum.strictCompilerOutcome.exactScalarFaceReduction =
      datum.anchored.exactScalarFaceReduction := by
  exact datum.anchored.exactScalarFaceSurface

theorem strictTrichotomySurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveCoherentWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface arith closureArith) :
    datum.strictCompilerOutcome.coordinateIndependentTrichotomy =
      datum.anchored.coordinateIndependentTrichotomy := by
  exact datum.anchored.trichotomySurface

/-- The same coherent strict-compiler output also keeps the scalar-face readout
already carried by the anchored witness datum. -/
theorem scalarFaceReadoutSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveCoherentWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface arith closureArith) :
    datum.strictCompilerOutcome.branchRatio = datum.anchored.branchRatio ∧
      datum.strictCompilerOutcome.exactScalarFaceReduction =
        datum.anchored.exactScalarFaceReduction ∧
      datum.strictCompilerOutcome.coordinateIndependentTrichotomy =
        datum.anchored.coordinateIndependentTrichotomy := by
  exact
    ⟨datum.branchRatioSurface,
      datum.exactScalarFaceSurface,
      datum.strictTrichotomySurface⟩

/-- The coherent strict-compiler output keeps exactly the strictness and
scalar-face clauses already carried by the generic anchored witness datum. -/
theorem strictCompilerSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveCoherentWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface arith closureArith) :
    datum.strictCompilerOutcome.distinguishedCutStrict =
        datum.anchored.distinguishedCutStrict ∧
      datum.strictCompilerOutcome.strictRegime = datum.anchored.strictRegime ∧
      datum.strictCompilerOutcome.branchRatio = datum.anchored.branchRatio ∧
      datum.strictCompilerOutcome.exactScalarFaceReduction =
        datum.anchored.exactScalarFaceReduction ∧
      datum.strictCompilerOutcome.coordinateIndependentTrichotomy =
        datum.anchored.coordinateIndependentTrichotomy := by
  have hstrict := datum.strictnessReadoutSurface
  have hscalar := datum.scalarFaceReadoutSurface
  rcases hstrict with ⟨hcut, hregime⟩
  rcases hscalar with ⟨hratio, hface, htrichotomy⟩
  exact ⟨hcut, hregime, hratio, hface, htrichotomy⟩

/-- The coherent anchored witness already carries both the strict-compiler
readout and the corresponding coherent strict-compiler object. -/
theorem strictCompilerWitnessSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveCoherentWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface arith closureArith) :
    (datum.strictCompilerOutcome.distinguishedCutStrict =
        datum.anchored.distinguishedCutStrict ∧
      datum.strictCompilerOutcome.strictRegime = datum.anchored.strictRegime ∧
      datum.strictCompilerOutcome.branchRatio = datum.anchored.branchRatio ∧
      datum.strictCompilerOutcome.exactScalarFaceReduction =
        datum.anchored.exactScalarFaceReduction ∧
      datum.strictCompilerOutcome.coordinateIndependentTrichotomy =
        datum.anchored.coordinateIndependentTrichotomy) ∧
      Nonempty
        (StrictTwoChannelCompilerOutcome
          closureArith datum.anchored.determinantResidue) := by
  exact ⟨datum.strictCompilerSurface, datum.strictCompiler_nonempty⟩

/-- The coherent determinant-anchored corollary is exactly the generic
scalar-face corollary read on the coherent specialization. -/
def compilerCorollary
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveCoherentWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface arith closureArith) :
    DeterminantAnchoredStrictTwoChannelCompilerOutcome := by
  exact datum.anchored.compilerCorollary

/-- The determinant-anchored strict coherent compiler corollary is the same
scalar-face reduction package read on the coherent specialization. -/
theorem compilerCorollary_nonempty
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveCoherentWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface arith closureArith) :
    Nonempty DeterminantAnchoredStrictTwoChannelCompilerOutcome := by
  exact ⟨datum.compilerCorollary⟩

/-- The coherent determinant-anchored corollary keeps exactly the scalar-face
clauses already carried by the generic anchored witness datum. -/
theorem scalarReductionSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveCoherentWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface arith closureArith) :
    datum.compilerCorollary.exactScalarFaceReduction =
        datum.anchored.exactScalarFaceReduction := by
  exact datum.anchored.scalarReductionSurface

/-- The same coherent determinant-anchored corollary also keeps the
coordinate-free trichotomy clause carried by the anchored witness datum. -/
theorem trichotomySurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveCoherentWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface arith closureArith) :
    datum.compilerCorollary.coordinateIndependentTrichotomy =
        datum.anchored.coordinateIndependentTrichotomy := by
  exact datum.anchored.trichotomySurface

/-- The coherent determinant-anchored corollary keeps exactly the scalar-face
clauses already carried by the generic anchored witness datum. -/
theorem compilerCorollarySurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveCoherentWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface arith closureArith) :
    datum.compilerCorollary.exactScalarFaceReduction =
        datum.anchored.exactScalarFaceReduction ∧
    datum.compilerCorollary.coordinateIndependentTrichotomy =
        datum.anchored.coordinateIndependentTrichotomy := by
  exact ⟨datum.scalarReductionSurface, datum.trichotomySurface⟩

/-- The coherent anchored witness already carries both the determinant-anchored
corollary readout and the corresponding corollary object. -/
theorem compilerCorollaryWitnessSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : CanonicallyAnchoredDeterminantPositiveCoherentWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface arith closureArith) :
    (datum.compilerCorollary.exactScalarFaceReduction =
        datum.anchored.exactScalarFaceReduction ∧
      datum.compilerCorollary.coordinateIndependentTrichotomy =
        datum.anchored.coordinateIndependentTrichotomy) ∧
      Nonempty DeterminantAnchoredStrictTwoChannelCompilerOutcome := by
  exact ⟨datum.compilerCorollarySurface, ⟨datum.compilerCorollary⟩⟩

end CanonicallyAnchoredDeterminantPositiveCoherentWitnessDatum

/-- A distinguished nondegenerate mode-aligned coherent cut is the coherent
specialization of the generic distinguished cut package, together with an
explicit mode-aligned coherent witness on that same cut. -/
structure DistinguishedNondegenerateModeAlignedCoherentCut
    {Channel State Threshold Profile Scalar Horizon : Type}
    (interface : CoherentDirectReturnInterface Channel Scalar)
    (arith : RankTwoCompressionArithmetic Scalar) where
  witness : CoherentLocalSchurWitnessDatum
    (Channel := Channel) (State := State) (Threshold := Threshold)
    (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface
  distinguished :
    DistinguishedNondegenerateRankTwoTwoChannelCut
      (coherentToTwoChannelSchurCandidateSurface
        (Channel := Channel) (State := State) (Threshold := Threshold)
        (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
        witness.surface) arith
  modeAligned : ModeAlignedTwoChannelCoherentSchurCut witness.surface

namespace DistinguishedNondegenerateModeAlignedCoherentCut

/-- The coherent collapse defect is exactly the generic collapse defect read on
the coherent specialization of the distinguished local cut. -/
def collapseDefect
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    (datum : DistinguishedNondegenerateModeAlignedCoherentCut
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface arith) :
    OneChannelCollapseDefectOnTwoChannelSchurCut
      (coherentToTwoChannelSchurCandidateSurface
        (Channel := Channel) (State := State) (Threshold := Threshold)
        (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
        datum.witness.surface)
      datum.distinguished.distinguishedCompression closureArith := by
  refine
    { value :=
        closureArith.collapseDefectFromMoments
          datum.distinguished.distinguishedCompression.coordinates.momentOne
          datum.distinguished.distinguishedCompression.coordinates.momentTwo
      value_exact := rfl }

end DistinguishedNondegenerateModeAlignedCoherentCut

/-- The entire distinguished-cut closure route on the coherent surface is just
the generic closure package read on the coherent specialization. -/
structure CoherentDistinguishedCutClosureRoute
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (closureArith : DistinguishedCutClosureArithmetic arith)
    (datum : DistinguishedNondegenerateModeAlignedCoherentCut
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface arith) where
  certificates :
    DistinguishedCutClosureCertificatePackage
      (coherentToTwoChannelSchurCandidateSurface
        (Channel := Channel) (State := State) (Threshold := Threshold)
        (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
        datum.witness.surface)
      datum.distinguished closureArith
  singleInequality :
    SingleInequalityClosureCriterionDatum
      (coherentToTwoChannelSchurCandidateSurface
        (Channel := Channel) (State := State) (Threshold := Threshold)
        (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
        datum.witness.surface)
      datum.distinguished closureArith
  positiveCollapseDefect :
    PositiveCollapseDefectExactStrictnessDatum
      (coherentToTwoChannelSchurCandidateSurface
        (Channel := Channel) (State := State) (Threshold := Threshold)
        (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
        datum.witness.surface)
      datum.distinguished closureArith

namespace CoherentDistinguishedCutClosureRoute

/-- The coherent distinguished-cut route carries the same leading strictness
criteria as the generic certificate and single-inequality packages. -/
theorem strictnessSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    {datum : DistinguishedNondegenerateModeAlignedCoherentCut
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface arith}
    (route : CoherentDistinguishedCutClosureRoute
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      closureArith datum) :
    (route.certificates.strictWitness ↔ route.certificates.betaStrict) ∧
      (route.singleInequality.strictMomentInequality ↔
        route.singleInequality.certificates.betaStrict) := by
  exact
    ⟨route.certificates.strictCriterionSurface,
      route.singleInequality.strictMomentInequality_iff_betaStrict⟩

/-- The coherent frontier readout keeps the strict-regime and scalar-face
clauses already fixed by the certificate package. -/
theorem frontierSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    {datum : DistinguishedNondegenerateModeAlignedCoherentCut
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface arith}
    (route : CoherentDistinguishedCutClosureRoute
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      closureArith datum) :
    route.singleInequality.frontierOutcome.strictRegime =
        route.singleInequality.certificates.strictRegime ∧
      route.singleInequality.frontierOutcome.exactScalarFaceReduction =
        route.singleInequality.certificates.exactScalarFaceReduction := by
  exact
    ⟨route.singleInequality.strictRegimeSurface,
      route.singleInequality.scalarReductionSurface⟩

/-- The coherent positive-collapse package identifies collapse-defect
strictness exactly with the single-inequality criterion. -/
theorem collapseDefectCriterion
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    {datum : DistinguishedNondegenerateModeAlignedCoherentCut
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface arith}
    (route : CoherentDistinguishedCutClosureRoute
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      closureArith datum) :
    route.positiveCollapseDefect.collapseDefectPositive ↔
      route.positiveCollapseDefect.singleInequality.strictMomentInequality := by
  exact route.positiveCollapseDefect.strictnessCriterion

/-- The coherent distinguished-cut closure route already carries the same
strictness ladder and frontier readout as the generic route on that cut. -/
theorem closureSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    {datum : DistinguishedNondegenerateModeAlignedCoherentCut
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface arith}
    (route : CoherentDistinguishedCutClosureRoute
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      closureArith datum) :
    (route.certificates.strictWitness ↔ route.certificates.betaStrict) ∧
      (route.singleInequality.strictMomentInequality ↔
        route.singleInequality.certificates.betaStrict) ∧
      (route.singleInequality.frontierOutcome.strictRegime =
        route.singleInequality.certificates.strictRegime) ∧
      (route.singleInequality.frontierOutcome.exactScalarFaceReduction =
        route.singleInequality.certificates.exactScalarFaceReduction) ∧
      (route.positiveCollapseDefect.collapseDefectPositive ↔
        route.positiveCollapseDefect.singleInequality.strictMomentInequality) := by
  exact
    ⟨route.strictnessSurface.1,
      route.strictnessSurface.2,
      route.frontierSurface.1,
      route.frontierSurface.2,
      route.collapseDefectCriterion⟩

/-- The coherent distinguished-cut route already carries both the full closure
readout surface and the coherent route object itself. -/
theorem closureWitnessSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    {datum : DistinguishedNondegenerateModeAlignedCoherentCut
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface arith}
    (route : CoherentDistinguishedCutClosureRoute
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      closureArith datum) :
    ((route.certificates.strictWitness ↔ route.certificates.betaStrict) ∧
      (route.singleInequality.strictMomentInequality ↔
        route.singleInequality.certificates.betaStrict) ∧
      (route.singleInequality.frontierOutcome.strictRegime =
        route.singleInequality.certificates.strictRegime) ∧
      (route.singleInequality.frontierOutcome.exactScalarFaceReduction =
        route.singleInequality.certificates.exactScalarFaceReduction) ∧
      (route.positiveCollapseDefect.collapseDefectPositive ↔
        route.positiveCollapseDefect.singleInequality.strictMomentInequality)) ∧
      Nonempty
        (CoherentDistinguishedCutClosureRoute
          (Channel := Channel) (State := State) (Threshold := Threshold)
          (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
          closureArith datum) := by
  exact ⟨route.closureSurface, ⟨route⟩⟩

/-- Once the coherent distinguished cut is supplied, the whole generic closure
route is inherited on that same coherent surface. -/
theorem nonempty
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    {closureArith : DistinguishedCutClosureArithmetic arith}
    {datum : DistinguishedNondegenerateModeAlignedCoherentCut
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface arith}
    (route : CoherentDistinguishedCutClosureRoute
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      closureArith datum) :
    Nonempty
      (CoherentDistinguishedCutClosureRoute
        (Channel := Channel) (State := State) (Threshold := Threshold)
        (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
        closureArith datum) := by
  exact route.closureWitnessSurface.2

end CoherentDistinguishedCutClosureRoute

end CoherenceCalculus
