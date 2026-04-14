import CoherenceCalculus.PartV.LocalSchurWitnessCore

namespace CoherenceCalculus

/-- The local rank-two compression layer is parameterized by the exact scalar
coordinate formulas that a branch chooses to read on its certified local cut. -/
structure RankTwoCompressionArithmetic (Scalar : Type) where
  determinantFromMoments : Scalar → Scalar → Scalar
  balanceFromTraceDeterminant : Scalar → Scalar → Scalar
  betaFromMoments : Scalar → Scalar → Scalar
  balanceFromBeta : Scalar → Scalar
  rootPlusFromBeta : Scalar → Scalar
  rootMinusFromBeta : Scalar → Scalar

/-- The explicit scalar coordinates carried by a rank-two local Schur cut. -/
structure RankTwoSchurCompressionCoordinates
    {Scalar : Type} (arith : RankTwoCompressionArithmetic Scalar) where
  momentOne : Scalar
  momentTwo : Scalar
  trace : Scalar
  determinant : Scalar
  balance : Scalar
  beta : Scalar
  rootPlus : Scalar
  rootMinus : Scalar
  trace_exact : trace = momentOne
  determinant_exact : determinant = arith.determinantFromMoments momentOne momentTwo
  balance_trace_det_exact : balance = arith.balanceFromTraceDeterminant trace determinant
  beta_exact : beta = arith.betaFromMoments momentOne momentTwo
  balance_beta_exact : balance = arith.balanceFromBeta beta
  rootPlus_exact : rootPlus = arith.rootPlusFromBeta beta
  rootMinus_exact : rootMinus = arith.rootMinusFromBeta beta

/-- The full generic rank-two compression package is the local rank-two support
certificate together with the exact scalar coordinates read on that cut. -/
structure RankTwoSchurCompressionDatum
    {Channel Horizon Scalar : Type}
    (surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar)
    (arith : RankTwoCompressionArithmetic Scalar) where
  rankTwoSupport : RankTwoTwoChannelSchurSupport surface
  coordinates : RankTwoSchurCompressionCoordinates arith

/-- Build the generic rank-two compression package from a certified local
rank-two source and explicit local compression coordinates. -/
def rankTwoSchurCompressionDatumOfSource
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (source : LocalRankTwoSource surface)
    (coordinates : RankTwoSchurCompressionCoordinates arith) :
    RankTwoSchurCompressionDatum surface arith := by
  refine
    { rankTwoSupport := source.rankTwoSupport
      coordinates := coordinates }

/-- The generic rank-two compression package is exactly the local rank-two
support together with the chosen coordinate readout on that cut. -/
theorem rankTwoSupportSurface
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (source : LocalRankTwoSource surface)
    (coordinates : RankTwoSchurCompressionCoordinates arith) :
    (rankTwoSchurCompressionDatumOfSource source coordinates).rankTwoSupport =
        source.rankTwoSupport := by
  rfl

/-- The same compression package also keeps exactly the chosen coordinate
readout on that cut. -/
theorem coordinateReadoutSurface
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (source : LocalRankTwoSource surface)
    (coordinates : RankTwoSchurCompressionCoordinates arith) :
    (rankTwoSchurCompressionDatumOfSource source coordinates).coordinates =
        coordinates := by
  rfl

/-- The generic rank-two compression package is exactly the local rank-two
support together with the chosen coordinate readout on that cut. -/
theorem rankTwoCompressionSurface
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (source : LocalRankTwoSource surface)
    (coordinates : RankTwoSchurCompressionCoordinates arith) :
    (rankTwoSchurCompressionDatumOfSource source coordinates).rankTwoSupport =
        source.rankTwoSupport ∧
    (rankTwoSchurCompressionDatumOfSource source coordinates).coordinates =
        coordinates := by
  exact ⟨rankTwoSupportSurface source coordinates, coordinateReadoutSurface source coordinates⟩

/-- A certified local rank-two source already carries both the exact
compression readout surface and the corresponding compression object. -/
theorem rankTwoCompressionWitnessSurface
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (source : LocalRankTwoSource surface)
    (coordinates : RankTwoSchurCompressionCoordinates arith) :
    ((rankTwoSchurCompressionDatumOfSource source coordinates).rankTwoSupport =
        source.rankTwoSupport ∧
      (rankTwoSchurCompressionDatumOfSource source coordinates).coordinates =
        coordinates) ∧
      Nonempty (RankTwoSchurCompressionDatum surface arith) := by
  exact
    ⟨rankTwoCompressionSurface source coordinates,
      ⟨rankTwoSchurCompressionDatumOfSource source coordinates⟩⟩

/-- A certified local rank-two source therefore suffices to package the exact
rank-two Schur compression data on that same two-channel cut. -/
theorem rank_two_schur_compression_two_channel
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (source : LocalRankTwoSource surface)
    (coordinates : RankTwoSchurCompressionCoordinates arith) :
    Nonempty (RankTwoSchurCompressionDatum surface arith) := by
  exact (rankTwoCompressionWitnessSurface source coordinates).2

/-- The normalized balance-ratio package is only a restatement of the same
rank-two compression data in the single scale-free `beta` coordinate. -/
structure NormalizedTwoChannelSchurBalanceRatioDatum
    {Channel Horizon Scalar : Type}
    (surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar)
    (arith : RankTwoCompressionArithmetic Scalar) where
  compression : RankTwoSchurCompressionDatum surface arith
  balanceRatio : Scalar
  balanceRatio_exact : balanceRatio = compression.coordinates.beta
  normalizedBalance_exact :
    compression.coordinates.balance = arith.balanceFromBeta balanceRatio
  rootPlus_exact :
    compression.coordinates.rootPlus = arith.rootPlusFromBeta balanceRatio
  rootMinus_exact :
    compression.coordinates.rootMinus = arith.rootMinusFromBeta balanceRatio

/-- The balance-ratio package is read directly from the generic rank-two
compression datum. -/
def normalizedTwoChannelSchurBalanceRatioDatumOfCompression
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (compression : RankTwoSchurCompressionDatum surface arith) :
    NormalizedTwoChannelSchurBalanceRatioDatum surface arith := by
  refine
    { compression := compression
      balanceRatio := compression.coordinates.beta
      balanceRatio_exact := rfl
      normalizedBalance_exact := by
        simpa using compression.coordinates.balance_beta_exact
      rootPlus_exact := by
        simpa using compression.coordinates.rootPlus_exact
      rootMinus_exact := by
        simpa using compression.coordinates.rootMinus_exact }

/-- The normalized balance-ratio package is exactly the same compression datum
read through its single `beta` coordinate. -/
theorem compressionReadoutSurface
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (compression : RankTwoSchurCompressionDatum surface arith) :
    (normalizedTwoChannelSchurBalanceRatioDatumOfCompression compression).compression =
        compression := by
  rfl

/-- The same normalized package also keeps exactly the induced `beta`
coordinate read from that compression datum. -/
theorem betaCoordinateSurface
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (compression : RankTwoSchurCompressionDatum surface arith) :
    (normalizedTwoChannelSchurBalanceRatioDatumOfCompression compression).balanceRatio =
        compression.coordinates.beta := by
  rfl

/-- The normalized balance-ratio package is exactly the same compression datum
read through its single `beta` coordinate. -/
theorem normalizedBalanceRatioSurface
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (compression : RankTwoSchurCompressionDatum surface arith) :
    (normalizedTwoChannelSchurBalanceRatioDatumOfCompression compression).compression =
        compression ∧
    (normalizedTwoChannelSchurBalanceRatioDatumOfCompression compression).balanceRatio =
        compression.coordinates.beta := by
  exact ⟨compressionReadoutSurface compression, betaCoordinateSurface compression⟩

/-- The normalized balance-ratio package already carries both its beta-readout
surface and the corresponding normalized-ratio object. -/
theorem normalizedBalanceRatioWitnessSurface
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (compression : RankTwoSchurCompressionDatum surface arith) :
    ((normalizedTwoChannelSchurBalanceRatioDatumOfCompression compression).compression =
        compression ∧
      (normalizedTwoChannelSchurBalanceRatioDatumOfCompression compression).balanceRatio =
        compression.coordinates.beta) ∧
      Nonempty (NormalizedTwoChannelSchurBalanceRatioDatum surface arith) := by
  exact
    ⟨normalizedBalanceRatioSurface compression,
      ⟨normalizedTwoChannelSchurBalanceRatioDatumOfCompression compression⟩⟩

/-- On the generic rank-two surface, the balance-ratio corollary is just the
single-coordinate restatement of the same compression package. -/
theorem normalized_two_channel_schur_balance_ratio_generic
    {Channel Horizon Scalar : Type}
    {surface : TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (compression : RankTwoSchurCompressionDatum surface arith) :
    Nonempty (NormalizedTwoChannelSchurBalanceRatioDatum surface arith) := by
  exact (normalizedBalanceRatioWitnessSurface compression).2

end CoherenceCalculus
