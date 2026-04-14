import CoherenceCalculus.PartV.CoherentLocalSchurCore
import CoherenceCalculus.PartV.RankTwoCompressionCore

namespace CoherenceCalculus

/-- Forget only the coherent-only witness presentation and keep the underlying
generic local rank-two source. -/
def coherentLocalRankTwoSourceToLocalRankTwoSource
    {Channel State Threshold Profile Scalar Horizon : Type}
    {surface : CoherentSchurCandidateSurface
      Channel State Threshold Profile Scalar Horizon}
    (source : CoherentLocalRankTwoSource surface) :
    LocalRankTwoSource (coherentToTwoChannelSchurCandidateSurface surface) := by
  cases source with
  | symmetry gate =>
      exact LocalRankTwoSource.symmetry gate.genericGate
  | modeAligned cut =>
      exact LocalRankTwoSource.mode cut.genericGate

/-- The coherent rank-two compression package is the generic compression package
read on the coherent specialization of the local cut. -/
def coherentRankTwoSchurCompressionDatum
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface)
    (coordinates : RankTwoSchurCompressionCoordinates arith) :
    RankTwoSchurCompressionDatum
      (coherentToTwoChannelSchurCandidateSurface datum.surface) arith := by
  exact
    rankTwoSchurCompressionDatumOfSource
      (coherentLocalRankTwoSourceToLocalRankTwoSource datum.source)
      coordinates

/-- The coherent rank-two compression theorem is the coherent specialization of
the generic two-channel compression package. -/
theorem rank_two_schur_compression_coherent
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface)
    (coordinates : RankTwoSchurCompressionCoordinates arith) :
    Nonempty
      (RankTwoSchurCompressionDatum
        (coherentToTwoChannelSchurCandidateSurface datum.surface) arith) := by
  exact ⟨coherentRankTwoSchurCompressionDatum datum coordinates⟩

/-- On the coherent specialization, the rank-two compression object keeps the
same support witness and coordinates as the generic compression datum it
reuses. -/
theorem coherentRankTwoSupportSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface)
    (coordinates : RankTwoSchurCompressionCoordinates arith) :
    (coherentRankTwoSchurCompressionDatum datum coordinates).rankTwoSupport =
        (coherentLocalRankTwoSourceToLocalRankTwoSource datum.source).rankTwoSupport := by
  exact
    rankTwoSupportSurface
      (source := coherentLocalRankTwoSourceToLocalRankTwoSource datum.source)
      (coordinates := coordinates)

/-- The same coherent compression object also keeps exactly the chosen
coordinate readout. -/
theorem coherentCoordinateReadoutSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface)
    (coordinates : RankTwoSchurCompressionCoordinates arith) :
    (coherentRankTwoSchurCompressionDatum datum coordinates).coordinates =
        coordinates := by
  exact
    coordinateReadoutSurface
      (source := coherentLocalRankTwoSourceToLocalRankTwoSource datum.source)
      (coordinates := coordinates)

/-- On the coherent specialization, the rank-two compression object keeps the
same support witness and coordinates as the generic compression datum it
reuses. -/
theorem coherentRankTwoCompressionSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface)
    (coordinates : RankTwoSchurCompressionCoordinates arith) :
    (coherentRankTwoSchurCompressionDatum datum coordinates).rankTwoSupport =
        (coherentLocalRankTwoSourceToLocalRankTwoSource datum.source).rankTwoSupport ∧
      (coherentRankTwoSchurCompressionDatum datum coordinates).coordinates =
        coordinates := by
  exact
    ⟨coherentRankTwoSupportSurface datum coordinates,
      coherentCoordinateReadoutSurface datum coordinates⟩

/-- On the coherent specialization, the compression layer already carries both
the exact support/coordinate readout and the corresponding compression object.
-/
theorem coherentRankTwoCompressionWitnessSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface)
    (coordinates : RankTwoSchurCompressionCoordinates arith) :
    ((coherentRankTwoSchurCompressionDatum datum coordinates).rankTwoSupport =
        (coherentLocalRankTwoSourceToLocalRankTwoSource datum.source).rankTwoSupport ∧
      (coherentRankTwoSchurCompressionDatum datum coordinates).coordinates =
        coordinates) ∧
      Nonempty
        (RankTwoSchurCompressionDatum
          (coherentToTwoChannelSchurCandidateSurface datum.surface) arith) := by
  exact
    ⟨coherentRankTwoCompressionSurface datum coordinates,
      ⟨coherentRankTwoSchurCompressionDatum datum coordinates⟩⟩

/-- The coherent balance-ratio package is exactly the generic balance-ratio
package read on the coherent rank-two compression datum. -/
def coherentNormalizedTwoChannelSchurBalanceRatioDatum
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface)
    (coordinates : RankTwoSchurCompressionCoordinates arith) :
    NormalizedTwoChannelSchurBalanceRatioDatum
      (coherentToTwoChannelSchurCandidateSurface datum.surface) arith := by
  exact
    normalizedTwoChannelSchurBalanceRatioDatumOfCompression
      (coherentRankTwoSchurCompressionDatum datum coordinates)

/-- The coherent normalized balance-ratio corollary is the coherent
specialization of the generic balance-ratio package. -/
theorem normalized_two_channel_schur_balance_ratio
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface)
    (coordinates : RankTwoSchurCompressionCoordinates arith) :
    Nonempty
      (NormalizedTwoChannelSchurBalanceRatioDatum
        (coherentToTwoChannelSchurCandidateSurface datum.surface) arith) := by
  exact ⟨coherentNormalizedTwoChannelSchurBalanceRatioDatum datum coordinates⟩

/-- The coherent balance-ratio package keeps exactly the coherent compression
datum and its induced beta-coordinate readout. -/
theorem coherentCompressionReadoutSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface)
    (coordinates : RankTwoSchurCompressionCoordinates arith) :
    (coherentNormalizedTwoChannelSchurBalanceRatioDatum datum coordinates).compression =
        coherentRankTwoSchurCompressionDatum datum coordinates := by
  exact
    compressionReadoutSurface
      (compression := coherentRankTwoSchurCompressionDatum datum coordinates)

/-- The same coherent normalized package also keeps exactly the induced
`beta`-coordinate readout. -/
theorem coherentBetaCoordinateSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface)
    (coordinates : RankTwoSchurCompressionCoordinates arith) :
    (coherentNormalizedTwoChannelSchurBalanceRatioDatum datum coordinates).balanceRatio =
        coordinates.beta := by
  exact
    betaCoordinateSurface
      (compression := coherentRankTwoSchurCompressionDatum datum coordinates)

/-- The coherent balance-ratio package keeps exactly the coherent compression
datum and its induced beta-coordinate readout. -/
theorem coherentNormalizedBalanceRatioSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface)
    (coordinates : RankTwoSchurCompressionCoordinates arith) :
    (coherentNormalizedTwoChannelSchurBalanceRatioDatum datum coordinates).compression =
        coherentRankTwoSchurCompressionDatum datum coordinates ∧
      (coherentNormalizedTwoChannelSchurBalanceRatioDatum datum coordinates).balanceRatio =
        coordinates.beta := by
  exact
    ⟨coherentCompressionReadoutSurface datum coordinates,
      coherentBetaCoordinateSurface datum coordinates⟩

/-- On the coherent specialization, the normalized balance-ratio layer already
keeps both its beta-readout surface and the corresponding normalized-ratio
object. -/
theorem coherentNormalizedBalanceRatioWitnessSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (datum : CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface)
    (coordinates : RankTwoSchurCompressionCoordinates arith) :
    ((coherentNormalizedTwoChannelSchurBalanceRatioDatum datum coordinates).compression =
        coherentRankTwoSchurCompressionDatum datum coordinates ∧
      (coherentNormalizedTwoChannelSchurBalanceRatioDatum datum coordinates).balanceRatio =
        coordinates.beta) ∧
      Nonempty
        (NormalizedTwoChannelSchurBalanceRatioDatum
          (coherentToTwoChannelSchurCandidateSurface datum.surface) arith) := by
  exact
    ⟨coherentNormalizedBalanceRatioSurface datum coordinates,
      ⟨coherentNormalizedTwoChannelSchurBalanceRatioDatum datum coordinates⟩⟩

end CoherenceCalculus
