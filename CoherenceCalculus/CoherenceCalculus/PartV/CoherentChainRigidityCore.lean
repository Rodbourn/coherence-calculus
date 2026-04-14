import CoherenceCalculus.PartV.CoherentRankTwoCompressionCore
import CoherenceCalculus.PartV.RankTwoChainRigidityCore

namespace CoherenceCalculus

/-- A coherent chain rigidity datum is a family of coherent local witness
surfaces whose rank-two compression data share a common normalized ratio. -/
structure CoherentRatioRigidTwoChannelSchurChainDatum
    {Channel State Threshold Profile Scalar Horizon : Type}
    (interface : CoherentDirectReturnInterface Channel Scalar)
    (Cut : Type)
    (arith : RankTwoCompressionArithmetic Scalar) where
  witness : Cut →
    CoherentLocalSchurWitnessDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon) interface
  compression :
    ∀ cut : Cut,
      RankTwoSchurCompressionDatum
        (coherentToTwoChannelSchurCandidateSurface (witness cut).surface) arith
  commonBalanceRatio : Scalar
  beta_exact :
    ∀ cut : Cut, (compression cut).coordinates.beta = commonBalanceRatio

/-- Forgetting the coherent presentation yields exactly the generic chainwise
rank-two rigidity datum on the coherent specialization. -/
def coherentRatioRigidTwoChannelSchurChainDatumToGeneric
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {Cut : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    (datum : CoherentRatioRigidTwoChannelSchurChainDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface Cut arith) :
    ChainwiseRankTwoRigidityDatum
      Cut
      (fun cut =>
        coherentToTwoChannelSchurCandidateSurface (datum.witness cut).surface)
      arith := by
  refine
    { compression := datum.compression
      commonBalanceRatio := datum.commonBalanceRatio
      beta_exact := datum.beta_exact }

/-- Ratio-rigid coherent Schur chains are therefore scalar-rigid by direct
reuse of the generic chainwise rank-two rigidity package. -/
def coherentChainwiseRankTwoCandidateSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {Cut : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    (datum : CoherentRatioRigidTwoChannelSchurChainDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface Cut arith) :
    ChainwiseRankTwoCandidateSurface
      Cut
      (fun cut =>
        coherentToTwoChannelSchurCandidateSurface (datum.witness cut).surface)
      arith := by
  exact
    chainwiseRankTwoCandidateSurfaceOfDatum
      (coherentRatioRigidTwoChannelSchurChainDatumToGeneric datum)

/-- The coherent chainwise candidate surface keeps exactly the common
balance-ratio and local normalized coordinates already carried by the coherent
compression family. -/
theorem coherentChainwiseRankTwoCandidateSurface_readout
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {Cut : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    (datum : CoherentRatioRigidTwoChannelSchurChainDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface Cut arith) :
    (coherentChainwiseRankTwoCandidateSurface datum).commonBalanceRatio =
        datum.commonBalanceRatio ∧
      (∀ cut, (coherentChainwiseRankTwoCandidateSurface datum).balanceAt cut =
        (datum.compression cut).coordinates.balance) ∧
      (∀ cut, (coherentChainwiseRankTwoCandidateSurface datum).rootPlusAt cut =
        (datum.compression cut).coordinates.rootPlus) ∧
      (∀ cut, (coherentChainwiseRankTwoCandidateSurface datum).rootMinusAt cut =
        (datum.compression cut).coordinates.rootMinus) := by
  exact ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The coherent chainwise candidate package already carries both the
chain-rigidity readout surface and the corresponding candidate object. -/
theorem coherentChainwiseRankTwoCandidateWitnessSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {Cut : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    (datum : CoherentRatioRigidTwoChannelSchurChainDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface Cut arith) :
    ((coherentChainwiseRankTwoCandidateSurface datum).commonBalanceRatio =
        datum.commonBalanceRatio ∧
      (∀ cut, (coherentChainwiseRankTwoCandidateSurface datum).balanceAt cut =
        (datum.compression cut).coordinates.balance) ∧
      (∀ cut, (coherentChainwiseRankTwoCandidateSurface datum).rootPlusAt cut =
        (datum.compression cut).coordinates.rootPlus) ∧
      (∀ cut, (coherentChainwiseRankTwoCandidateSurface datum).rootMinusAt cut =
        (datum.compression cut).coordinates.rootMinus)) ∧
      Nonempty
        (ChainwiseRankTwoCandidateSurface
          Cut
          (fun cut =>
            coherentToTwoChannelSchurCandidateSurface (datum.witness cut).surface)
          arith) := by
  exact
    ⟨coherentChainwiseRankTwoCandidateSurface_readout datum,
      ⟨coherentChainwiseRankTwoCandidateSurface datum⟩⟩

/-- Ratio-rigid coherent Schur chains are therefore scalar-rigid by direct
reuse of the generic chainwise rank-two rigidity package. -/
theorem ratio_rigid_two_channel_coherent_schur_chains_are_scalar_rigid
    {Channel State Threshold Profile Scalar Horizon : Type}
    {interface : CoherentDirectReturnInterface Channel Scalar}
    {Cut : Type}
    {arith : RankTwoCompressionArithmetic Scalar}
    (datum : CoherentRatioRigidTwoChannelSchurChainDatum
      (Channel := Channel) (State := State) (Threshold := Threshold)
      (Profile := Profile) (Scalar := Scalar) (Horizon := Horizon)
      interface Cut arith) :
    Nonempty
      (ChainwiseRankTwoCandidateSurface
        Cut
        (fun cut =>
          coherentToTwoChannelSchurCandidateSurface (datum.witness cut).surface)
        arith) := by
  exact (coherentChainwiseRankTwoCandidateWitnessSurface datum).2

end CoherenceCalculus
