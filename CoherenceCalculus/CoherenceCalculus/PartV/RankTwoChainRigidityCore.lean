import CoherenceCalculus.PartV.RankTwoCompressionCore

namespace CoherenceCalculus

/-- A chainwise rank-two rigidity datum packages a family of local rank-two
compression data that all share the same normalized balance ratio. -/
structure ChainwiseRankTwoRigidityDatum
    {Channel Horizon Scalar : Type}
    (Cut : Type)
    (surface : Cut → TwoChannelSchurCandidateSurface Channel Horizon Scalar)
    (arith : RankTwoCompressionArithmetic Scalar) where
  compression : ∀ cut : Cut, RankTwoSchurCompressionDatum (surface cut) arith
  commonBalanceRatio : Scalar
  beta_exact :
    ∀ cut : Cut, (compression cut).coordinates.beta = commonBalanceRatio

/-- The surviving chainwise scale-free candidate surface is determined entirely
by the common balance ratio and the corresponding normalized local coordinates. -/
structure ChainwiseRankTwoCandidateSurface
    {Channel Horizon Scalar : Type}
    (Cut : Type)
    (surface : Cut → TwoChannelSchurCandidateSurface Channel Horizon Scalar)
    (arith : RankTwoCompressionArithmetic Scalar) where
  commonBalanceRatio : Scalar
  balanceAt : Cut → Scalar
  rootPlusAt : Cut → Scalar
  rootMinusAt : Cut → Scalar
  balance_exact :
    ∀ cut : Cut, balanceAt cut = arith.balanceFromBeta commonBalanceRatio
  rootPlus_exact :
    ∀ cut : Cut, rootPlusAt cut = arith.rootPlusFromBeta commonBalanceRatio
  rootMinus_exact :
    ∀ cut : Cut, rootMinusAt cut = arith.rootMinusFromBeta commonBalanceRatio

/-- A chain of local rank-two cuts with common balance ratio collapses to one
shared scale-free scalar together with the corresponding normalized roots. -/
def chainwiseRankTwoCandidateSurfaceOfDatum
    {Channel Horizon Scalar : Type}
    {Cut : Type}
    {surface : Cut → TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (datum : ChainwiseRankTwoRigidityDatum Cut surface arith) :
    ChainwiseRankTwoCandidateSurface Cut surface arith := by
  refine
    { commonBalanceRatio := datum.commonBalanceRatio
      balanceAt := fun cut => (datum.compression cut).coordinates.balance
      rootPlusAt := fun cut => (datum.compression cut).coordinates.rootPlus
      rootMinusAt := fun cut => (datum.compression cut).coordinates.rootMinus
      balance_exact := ?_
      rootPlus_exact := ?_
      rootMinus_exact := ?_ }
  · intro cut
    rw [(datum.compression cut).coordinates.balance_beta_exact, datum.beta_exact cut]
  · intro cut
    rw [(datum.compression cut).coordinates.rootPlus_exact, datum.beta_exact cut]
  · intro cut
    rw [(datum.compression cut).coordinates.rootMinus_exact, datum.beta_exact cut]

/-- The chainwise rank-two rigidity corollary packages the surviving scale-free
surface once the balance ratio is constant along the chain. -/
theorem chainwise_rank_two_rigidity_two_channel
    {Channel Horizon Scalar : Type}
    {Cut : Type}
    {surface : Cut → TwoChannelSchurCandidateSurface Channel Horizon Scalar}
    {arith : RankTwoCompressionArithmetic Scalar}
    (datum : ChainwiseRankTwoRigidityDatum Cut surface arith) :
    Nonempty (ChainwiseRankTwoCandidateSurface Cut surface arith) := by
  exact ⟨chainwiseRankTwoCandidateSurfaceOfDatum datum⟩

end CoherenceCalculus
