import CoherenceCalculusMathlibBridge.HilbertOrthogonalityValidation
import Mathlib.Analysis.InnerProductSpace.Positive

namespace CoherenceCalculusMathlibBridge

open CoherenceCalculus

/--
Validated Hilbert consumer slice for positivity/order on the concrete
`U.starProjection` recovery model.
-/
theorem subspaceProjectionRecovery_operator_isPositive
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    ((subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U).operator).IsPositive := by
  simpa [subspaceProjectionRecovery_operator_eq] using
    (ContinuousLinearMap.IsPositive.of_isStarProjection
      (subspaceProjection_operator_isStarProjection (𝕜 := 𝕜) (E := E) U))

theorem subspaceProjectionRecovery_operator_nonneg
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    0 ≤ (subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U).operator := by
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).2
    (subspaceProjectionRecovery_operator_isPositive (𝕜 := 𝕜) (E := E) cutoff U)

theorem subspaceProjectionRecovery_operator_complement_nonneg
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    0 ≤ ContinuousLinearMap.id 𝕜 E -
      (subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U).operator := by
  have hPos : (Uᗮ.starProjection).IsPositive := by
    exact ContinuousLinearMap.IsPositive.of_isStarProjection
      (subspaceProjection_operator_isStarProjection (𝕜 := 𝕜) (E := E) Uᗮ)
  rw [← subspaceProjectionRecovery_orthogonal_operator (𝕜 := 𝕜) (E := E) cutoff U]
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).2 hPos

theorem subspaceProjectionRecovery_operator_le_id
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U).operator ≤
      ContinuousLinearMap.id 𝕜 E := by
  refine (ContinuousLinearMap.le_def _ _).2 ?_
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).1
    (subspaceProjectionRecovery_operator_complement_nonneg (𝕜 := 𝕜) (E := E) cutoff U)

theorem subspaceProjectionRecovery_operator_mem_Icc
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U).operator ∈
      Set.Icc (0 : BoundedEndo 𝕜 E) (ContinuousLinearMap.id 𝕜 E) := by
  exact ⟨subspaceProjectionRecovery_operator_nonneg (𝕜 := 𝕜) (E := E) cutoff U,
    subspaceProjectionRecovery_operator_le_id (𝕜 := 𝕜) (E := E) cutoff U⟩

theorem subspaceProjectionRecovery_operator_le_iff
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U).operator ≤
        (subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff V).operator ↔
      U ≤ V := by
  simpa [subspaceProjectionRecovery_operator_eq] using
    (Submodule.starProjection_le_starProjection_iff (𝕜 := 𝕜) (E := E) (U := U) (V := V))

theorem subspaceProjectionRecovery_operator_eq_iff
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U).operator =
        (subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff V).operator ↔
      U = V := by
  simpa [subspaceProjectionRecovery_operator_eq] using
    (Submodule.starProjection_inj (𝕜 := 𝕜) (E := E) (U := U) (V := V))

theorem subspaceProjectionRecovery_positive_compression
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    {T : BoundedEndo 𝕜 E} (hT : T.IsPositive) :
    ((subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U).operator ∘L T ∘L
      (subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U).operator).IsPositive := by
  simpa [subspaceProjectionRecovery_operator_eq] using hT.conj_starProjection (U := U)

theorem subspaceProjectionRecovery_positive_subspace_compression
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    {T : BoundedEndo 𝕜 E} (hT : T.IsPositive) :
    (U.orthogonalProjection ∘L T ∘L U.subtypeL).IsPositive := by
  simpa using hT.orthogonalProjection_comp U

end CoherenceCalculusMathlibBridge
