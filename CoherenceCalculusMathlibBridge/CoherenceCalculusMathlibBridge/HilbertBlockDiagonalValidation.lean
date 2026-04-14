import CoherenceCalculusMathlibBridge.HilbertTraceRankValidation
import Mathlib.Analysis.InnerProductSpace.Orthogonal

namespace CoherenceCalculusMathlibBridge

open CoherenceCalculus

/--
Validated Hilbert consumer slice for block-diagonal normal form of the concrete
`U.starProjection` recovery model.
-/
theorem subspaceProjectionRecovery_operator_isCompl
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    IsCompl U (LinearMap.ker (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U)) :=
  (subspaceProjectionRecovery_operator_isProj (𝕜 := 𝕜) (E := E) cutoff U).isCompl

theorem subspaceProjectionRecovery_operator_isCompl_orthogonal
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    IsCompl U Uᗮ := by
  simpa [subspaceProjectionRecovery_operator_ker_eq (𝕜 := 𝕜) (E := E) cutoff U] using
    (subspaceProjectionRecovery_operator_isCompl (𝕜 := 𝕜) (E := E) cutoff U)

theorem subspaceProjectionRecovery_operator_eq_conj_prodMap
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U =
      (U.prodEquivOfIsCompl
        (LinearMap.ker (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U))
        (subspaceProjectionRecovery_operator_isCompl (𝕜 := 𝕜) (E := E) cutoff U)).conj
        (LinearMap.prodMap LinearMap.id 0) := by
  exact
    (subspaceProjectionRecovery_operator_isProj (𝕜 := 𝕜) (E := E) cutoff U).eq_conj_prodMap

theorem subspaceProjectionRecovery_orthogonal_operator_eq_conj_prodMap
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U =
      (Uᗮ.prodEquivOfIsCompl
        (LinearMap.ker
          (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U))
        (subspaceProjectionRecovery_orthogonal_operator_isProj
          (𝕜 := 𝕜) (E := E) cutoff U |>.isCompl)).conj
        (LinearMap.prodMap LinearMap.id 0) := by
  exact
    (subspaceProjectionRecovery_orthogonal_operator_isProj (𝕜 := 𝕜) (E := E) cutoff U).eq_conj_prodMap

theorem subspaceProjectionRecovery_operator_eq_id_iff
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U = LinearMap.id ↔ U = ⊤ := by
  simpa [Iff.comm] using
    (subspaceProjectionRecovery_operator_isProj (𝕜 := 𝕜) (E := E) cutoff U).submodule_eq_top_iff

theorem subspaceProjectionRecovery_operator_eq_zero_iff
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U = 0 ↔ U = ⊥ := by
  simpa [Iff.comm] using
    (subspaceProjectionRecovery_operator_isProj (𝕜 := 𝕜) (E := E) cutoff U).submodule_eq_bot_iff

theorem subspaceProjectionRecovery_orthogonal_operator_eq_id_iff
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U = LinearMap.id ↔
      U = ⊥ := by
  have h :=
    (subspaceProjectionRecovery_orthogonal_operator_isProj (𝕜 := 𝕜) (E := E) cutoff U).submodule_eq_top_iff
  simpa [Iff.comm, Submodule.orthogonal_eq_top_iff] using h

theorem subspaceProjectionRecovery_orthogonal_operator_eq_zero_iff
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U = 0 ↔
      U = ⊤ := by
  have h :=
    (subspaceProjectionRecovery_orthogonal_operator_isProj (𝕜 := 𝕜) (E := E) cutoff U).submodule_eq_bot_iff
  simpa [Iff.comm, Submodule.orthogonal_eq_bot_iff] using h

theorem subspaceProjectionRecovery_block_symm_fst_eq_zero_iff
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] {x : E} :
    ((U.prodEquivOfIsCompl
        (LinearMap.ker (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U))
        (subspaceProjectionRecovery_operator_isCompl (𝕜 := 𝕜) (E := E) cutoff U)).symm x).1 = 0 ↔
      x ∈ Uᗮ := by
  simpa [subspaceProjectionRecovery_operator_ker_eq (𝕜 := 𝕜) (E := E) cutoff U] using
    (Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero
      (p := U)
      (q := LinearMap.ker (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U))
      (h := subspaceProjectionRecovery_operator_isCompl (𝕜 := 𝕜) (E := E) cutoff U)
      (x := x))

theorem subspaceProjectionRecovery_block_symm_snd_eq_zero_iff
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] {x : E} :
    ((U.prodEquivOfIsCompl
        (LinearMap.ker (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U))
        (subspaceProjectionRecovery_operator_isCompl (𝕜 := 𝕜) (E := E) cutoff U)).symm x).2 = 0 ↔
      x ∈ U := by
  simpa using
    (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero
      (p := U)
      (q := LinearMap.ker (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U))
      (h := subspaceProjectionRecovery_operator_isCompl (𝕜 := 𝕜) (E := E) cutoff U)
      (x := x))

end CoherenceCalculusMathlibBridge
