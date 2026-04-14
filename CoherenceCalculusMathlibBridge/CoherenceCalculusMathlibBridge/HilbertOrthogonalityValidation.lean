import CoherenceCalculusMathlibBridge.HilbertProjectionValidation

namespace CoherenceCalculusMathlibBridge

open CoherenceCalculus

/--
Further validated Hilbert consumer slice: standard orthogonal-projection laws on
the concrete recovery model built from `U.starProjection`.
-/
theorem subspaceProjectionRecovery_operator_eq
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U).operator = U.starProjection := by
  rfl

theorem subspaceProjectionRecovery_operator_apply_mem
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (x : E) :
    (subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U).operator x ∈ U := by
  exact U.starProjection_apply_mem x

theorem subspaceProjectionRecovery_residual_mem_orthogonal
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (x : E) :
    x - (subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U).operator x ∈ Uᗮ := by
  exact U.sub_starProjection_mem_orthogonal x

theorem subspaceProjectionRecovery_operator_eq_self_iff
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (x : E) :
    (subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U).operator x = x ↔ x ∈ U := by
  simpa [subspaceProjectionRecovery_operator_eq] using (U.starProjection_eq_self_iff (v := x))

theorem subspaceProjectionRecovery_operator_idempotent
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (x : E) :
    (subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U).operator
        ((subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U).operator x) =
      (subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U).operator x := by
  have hx : U.starProjection x ∈ U := U.starProjection_apply_mem x
  simpa [subspaceProjectionRecovery_operator_eq] using
    ((U.starProjection_eq_self_iff (v := U.starProjection x)).2 hx)

theorem subspaceProjectionRecovery_orthogonal_operator
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    Uᗮ.starProjection =
      ContinuousLinearMap.id 𝕜 E - (subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U).operator := by
  simpa [subspaceProjectionRecovery_operator_eq] using Submodule.starProjection_orthogonal U

theorem subspaceProjectionRecovery_operator_norm_le
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (x : E) :
    ‖(subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U).operator x‖ ≤ ‖x‖ := by
  simpa [subspaceProjectionRecovery_operator_eq] using U.norm_orthogonalProjection_apply_le x

theorem subspaceProjectionRecovery_operator_comp_orthogonal_eq_zero
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U).operator ∘L Uᗮ.starProjection = 0 := by
  simpa [subspaceProjectionRecovery_operator_eq] using
    (Submodule.isOrtho_orthogonal_right (𝕜 := 𝕜) (E := E) U).starProjection_comp_starProjection

theorem subspaceProjectionRecovery_operator_comp_of_le
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (hUV : U ≤ V) :
    (subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U).operator ∘L V.starProjection =
      (subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U).operator := by
  simpa [subspaceProjectionRecovery_operator_eq] using
    (Submodule.starProjection_comp_starProjection_of_le (U := U) (V := V) hUV)

theorem top_subspaceProjectionRecovery_operator_eq_id
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) :
    (subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff (⊤ : Submodule 𝕜 E)).operator =
      ContinuousLinearMap.id 𝕜 E := by
  simpa [subspaceProjectionRecovery_operator_eq] using
    (Submodule.starProjection_top (𝕜 := 𝕜) (E := E))

theorem bot_subspaceProjectionRecovery_operator_eq_zero
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) :
    (subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff (⊥ : Submodule 𝕜 E)).operator = 0 := by
  exact Submodule.starProjection_bot (𝕜 := 𝕜) (E := E)

end CoherenceCalculusMathlibBridge
