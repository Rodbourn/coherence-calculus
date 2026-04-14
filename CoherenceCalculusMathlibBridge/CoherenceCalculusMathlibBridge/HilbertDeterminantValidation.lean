import CoherenceCalculusMathlibBridge.HilbertEigenspaceValidation
import Mathlib.LinearAlgebra.Determinant

namespace CoherenceCalculusMathlibBridge

open CoherenceCalculus

/--
Validated Hilbert consumer slice for determinant and invertibility consequences
on the concrete finite-dimensional `U.starProjection` recovery model.
-/
theorem subspaceProjectionRecovery_operator_isUnit_iff
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    IsUnit (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) ↔ U = ⊤ := by
  rw [LinearMap.isUnit_iff_ker_eq_bot]
  rw [subspaceProjectionRecovery_operatorEnd_eq]
  have hker : LinearMap.ker (↑U.starProjection : E →ₗ[𝕜] E) = Uᗮ :=
    (Submodule.ker_starProjection (U := U))
  rw [hker]
  exact Submodule.orthogonal_eq_bot_iff

theorem subspaceProjectionRecovery_operator_det_eq_zero_iff
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U).det = 0 ↔ U ≠ ⊤ := by
  rw [LinearMap.det_eq_zero_iff_ker_ne_bot]
  rw [subspaceProjectionRecovery_operatorEnd_eq]
  have hker : LinearMap.ker (↑U.starProjection : E →ₗ[𝕜] E) = Uᗮ :=
    (Submodule.ker_starProjection (U := U))
  rw [hker]
  exact not_congr (Submodule.orthogonal_eq_bot_iff (K := U))

theorem subspaceProjectionRecovery_operator_det_ne_zero_iff
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U).det ≠ 0 ↔ U = ⊤ := by
  simpa using not_congr
    (subspaceProjectionRecovery_operator_det_eq_zero_iff (𝕜 := 𝕜) (E := E) cutoff U)

theorem top_subspaceProjectionRecovery_operator_det_eq_one
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) :
    (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff (⊤ : Submodule 𝕜 E)).det = 1 := by
  rw [subspaceProjectionRecovery_operatorEnd_eq, Submodule.starProjection_top]
  exact (LinearMap.det_id : LinearMap.det (LinearMap.id : E →ₗ[𝕜] E) = 1)

theorem subspaceProjectionRecovery_orthogonal_operator_isUnit_iff
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    IsUnit (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) ↔ U = ⊥ := by
  rw [LinearMap.isUnit_iff_ker_eq_bot]
  rw [subspaceProjectionRecovery_orthogonal_operatorEnd_eq]
  have hker : LinearMap.ker (↑(Uᗮ).starProjection : E →ₗ[𝕜] E) = Uᗮᗮ :=
    (Submodule.ker_starProjection (U := Uᗮ))
  rw [hker, Submodule.orthogonal_orthogonal]

theorem subspaceProjectionRecovery_orthogonal_operator_det_eq_zero_iff
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U).det = 0 ↔ U ≠ ⊥ := by
  rw [LinearMap.det_eq_zero_iff_ker_ne_bot]
  rw [subspaceProjectionRecovery_orthogonal_operatorEnd_eq]
  have hker : LinearMap.ker (↑(Uᗮ).starProjection : E →ₗ[𝕜] E) = Uᗮᗮ :=
    (Submodule.ker_starProjection (U := Uᗮ))
  rw [hker, Submodule.orthogonal_orthogonal]

theorem subspaceProjectionRecovery_orthogonal_operator_det_ne_zero_iff
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U).det ≠ 0 ↔ U = ⊥ := by
  simpa using not_congr
    (subspaceProjectionRecovery_orthogonal_operator_det_eq_zero_iff
      (𝕜 := 𝕜) (E := E) cutoff U)

theorem bot_subspaceProjectionRecovery_orthogonal_operator_det_eq_one
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) :
    (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff (⊥ : Submodule 𝕜 E)).det = 1 := by
  simpa [subspaceProjectionRecovery_orthogonal_operatorEnd_eq, Submodule.bot_orthogonal_eq_top] using
    (top_subspaceProjectionRecovery_operator_det_eq_one (𝕜 := 𝕜) (E := E) cutoff)

end CoherenceCalculusMathlibBridge
