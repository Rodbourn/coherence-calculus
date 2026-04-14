import CoherenceCalculusMathlibBridge.HilbertMinpolyValidation
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace CoherenceCalculusMathlibBridge

open CoherenceCalculus
open Module

/--
Validated Hilbert consumer slice for range/kernel and finite-dimensional rank
consequences on the concrete `U.starProjection` recovery model.
-/
theorem subspaceProjectionRecovery_operator_range_eq
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    LinearMap.range (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) = U := by
  rw [subspaceProjectionRecovery_operatorEnd_eq]
  exact Submodule.range_starProjection (U := U)

theorem subspaceProjectionRecovery_operator_ker_eq
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    LinearMap.ker (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) = Uᗮ := by
  rw [subspaceProjectionRecovery_operatorEnd_eq]
  exact Submodule.ker_starProjection (U := U)

theorem subspaceProjectionRecovery_orthogonal_operator_range_eq
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    LinearMap.range (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) =
      Uᗮ := by
  rw [subspaceProjectionRecovery_orthogonal_operatorEnd_eq]
  exact Submodule.range_starProjection (U := Uᗮ)

theorem subspaceProjectionRecovery_orthogonal_operator_ker_eq
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    LinearMap.ker (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) =
      U := by
  rw [subspaceProjectionRecovery_orthogonal_operatorEnd_eq]
  have hker : LinearMap.ker (↑(Uᗮ).starProjection : E →ₗ[𝕜] E) = Uᗮᗮ := by
    exact Submodule.ker_starProjection (U := Uᗮ)
  rw [hker, Submodule.orthogonal_orthogonal]

theorem subspaceProjectionRecovery_operator_finrank_range
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    finrank 𝕜
        (LinearMap.range (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U)) =
      finrank 𝕜 U := by
  rw [subspaceProjectionRecovery_operator_range_eq]

theorem subspaceProjectionRecovery_operator_finrank_ker
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    finrank 𝕜
        (LinearMap.ker (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U)) =
      finrank 𝕜 Uᗮ := by
  rw [subspaceProjectionRecovery_operator_ker_eq]

theorem subspaceProjectionRecovery_orthogonal_operator_finrank_range
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    finrank 𝕜
        (LinearMap.range
          (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U)) =
      finrank 𝕜 Uᗮ := by
  rw [subspaceProjectionRecovery_orthogonal_operator_range_eq]

theorem subspaceProjectionRecovery_orthogonal_operator_finrank_ker
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    finrank 𝕜
        (LinearMap.ker
          (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U)) =
      finrank 𝕜 U := by
  rw [subspaceProjectionRecovery_orthogonal_operator_ker_eq]

theorem subspaceProjectionRecovery_operator_finrank_range_add_finrank_ker
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    finrank 𝕜
        (LinearMap.range (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U)) +
      finrank 𝕜
        (LinearMap.ker (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U)) =
      finrank 𝕜 E := by
  simpa using
    (LinearMap.finrank_range_add_finrank_ker
      (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U))

theorem subspaceProjectionRecovery_operator_finrank_range_add_orthogonal
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    finrank 𝕜
        (LinearMap.range (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U)) +
      finrank 𝕜
        (LinearMap.range
          (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U)) =
      finrank 𝕜 E := by
  rw [subspaceProjectionRecovery_operator_finrank_range,
    subspaceProjectionRecovery_orthogonal_operator_finrank_range]
  exact Submodule.finrank_add_finrank_orthogonal U

end CoherenceCalculusMathlibBridge
