import CoherenceCalculusMathlibBridge.HilbertTraceValidation
import Mathlib.LinearAlgebra.Projection

namespace CoherenceCalculusMathlibBridge

open CoherenceCalculus
open Module

/--
Validated Hilbert consumer slice linking the concrete finite-dimensional
projection model to mathlib's projection-trace theorem family.
-/
theorem subspaceProjectionRecovery_operator_isProj
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    LinearMap.IsProj U
      (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) := by
  have hIdem :
      IsIdempotentElem
        (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) := by
    rw [subspaceProjectionRecovery_operatorEnd_eq]
    exact (ContinuousLinearMap.isIdempotentElem_toLinearMap_iff).2 U.isIdempotentElem_starProjection
  have hRange :
      LinearMap.IsProj
        (LinearMap.range (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U))
        (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) := by
    exact
      (LinearMap.isProj_range_iff_isIdempotentElem
        (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U)).2 hIdem
  simpa [subspaceProjectionRecovery_operator_range_eq (𝕜 := 𝕜) (E := E) cutoff U] using hRange

theorem subspaceProjectionRecovery_orthogonal_operator_isProj
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    LinearMap.IsProj Uᗮ
      (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) := by
  have hIdem :
      IsIdempotentElem
        (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) := by
    rw [subspaceProjectionRecovery_orthogonal_operatorEnd_eq]
    exact
      (ContinuousLinearMap.isIdempotentElem_toLinearMap_iff).2 (Uᗮ).isIdempotentElem_starProjection
  have hRange :
      LinearMap.IsProj
        (LinearMap.range
          (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U))
        (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) := by
    exact
      (LinearMap.isProj_range_iff_isIdempotentElem
        (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U)).2 hIdem
  simpa [subspaceProjectionRecovery_orthogonal_operator_range_eq (𝕜 := 𝕜) (E := E) cutoff U] using
    hRange

theorem subspaceProjectionRecovery_operator_trace_eq_finrank_subspace
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) =
      (finrank 𝕜 U : 𝕜) := by
  have hProj :=
    subspaceProjectionRecovery_operator_isProj (𝕜 := 𝕜) (E := E) cutoff U
  simpa using
    (LinearMap.IsProj.trace
      (R := 𝕜) (M := E) (p := U)
      (f := subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) hProj)

theorem subspaceProjectionRecovery_orthogonal_operator_trace_eq_finrank_subspace
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_orthogonal_operatorEnd
          (𝕜 := 𝕜) (E := E) cutoff U) =
      (finrank 𝕜 Uᗮ : 𝕜) := by
  have hProj :=
    subspaceProjectionRecovery_orthogonal_operator_isProj (𝕜 := 𝕜) (E := E) cutoff U
  simpa using
    (LinearMap.IsProj.trace
      (R := 𝕜) (M := E) (p := Uᗮ)
      (f := subspaceProjectionRecovery_orthogonal_operatorEnd
        (𝕜 := 𝕜) (E := E) cutoff U) hProj)

theorem subspaceProjectionRecovery_operator_trace_eq_finrank_range
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) =
      (finrank 𝕜
        (LinearMap.range (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U)) : 𝕜) := by
  simpa [subspaceProjectionRecovery_operator_finrank_range (𝕜 := 𝕜) (E := E) cutoff U] using
    (subspaceProjectionRecovery_operator_trace_eq_finrank_subspace
      (𝕜 := 𝕜) (E := E) cutoff U)

theorem subspaceProjectionRecovery_orthogonal_operator_trace_eq_finrank_range
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_orthogonal_operatorEnd
          (𝕜 := 𝕜) (E := E) cutoff U) =
      (finrank 𝕜
        (LinearMap.range
          (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U)) : 𝕜) := by
  simpa [subspaceProjectionRecovery_orthogonal_operator_finrank_range (𝕜 := 𝕜) (E := E) cutoff U] using
    (subspaceProjectionRecovery_orthogonal_operator_trace_eq_finrank_subspace
      (𝕜 := 𝕜) (E := E) cutoff U)

theorem subspaceProjectionRecovery_operator_trace_eq_zero_iff
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) = 0 ↔
      U = ⊥ := by
  rw [subspaceProjectionRecovery_operator_trace_eq_finrank_subspace, Nat.cast_eq_zero,
    Submodule.finrank_eq_zero]

theorem subspaceProjectionRecovery_orthogonal_operator_trace_eq_zero_iff
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_orthogonal_operatorEnd
          (𝕜 := 𝕜) (E := E) cutoff U) = 0 ↔
      U = ⊤ := by
  rw [subspaceProjectionRecovery_orthogonal_operator_trace_eq_finrank_subspace, Nat.cast_eq_zero,
    Submodule.finrank_eq_zero, Submodule.orthogonal_eq_bot_iff]

end CoherenceCalculusMathlibBridge
