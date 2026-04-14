import CoherenceCalculusMathlibBridge.HilbertRankValidation
import Mathlib.Analysis.InnerProductSpace.Trace

namespace CoherenceCalculusMathlibBridge

open CoherenceCalculus
open Module

/--
Validated Hilbert consumer slice for finite-dimensional trace consequences on
the concrete `U.starProjection` recovery model.
-/
theorem subspaceProjectionRecovery_operatorEnd_add_orthogonal_eq_one
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U +
        subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U =
      1 := by
  ext x
  simpa [subspaceProjectionRecovery_operatorEnd_eq, subspaceProjectionRecovery_orthogonal_operatorEnd_eq]
    using (Submodule.starProjection_add_starProjection_orthogonal (K := U) x)

theorem subspaceProjectionRecovery_operator_trace_add_orthogonal_eq_finrank
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    LinearMap.trace 𝕜 E (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) +
      LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) =
      (finrank 𝕜 E : 𝕜) := by
  have h :=
    congrArg (LinearMap.trace 𝕜 E)
      (subspaceProjectionRecovery_operatorEnd_add_orthogonal_eq_one (𝕜 := 𝕜) (E := E) cutoff U)
  simpa [map_add, LinearMap.trace_one] using h

theorem top_subspaceProjectionRecovery_operator_trace
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) :
    LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff (⊤ : Submodule 𝕜 E)) =
      (finrank 𝕜 E : 𝕜) := by
  rw [subspaceProjectionRecovery_operatorEnd_eq, Submodule.starProjection_top]
  exact LinearMap.trace_id 𝕜 E

theorem bot_subspaceProjectionRecovery_operator_trace
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) :
    LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff (⊥ : Submodule 𝕜 E)) =
      0 := by
  rw [subspaceProjectionRecovery_operatorEnd_eq, Submodule.starProjection_bot]
  simp

theorem top_subspaceProjectionRecovery_orthogonal_operator_trace
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) :
    LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_orthogonal_operatorEnd
          (𝕜 := 𝕜) (E := E) cutoff (⊤ : Submodule 𝕜 E)) =
      0 := by
  have hsum :=
    subspaceProjectionRecovery_operator_trace_add_orthogonal_eq_finrank
      (𝕜 := 𝕜) (E := E) cutoff (⊤ : Submodule 𝕜 E)
  rw [top_subspaceProjectionRecovery_operator_trace (𝕜 := 𝕜) (E := E) cutoff] at hsum
  have hsum' :
      (finrank 𝕜 E : 𝕜) +
          LinearMap.trace 𝕜 E
            (subspaceProjectionRecovery_orthogonal_operatorEnd
              (𝕜 := 𝕜) (E := E) cutoff (⊤ : Submodule 𝕜 E)) =
        (finrank 𝕜 E : 𝕜) + 0 := by
    simpa using hsum
  exact add_left_cancel hsum'

theorem bot_subspaceProjectionRecovery_orthogonal_operator_trace
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) :
    LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_orthogonal_operatorEnd
          (𝕜 := 𝕜) (E := E) cutoff (⊥ : Submodule 𝕜 E)) =
      (finrank 𝕜 E : 𝕜) := by
  have hsum :=
    subspaceProjectionRecovery_operator_trace_add_orthogonal_eq_finrank
      (𝕜 := 𝕜) (E := E) cutoff (⊥ : Submodule 𝕜 E)
  rw [bot_subspaceProjectionRecovery_operator_trace (𝕜 := 𝕜) (E := E) cutoff, zero_add] at hsum
  exact hsum

theorem subspaceProjectionRecovery_operatorEnd_mul_orthogonal_eq_zero
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U *
        subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U =
      0 := by
  rw [subspaceProjectionRecovery_operatorEnd_eq, subspaceProjectionRecovery_orthogonal_operatorEnd_eq]
  ext x
  simpa using
    DFunLike.congr_fun
      ((Submodule.isOrtho_orthogonal_right (𝕜 := 𝕜) (E := E) U).starProjection_comp_starProjection)
      x

theorem subspaceProjectionRecovery_orthogonal_operatorEnd_mul_operator_eq_zero
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U *
        subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U =
      0 := by
  rw [subspaceProjectionRecovery_orthogonal_operatorEnd_eq, subspaceProjectionRecovery_operatorEnd_eq]
  ext x
  simpa using
    DFunLike.congr_fun
      ((Submodule.isOrtho_orthogonal_left (𝕜 := 𝕜) (E := E) U).starProjection_comp_starProjection)
      x

theorem subspaceProjectionRecovery_operator_trace_mul_orthogonal_eq_zero
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U *
          subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) =
      0 := by
  rw [subspaceProjectionRecovery_operatorEnd_mul_orthogonal_eq_zero]
  simp

theorem subspaceProjectionRecovery_orthogonal_operator_trace_mul_eq_zero
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U *
          subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) =
      0 := by
  rw [subspaceProjectionRecovery_orthogonal_operatorEnd_mul_operator_eq_zero]
  simp

theorem subspaceProjectionRecovery_operator_trace_square_eq
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U *
          subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) =
      LinearMap.trace 𝕜 E (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) := by
  have hp :
      IsIdempotentElem (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) := by
    rw [subspaceProjectionRecovery_operatorEnd_eq]
    exact (ContinuousLinearMap.isIdempotentElem_toLinearMap_iff).2 U.isIdempotentElem_starProjection
  simp [hp.eq]

theorem subspaceProjectionRecovery_orthogonal_operator_trace_square_eq
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U *
          subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) =
      LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) := by
  have hp :
      IsIdempotentElem
        (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) := by
    rw [subspaceProjectionRecovery_orthogonal_operatorEnd_eq]
    exact
      (ContinuousLinearMap.isIdempotentElem_toLinearMap_iff).2 (Uᗮ).isIdempotentElem_starProjection
  simp [hp.eq]

end CoherenceCalculusMathlibBridge
