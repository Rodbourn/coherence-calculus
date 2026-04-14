import CoherenceCalculusMathlibBridge.HilbertEigenspaceValidation
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

namespace CoherenceCalculusMathlibBridge

open CoherenceCalculus
open Polynomial
open scoped Polynomial

/--
Validated Hilbert consumer slice for minimal-polynomial consequences on the
concrete finite-dimensional `U.starProjection` recovery model.
-/
theorem subspaceProjectionRecovery_operator_minpoly_isRoot_one_iff
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (minpoly 𝕜 (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U)).IsRoot 1 ↔
      U ≠ ⊥ := by
  rw [← Module.End.hasEigenvalue_iff_isRoot,
    subspaceProjectionRecovery_operator_hasEigenvalue_one_iff (𝕜 := 𝕜) (E := E) cutoff U]

theorem subspaceProjectionRecovery_operator_minpoly_isRoot_zero_iff
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (minpoly 𝕜 (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U)).IsRoot 0 ↔
      U ≠ ⊤ := by
  rw [← Module.End.hasEigenvalue_iff_isRoot,
    subspaceProjectionRecovery_operator_hasEigenvalue_zero_iff (𝕜 := 𝕜) (E := E) cutoff U]

theorem subspaceProjectionRecovery_orthogonal_operator_minpoly_isRoot_one_iff
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (minpoly 𝕜
      (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U)).IsRoot 1 ↔
      U ≠ ⊤ := by
  rw [← Module.End.hasEigenvalue_iff_isRoot,
    subspaceProjectionRecovery_orthogonal_operator_hasEigenvalue_one_iff
      (𝕜 := 𝕜) (E := E) cutoff U]

theorem subspaceProjectionRecovery_orthogonal_operator_minpoly_isRoot_zero_iff
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (minpoly 𝕜
      (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U)).IsRoot 0 ↔
      U ≠ ⊥ := by
  rw [← Module.End.hasEigenvalue_iff_isRoot,
    subspaceProjectionRecovery_orthogonal_operator_hasEigenvalue_zero_iff
      (𝕜 := 𝕜) (E := E) cutoff U]

theorem subspaceProjectionRecovery_operator_minpoly_dvd_projectionQuadratic
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    minpoly 𝕜 (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) ∣
      X * (X - C (1 : 𝕜)) := by
  refine minpoly.dvd 𝕜 _ ?_
  have hp : IsIdempotentElem (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) := by
    rw [subspaceProjectionRecovery_operatorEnd_eq]
    exact (ContinuousLinearMap.isIdempotentElem_toLinearMap_iff).2 U.isIdempotentElem_starProjection
  rw [map_mul, map_sub]
  simp only [aeval_X, aeval_C]
  simp [mul_sub, hp.eq]

theorem subspaceProjectionRecovery_orthogonal_operator_minpoly_dvd_projectionQuadratic
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    minpoly 𝕜 (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) ∣
      X * (X - C (1 : 𝕜)) := by
  refine minpoly.dvd 𝕜 _ ?_
  have hp :
      IsIdempotentElem
        (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) := by
    rw [subspaceProjectionRecovery_orthogonal_operatorEnd_eq]
    exact
      (ContinuousLinearMap.isIdempotentElem_toLinearMap_iff).2 (Uᗮ).isIdempotentElem_starProjection
  rw [map_mul, map_sub]
  simp only [aeval_X, aeval_C]
  simp [mul_sub, hp.eq]

theorem top_subspaceProjectionRecovery_operator_minpoly
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E] [Nontrivial E]
    (cutoff : Nat) :
    minpoly 𝕜
        (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff (⊤ : Submodule 𝕜 E)) =
      X - C (1 : 𝕜) := by
  rw [subspaceProjectionRecovery_operatorEnd_eq, Submodule.starProjection_top']
  change minpoly 𝕜 (1 : Module.End 𝕜 E) = X - 1
  exact minpoly.one (A := 𝕜) (B := Module.End 𝕜 E)

theorem bot_subspaceProjectionRecovery_operator_minpoly
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E] [Nontrivial E]
    (cutoff : Nat) :
    minpoly 𝕜
        (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff (⊥ : Submodule 𝕜 E)) =
      X := by
  rw [subspaceProjectionRecovery_operatorEnd_eq, Submodule.starProjection_bot]
  exact minpoly.zero (A := 𝕜) (B := Module.End 𝕜 E)

theorem top_subspaceProjectionRecovery_orthogonal_operator_minpoly
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E] [Nontrivial E]
    (cutoff : Nat) :
    minpoly 𝕜
        (subspaceProjectionRecovery_orthogonal_operatorEnd
          (𝕜 := 𝕜) (E := E) cutoff (⊤ : Submodule 𝕜 E)) =
      X := by
  simpa [subspaceProjectionRecovery_orthogonal_operatorEnd_eq, Submodule.top_orthogonal_eq_bot] using
    (minpoly.zero (A := 𝕜) (B := Module.End 𝕜 E))

theorem bot_subspaceProjectionRecovery_orthogonal_operator_minpoly
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E] [Nontrivial E]
    (cutoff : Nat) :
    minpoly 𝕜
        (subspaceProjectionRecovery_orthogonal_operatorEnd
          (𝕜 := 𝕜) (E := E) cutoff (⊥ : Submodule 𝕜 E)) =
      X - C (1 : 𝕜) := by
  simpa [subspaceProjectionRecovery_orthogonal_operatorEnd_eq, Submodule.bot_orthogonal_eq_top] using
    (top_subspaceProjectionRecovery_operator_minpoly (𝕜 := 𝕜) (E := E) cutoff)

end CoherenceCalculusMathlibBridge
