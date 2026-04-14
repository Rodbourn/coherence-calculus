import CoherenceCalculusMathlibBridge.HilbertSpectralValidation
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.LinearAlgebra.Eigenspace.Basic

namespace CoherenceCalculusMathlibBridge

open CoherenceCalculus

/--
Validated Hilbert consumer slice for eigenspace and eigenvalue consequences on
the concrete `U.starProjection` recovery model. The eigenspace API in mathlib
lives on `Module.End`, so this slice works on the explicit `.toLinearMap`
view of the recovered operators.
-/
noncomputable def subspaceProjectionRecovery_operatorEnd
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    Module.End 𝕜 E :=
  ((subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U).operator).toLinearMap

noncomputable def subspaceProjectionRecovery_orthogonal_operatorEnd
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    Module.End 𝕜 E :=
  (ContinuousLinearMap.id 𝕜 E -
    (subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U).operator).toLinearMap

theorem subspaceProjectionRecovery_operatorEnd_eq
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U =
      U.starProjection.toLinearMap := by
  simpa [subspaceProjectionRecovery_operatorEnd] using
    congrArg ContinuousLinearMap.toLinearMap
      (subspaceProjectionRecovery_operator_eq (𝕜 := 𝕜) (E := E) cutoff U)

theorem subspaceProjectionRecovery_orthogonal_operatorEnd_eq
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U =
      (Uᗮ.starProjection).toLinearMap := by
  simpa [subspaceProjectionRecovery_orthogonal_operatorEnd] using
    congrArg ContinuousLinearMap.toLinearMap
      (subspaceProjectionRecovery_orthogonal_operator (𝕜 := 𝕜) (E := E) cutoff U).symm

theorem subspaceProjectionRecovery_operator_eigenspace_one
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U).eigenspace 1 = U := by
  ext x
  rw [subspaceProjectionRecovery_operatorEnd_eq, Module.End.mem_eigenspace_iff]
  simpa using (U.starProjection_eq_self_iff (v := x))

theorem subspaceProjectionRecovery_operator_eigenspace_zero
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U).eigenspace 0 = Uᗮ := by
  rw [subspaceProjectionRecovery_operatorEnd_eq, Module.End.eigenspace_zero]
  exact Submodule.ker_starProjection (U := U)

theorem subspaceProjectionRecovery_operator_hasEigenvalue_one_iff
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U).HasEigenvalue 1 ↔
      U ≠ ⊥ := by
  rw [Module.End.hasEigenvalue_iff, subspaceProjectionRecovery_operator_eigenspace_one]

theorem subspaceProjectionRecovery_operator_hasEigenvalue_zero_iff
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U).HasEigenvalue 0 ↔
      U ≠ ⊤ := by
  rw [Module.End.hasEigenvalue_iff, subspaceProjectionRecovery_operator_eigenspace_zero]
  exact not_congr (Submodule.orthogonal_eq_bot_iff (K := U))

theorem subspaceProjectionRecovery_operator_one_mem_spectrum_iff
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    (1 : ℂ) ∈ spectrum ℂ (subspaceProjectionRecovery_operatorEnd (E := E) cutoff U) ↔
      U ≠ ⊥ := by
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum,
    subspaceProjectionRecovery_operator_hasEigenvalue_one_iff (𝕜 := ℂ) (E := E) cutoff U]

theorem subspaceProjectionRecovery_operator_zero_mem_spectrum_iff
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    (0 : ℂ) ∈ spectrum ℂ (subspaceProjectionRecovery_operatorEnd (E := E) cutoff U) ↔
      U ≠ ⊤ := by
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum,
    subspaceProjectionRecovery_operator_hasEigenvalue_zero_iff (𝕜 := ℂ) (E := E) cutoff U]

theorem subspaceProjectionRecovery_orthogonal_operator_eigenspace_one
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U).eigenspace 1 =
      Uᗮ := by
  rw [subspaceProjectionRecovery_orthogonal_operatorEnd_eq]
  simpa using
    (subspaceProjectionRecovery_operator_eigenspace_one (𝕜 := 𝕜) (E := E) cutoff Uᗮ)

theorem subspaceProjectionRecovery_orthogonal_operator_eigenspace_zero
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U).eigenspace 0 =
      U := by
  rw [subspaceProjectionRecovery_orthogonal_operatorEnd_eq]
  simpa using
    (subspaceProjectionRecovery_operator_eigenspace_zero (𝕜 := 𝕜) (E := E) cutoff Uᗮ)

theorem subspaceProjectionRecovery_orthogonal_operator_hasEigenvalue_one_iff
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U).HasEigenvalue 1 ↔
      U ≠ ⊤ := by
  rw [Module.End.hasEigenvalue_iff, subspaceProjectionRecovery_orthogonal_operator_eigenspace_one]
  exact not_congr (Submodule.orthogonal_eq_bot_iff (K := U))

theorem subspaceProjectionRecovery_orthogonal_operator_hasEigenvalue_zero_iff
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U).HasEigenvalue 0 ↔
      U ≠ ⊥ := by
  rw [Module.End.hasEigenvalue_iff, subspaceProjectionRecovery_orthogonal_operator_eigenspace_zero]

theorem subspaceProjectionRecovery_orthogonal_operator_one_mem_spectrum_iff
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    (1 : ℂ) ∈ spectrum ℂ (subspaceProjectionRecovery_orthogonal_operatorEnd (E := E) cutoff U) ↔
      U ≠ ⊤ := by
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum,
    subspaceProjectionRecovery_orthogonal_operator_hasEigenvalue_one_iff
      (𝕜 := ℂ) (E := E) cutoff U]

theorem subspaceProjectionRecovery_orthogonal_operator_zero_mem_spectrum_iff
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    (0 : ℂ) ∈ spectrum ℂ (subspaceProjectionRecovery_orthogonal_operatorEnd (E := E) cutoff U) ↔
      U ≠ ⊥ := by
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum,
    subspaceProjectionRecovery_orthogonal_operator_hasEigenvalue_zero_iff
      (𝕜 := ℂ) (E := E) cutoff U]

end CoherenceCalculusMathlibBridge
