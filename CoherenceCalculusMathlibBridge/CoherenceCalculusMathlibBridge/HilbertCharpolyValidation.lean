import CoherenceCalculusMathlibBridge.HilbertEigenspaceValidation
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

namespace CoherenceCalculusMathlibBridge

open CoherenceCalculus

/--
Validated Hilbert consumer slice for characteristic-polynomial consequences on
the concrete `U.starProjection` recovery model, via the finite-dimensional
`Module.End` API.
-/
theorem subspaceProjectionRecovery_operator_mem_spectrum_iff_isRoot_charpoly
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection] (μ : ℂ) :
    μ ∈ spectrum ℂ (subspaceProjectionRecovery_operatorEnd (E := E) cutoff U) ↔
      (subspaceProjectionRecovery_operatorEnd (E := E) cutoff U).charpoly.IsRoot μ := by
  simpa using
    (Module.End.mem_spectrum_iff_isRoot_charpoly
      (subspaceProjectionRecovery_operatorEnd (E := E) cutoff U) μ)

theorem subspaceProjectionRecovery_operator_charpoly_root_one_iff
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    (subspaceProjectionRecovery_operatorEnd (E := E) cutoff U).charpoly.IsRoot 1 ↔ U ≠ ⊥ := by
  rw [← Module.End.hasEigenvalue_iff_isRoot_charpoly,
    subspaceProjectionRecovery_operator_hasEigenvalue_one_iff (𝕜 := ℂ) (E := E) cutoff U]

theorem subspaceProjectionRecovery_operator_charpoly_root_zero_iff
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    (subspaceProjectionRecovery_operatorEnd (E := E) cutoff U).charpoly.IsRoot 0 ↔ U ≠ ⊤ := by
  rw [← Module.End.hasEigenvalue_iff_isRoot_charpoly,
    subspaceProjectionRecovery_operator_hasEigenvalue_zero_iff (𝕜 := ℂ) (E := E) cutoff U]

theorem subspaceProjectionRecovery_orthogonal_operator_mem_spectrum_iff_isRoot_charpoly
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection] (μ : ℂ) :
    μ ∈ spectrum ℂ (subspaceProjectionRecovery_orthogonal_operatorEnd (E := E) cutoff U) ↔
      (subspaceProjectionRecovery_orthogonal_operatorEnd (E := E) cutoff U).charpoly.IsRoot μ := by
  simpa using
    (Module.End.mem_spectrum_iff_isRoot_charpoly
      (subspaceProjectionRecovery_orthogonal_operatorEnd (E := E) cutoff U) μ)

theorem subspaceProjectionRecovery_orthogonal_operator_charpoly_root_one_iff
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    (subspaceProjectionRecovery_orthogonal_operatorEnd (E := E) cutoff U).charpoly.IsRoot 1 ↔
      U ≠ ⊤ := by
  rw [← Module.End.hasEigenvalue_iff_isRoot_charpoly,
    subspaceProjectionRecovery_orthogonal_operator_hasEigenvalue_one_iff
      (𝕜 := ℂ) (E := E) cutoff U]

theorem subspaceProjectionRecovery_orthogonal_operator_charpoly_root_zero_iff
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    (subspaceProjectionRecovery_orthogonal_operatorEnd (E := E) cutoff U).charpoly.IsRoot 0 ↔
      U ≠ ⊥ := by
  rw [← Module.End.hasEigenvalue_iff_isRoot_charpoly,
    subspaceProjectionRecovery_orthogonal_operator_hasEigenvalue_zero_iff
      (𝕜 := ℂ) (E := E) cutoff U]

end CoherenceCalculusMathlibBridge
