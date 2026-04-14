import CoherenceCalculusMathlibBridge.HilbertBlockFactorizationValidation
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

namespace CoherenceCalculusMathlibBridge

open CoherenceCalculus

/--
Validated Hilbert consumer slice for spectrum/eigenvalue behavior of the
block-diagonal operator on the concrete `U ⊕ Uᗮ` decomposition.

This uses the exact block factorization already proved for the detached bridge
and pushes it through mathlib's own finite-dimensional
`mem_spectrum_iff_isRoot_charpoly` / `hasEigenvalue_iff_isRoot_charpoly`
consumer theorems.
-/
theorem subspaceProjectionRecovery_blockDiagonal_charpoly_root_iff
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (T : Module.End ℂ E) (μ : ℂ) :
    (subspaceProjectionRecovery_blockDiagonal_operatorEnd
        (𝕜 := ℂ) (E := E) cutoff U T).charpoly.IsRoot μ ↔
      (subspaceProjectionRecovery_blockSubspaceEnd
          (𝕜 := ℂ) (E := E) cutoff U T).charpoly.IsRoot μ ∨
        (subspaceProjectionRecovery_blockOrthogonalEnd
          (𝕜 := ℂ) (E := E) cutoff U T).charpoly.IsRoot μ := by
  rw [subspaceProjectionRecovery_blockDiagonal_charpoly_eq_mul_charpoly_blocks
      (𝕜 := ℂ) (E := E) cutoff U T]
  simpa using
    (Polynomial.root_mul
      (p := (subspaceProjectionRecovery_blockSubspaceEnd
        (𝕜 := ℂ) (E := E) cutoff U T).charpoly)
      (q := (subspaceProjectionRecovery_blockOrthogonalEnd
        (𝕜 := ℂ) (E := E) cutoff U T).charpoly)
      (a := μ))

theorem subspaceProjectionRecovery_blockDiagonal_mem_spectrum_iff
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (T : Module.End ℂ E) (μ : ℂ) :
    μ ∈ spectrum ℂ
        (subspaceProjectionRecovery_blockDiagonal_operatorEnd
          (𝕜 := ℂ) (E := E) cutoff U T) ↔
      μ ∈ spectrum ℂ
          (subspaceProjectionRecovery_blockSubspaceEnd
            (𝕜 := ℂ) (E := E) cutoff U T) ∨
        μ ∈ spectrum ℂ
          (subspaceProjectionRecovery_blockOrthogonalEnd
            (𝕜 := ℂ) (E := E) cutoff U T) := by
  rw [Module.End.mem_spectrum_iff_isRoot_charpoly,
    subspaceProjectionRecovery_blockDiagonal_charpoly_root_iff (E := E) cutoff U T μ,
    Module.End.mem_spectrum_iff_isRoot_charpoly,
    Module.End.mem_spectrum_iff_isRoot_charpoly]

theorem subspaceProjectionRecovery_blockDiagonal_hasEigenvalue_iff
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (T : Module.End ℂ E) (μ : ℂ) :
    (subspaceProjectionRecovery_blockDiagonal_operatorEnd
        (𝕜 := ℂ) (E := E) cutoff U T).HasEigenvalue μ ↔
      (subspaceProjectionRecovery_blockSubspaceEnd
          (𝕜 := ℂ) (E := E) cutoff U T).HasEigenvalue μ ∨
        (subspaceProjectionRecovery_blockOrthogonalEnd
          (𝕜 := ℂ) (E := E) cutoff U T).HasEigenvalue μ := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly,
    subspaceProjectionRecovery_blockDiagonal_charpoly_root_iff (E := E) cutoff U T μ,
    Module.End.hasEigenvalue_iff_isRoot_charpoly,
    Module.End.hasEigenvalue_iff_isRoot_charpoly]

theorem subspaceProjectionRecovery_blockDiagonal_mem_spectrum_of_subspace
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (T : Module.End ℂ E) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ
      (subspaceProjectionRecovery_blockSubspaceEnd
        (𝕜 := ℂ) (E := E) cutoff U T)) :
    μ ∈ spectrum ℂ
      (subspaceProjectionRecovery_blockDiagonal_operatorEnd
        (𝕜 := ℂ) (E := E) cutoff U T) := by
  exact
    (subspaceProjectionRecovery_blockDiagonal_mem_spectrum_iff
      (E := E) cutoff U T μ).2 (Or.inl hμ)

theorem subspaceProjectionRecovery_blockDiagonal_mem_spectrum_of_orthogonal
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (T : Module.End ℂ E) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ
      (subspaceProjectionRecovery_blockOrthogonalEnd
        (𝕜 := ℂ) (E := E) cutoff U T)) :
    μ ∈ spectrum ℂ
      (subspaceProjectionRecovery_blockDiagonal_operatorEnd
        (𝕜 := ℂ) (E := E) cutoff U T) := by
  exact
    (subspaceProjectionRecovery_blockDiagonal_mem_spectrum_iff
      (E := E) cutoff U T μ).2 (Or.inr hμ)

theorem subspaceProjectionRecovery_blockDiagonal_hasEigenvalue_of_subspace
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (T : Module.End ℂ E) {μ : ℂ}
    (hμ : (subspaceProjectionRecovery_blockSubspaceEnd
      (𝕜 := ℂ) (E := E) cutoff U T).HasEigenvalue μ) :
    (subspaceProjectionRecovery_blockDiagonal_operatorEnd
      (𝕜 := ℂ) (E := E) cutoff U T).HasEigenvalue μ := by
  exact
    (subspaceProjectionRecovery_blockDiagonal_hasEigenvalue_iff
      (E := E) cutoff U T μ).2 (Or.inl hμ)

theorem subspaceProjectionRecovery_blockDiagonal_hasEigenvalue_of_orthogonal
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (T : Module.End ℂ E) {μ : ℂ}
    (hμ : (subspaceProjectionRecovery_blockOrthogonalEnd
      (𝕜 := ℂ) (E := E) cutoff U T).HasEigenvalue μ) :
    (subspaceProjectionRecovery_blockDiagonal_operatorEnd
      (𝕜 := ℂ) (E := E) cutoff U T).HasEigenvalue μ := by
  exact
    (subspaceProjectionRecovery_blockDiagonal_hasEigenvalue_iff
      (E := E) cutoff U T μ).2 (Or.inr hμ)

end CoherenceCalculusMathlibBridge
