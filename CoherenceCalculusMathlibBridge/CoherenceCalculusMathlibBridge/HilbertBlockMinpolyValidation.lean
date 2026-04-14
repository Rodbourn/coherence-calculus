import CoherenceCalculusMathlibBridge.HilbertBlockSpectrumValidation
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

namespace CoherenceCalculusMathlibBridge

open CoherenceCalculus

/--
Validated Hilbert consumer slice for minimal-polynomial behavior of the
block-diagonal operator on the concrete `U ⊕ Uᗮ` decomposition.

This uses the already validated block-eigenvalue split together with mathlib's
own `hasEigenvalue_iff_isRoot` and `minpoly_dvd_charpoly` theorems.
-/
theorem subspaceProjectionRecovery_blockDiagonal_minpoly_dvd_mul_block_charpolies
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (T : Module.End ℂ E) :
    minpoly ℂ
        (subspaceProjectionRecovery_blockDiagonal_operatorEnd
          (𝕜 := ℂ) (E := E) cutoff U T) ∣
      (subspaceProjectionRecovery_blockSubspaceEnd
          (𝕜 := ℂ) (E := E) cutoff U T).charpoly *
        (subspaceProjectionRecovery_blockOrthogonalEnd
          (𝕜 := ℂ) (E := E) cutoff U T).charpoly := by
  rw [← subspaceProjectionRecovery_blockDiagonal_charpoly_eq_mul_charpoly_blocks
      (𝕜 := ℂ) (E := E) cutoff U T]
  exact LinearMap.minpoly_dvd_charpoly
    (subspaceProjectionRecovery_blockDiagonal_operatorEnd
      (𝕜 := ℂ) (E := E) cutoff U T)

theorem subspaceProjectionRecovery_blockDiagonal_minpoly_isRoot_iff
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (T : Module.End ℂ E) (μ : ℂ) :
    (minpoly ℂ
        (subspaceProjectionRecovery_blockDiagonal_operatorEnd
          (𝕜 := ℂ) (E := E) cutoff U T)).IsRoot μ ↔
      (minpoly ℂ
          (subspaceProjectionRecovery_blockSubspaceEnd
            (𝕜 := ℂ) (E := E) cutoff U T)).IsRoot μ ∨
        (minpoly ℂ
          (subspaceProjectionRecovery_blockOrthogonalEnd
            (𝕜 := ℂ) (E := E) cutoff U T)).IsRoot μ := by
  rw [← Module.End.hasEigenvalue_iff_isRoot,
    subspaceProjectionRecovery_blockDiagonal_hasEigenvalue_iff (E := E) cutoff U T μ,
    ← Module.End.hasEigenvalue_iff_isRoot,
    ← Module.End.hasEigenvalue_iff_isRoot]

theorem subspaceProjectionRecovery_blockDiagonal_minpoly_isRoot_of_subspace
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (T : Module.End ℂ E) {μ : ℂ}
    (hμ : (minpoly ℂ
      (subspaceProjectionRecovery_blockSubspaceEnd
        (𝕜 := ℂ) (E := E) cutoff U T)).IsRoot μ) :
    (minpoly ℂ
      (subspaceProjectionRecovery_blockDiagonal_operatorEnd
        (𝕜 := ℂ) (E := E) cutoff U T)).IsRoot μ := by
  exact
    (subspaceProjectionRecovery_blockDiagonal_minpoly_isRoot_iff
      (E := E) cutoff U T μ).2 (Or.inl hμ)

theorem subspaceProjectionRecovery_blockDiagonal_minpoly_isRoot_of_orthogonal
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (T : Module.End ℂ E) {μ : ℂ}
    (hμ : (minpoly ℂ
      (subspaceProjectionRecovery_blockOrthogonalEnd
        (𝕜 := ℂ) (E := E) cutoff U T)).IsRoot μ) :
    (minpoly ℂ
      (subspaceProjectionRecovery_blockDiagonal_operatorEnd
        (𝕜 := ℂ) (E := E) cutoff U T)).IsRoot μ := by
  exact
    (subspaceProjectionRecovery_blockDiagonal_minpoly_isRoot_iff
      (E := E) cutoff U T μ).2 (Or.inr hμ)

end CoherenceCalculusMathlibBridge
