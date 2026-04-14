import CoherenceCalculusMathlibBridge.HilbertRestrictionTraceValidation
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

namespace CoherenceCalculusMathlibBridge

open CoherenceCalculus

/--
Validated Hilbert consumer slice for exact `prodMap` factorization of the
block-diagonal operator on the concrete `U.starProjection` model.

This turns the `U ⊕ Uᗮ` decomposition into a genuine product-factorization
theorem, then derives determinant and characteristic-polynomial factorization
from mathlib's own `prodMap` APIs.
-/
noncomputable def subspaceProjectionRecovery_blockSubspaceEnd
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (T : Module.End 𝕜 E) :
    Module.End 𝕜 U :=
  (subspaceProjectionRecovery_blockDiagonal_operatorEnd
    (𝕜 := 𝕜) (E := E) cutoff U T).restrict
    (subspaceProjectionRecovery_blockDiagonal_mapsTo_subspace
      (𝕜 := 𝕜) (E := E) cutoff U T)

noncomputable def subspaceProjectionRecovery_blockOrthogonalEnd
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (T : Module.End 𝕜 E) :
    Module.End 𝕜 Uᗮ :=
  (subspaceProjectionRecovery_blockDiagonal_operatorEnd
    (𝕜 := 𝕜) (E := E) cutoff U T).restrict
    (subspaceProjectionRecovery_blockDiagonal_mapsTo_orthogonal
      (𝕜 := 𝕜) (E := E) cutoff U T)

theorem prodEquivOfIsCompl_conj_prodMap_eq_ofIsCompl
    {R E : Type _}
    [CommRing R] [AddCommGroup E] [Module R E]
    {p q : Submodule R E} (h : IsCompl p q)
    (φ : Module.End R p) (ψ : Module.End R q) :
    (Submodule.prodEquivOfIsCompl p q h).conj (LinearMap.prodMap φ ψ) =
      LinearMap.ofIsCompl h (p.subtype ∘ₗ φ) (q.subtype ∘ₗ ψ) := by
  ext x
  obtain ⟨a, b, rfl, _⟩ := Submodule.existsUnique_add_of_isCompl h x
  simp [LinearEquiv.conj_apply, LinearMap.ofIsCompl]

theorem subspaceProjectionRecovery_blockDiagonal_eq_conj_prodMap
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (T : Module.End 𝕜 E) :
    subspaceProjectionRecovery_blockDiagonal_operatorEnd
        (𝕜 := 𝕜) (E := E) cutoff U T =
      (U.prodEquivOfIsCompl Uᗮ
        (subspaceProjectionRecovery_operator_isCompl_orthogonal
          (𝕜 := 𝕜) (E := E) cutoff U)).conj
        (LinearMap.prodMap
          (subspaceProjectionRecovery_blockSubspaceEnd
            (𝕜 := 𝕜) (E := E) cutoff U T)
          (subspaceProjectionRecovery_blockOrthogonalEnd
            (𝕜 := 𝕜) (E := E) cutoff U T)) := by
  let hU : IsCompl U Uᗮ :=
    subspaceProjectionRecovery_operator_isCompl_orthogonal
      (𝕜 := 𝕜) (E := E) cutoff U
  let χ : Module.End 𝕜 E :=
    subspaceProjectionRecovery_blockDiagonal_operatorEnd
      (𝕜 := 𝕜) (E := E) cutoff U T
  have hof :
      LinearMap.ofIsCompl hU
          (U.subtype ∘ₗ
            subspaceProjectionRecovery_blockSubspaceEnd
              (𝕜 := 𝕜) (E := E) cutoff U T)
          ((Uᗮ).subtype ∘ₗ
            subspaceProjectionRecovery_blockOrthogonalEnd
              (𝕜 := 𝕜) (E := E) cutoff U T) =
        χ := by
    exact LinearMap.ofIsCompl_eq' hU rfl rfl
  calc
    χ =
      LinearMap.ofIsCompl hU
        (U.subtype ∘ₗ
          subspaceProjectionRecovery_blockSubspaceEnd
            (𝕜 := 𝕜) (E := E) cutoff U T)
        ((Uᗮ).subtype ∘ₗ
          subspaceProjectionRecovery_blockOrthogonalEnd
            (𝕜 := 𝕜) (E := E) cutoff U T) := by
          simpa [χ] using hof.symm
    _ =
      (U.prodEquivOfIsCompl Uᗮ hU).conj
        (LinearMap.prodMap
          (subspaceProjectionRecovery_blockSubspaceEnd
            (𝕜 := 𝕜) (E := E) cutoff U T)
          (subspaceProjectionRecovery_blockOrthogonalEnd
            (𝕜 := 𝕜) (E := E) cutoff U T)) := by
          symm
          exact prodEquivOfIsCompl_conj_prodMap_eq_ofIsCompl hU _ _

theorem subspaceProjectionRecovery_blockDiagonal_det_eq_mul_det_blocks
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (T : Module.End 𝕜 E) :
    (subspaceProjectionRecovery_blockDiagonal_operatorEnd
        (𝕜 := 𝕜) (E := E) cutoff U T).det =
      (subspaceProjectionRecovery_blockSubspaceEnd
          (𝕜 := 𝕜) (E := E) cutoff U T).det *
        (subspaceProjectionRecovery_blockOrthogonalEnd
          (𝕜 := 𝕜) (E := E) cutoff U T).det := by
  let e :=
    U.prodEquivOfIsCompl Uᗮ
      (subspaceProjectionRecovery_operator_isCompl_orthogonal
        (𝕜 := 𝕜) (E := E) cutoff U)
  rw [subspaceProjectionRecovery_blockDiagonal_eq_conj_prodMap
      (𝕜 := 𝕜) (E := E) cutoff U T]
  calc
    LinearMap.det
        (e.conj
          (LinearMap.prodMap
            (subspaceProjectionRecovery_blockSubspaceEnd
              (𝕜 := 𝕜) (E := E) cutoff U T)
            (subspaceProjectionRecovery_blockOrthogonalEnd
              (𝕜 := 𝕜) (E := E) cutoff U T))) =
      LinearMap.det
        (LinearMap.prodMap
          (subspaceProjectionRecovery_blockSubspaceEnd
            (𝕜 := 𝕜) (E := E) cutoff U T)
          (subspaceProjectionRecovery_blockOrthogonalEnd
            (𝕜 := 𝕜) (E := E) cutoff U T)) := by
          change
            LinearMap.det
                (((e : U × Uᗮ →ₗ[𝕜] E) ∘ₗ
                    LinearMap.prodMap
                      (subspaceProjectionRecovery_blockSubspaceEnd
                        (𝕜 := 𝕜) (E := E) cutoff U T)
                      (subspaceProjectionRecovery_blockOrthogonalEnd
                        (𝕜 := 𝕜) (E := E) cutoff U T)) ∘ₗ
                  (e.symm : E →ₗ[𝕜] U × Uᗮ)) =
              LinearMap.det
                (LinearMap.prodMap
                  (subspaceProjectionRecovery_blockSubspaceEnd
                    (𝕜 := 𝕜) (E := E) cutoff U T)
                  (subspaceProjectionRecovery_blockOrthogonalEnd
                    (𝕜 := 𝕜) (E := E) cutoff U T))
          exact
            LinearMap.det_conj
              (LinearMap.prodMap
                (subspaceProjectionRecovery_blockSubspaceEnd
                  (𝕜 := 𝕜) (E := E) cutoff U T)
                (subspaceProjectionRecovery_blockOrthogonalEnd
                  (𝕜 := 𝕜) (E := E) cutoff U T))
              e
    _ =
      (subspaceProjectionRecovery_blockSubspaceEnd
          (𝕜 := 𝕜) (E := E) cutoff U T).det *
        (subspaceProjectionRecovery_blockOrthogonalEnd
          (𝕜 := 𝕜) (E := E) cutoff U T).det := by
          rw [LinearMap.det_prodMap]

theorem subspaceProjectionRecovery_blockDiagonal_charpoly_eq_mul_charpoly_blocks
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (T : Module.End 𝕜 E) :
    (subspaceProjectionRecovery_blockDiagonal_operatorEnd
        (𝕜 := 𝕜) (E := E) cutoff U T).charpoly =
      (subspaceProjectionRecovery_blockSubspaceEnd
          (𝕜 := 𝕜) (E := E) cutoff U T).charpoly *
        (subspaceProjectionRecovery_blockOrthogonalEnd
          (𝕜 := 𝕜) (E := E) cutoff U T).charpoly := by
  let e :=
    U.prodEquivOfIsCompl Uᗮ
      (subspaceProjectionRecovery_operator_isCompl_orthogonal
        (𝕜 := 𝕜) (E := E) cutoff U)
  rw [subspaceProjectionRecovery_blockDiagonal_eq_conj_prodMap
      (𝕜 := 𝕜) (E := E) cutoff U T]
  calc
    (e.conj
        (LinearMap.prodMap
          (subspaceProjectionRecovery_blockSubspaceEnd
            (𝕜 := 𝕜) (E := E) cutoff U T)
          (subspaceProjectionRecovery_blockOrthogonalEnd
            (𝕜 := 𝕜) (E := E) cutoff U T))).charpoly =
      (LinearMap.prodMap
        (subspaceProjectionRecovery_blockSubspaceEnd
          (𝕜 := 𝕜) (E := E) cutoff U T)
        (subspaceProjectionRecovery_blockOrthogonalEnd
          (𝕜 := 𝕜) (E := E) cutoff U T)).charpoly := by
          simpa using
            (LinearEquiv.charpoly_conj
              e
              (LinearMap.prodMap
                (subspaceProjectionRecovery_blockSubspaceEnd
                  (𝕜 := 𝕜) (E := E) cutoff U T)
                (subspaceProjectionRecovery_blockOrthogonalEnd
                  (𝕜 := 𝕜) (E := E) cutoff U T)))
    _ =
      (subspaceProjectionRecovery_blockSubspaceEnd
          (𝕜 := 𝕜) (E := E) cutoff U T).charpoly *
        (subspaceProjectionRecovery_blockOrthogonalEnd
          (𝕜 := 𝕜) (E := E) cutoff U T).charpoly := by
          rw [LinearMap.charpoly_prodMap]

end CoherenceCalculusMathlibBridge
