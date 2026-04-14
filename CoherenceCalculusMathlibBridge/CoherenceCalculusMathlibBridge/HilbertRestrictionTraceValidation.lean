import CoherenceCalculusMathlibBridge.HilbertBlockDiagonalValidation
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.LinearAlgebra.PID

namespace CoherenceCalculusMathlibBridge

open CoherenceCalculus
open DirectSum
open Module
open Set

/--
Validated Hilbert consumer slice for restriction-trace and invariant-subspace
trace laws on the concrete `U.starProjection` recovery model.

This is the first detached slice that directly uses mathlib's restriction and
internal-direct-sum trace theorems on the complement decomposition `U ⊕ Uᗮ`.
-/
def orthogonalPairFamily
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (U : Submodule 𝕜 E) :
    Bool → Submodule 𝕜 E
  | true => U
  | false => Uᗮ

theorem orthogonalPairFamily_isInternal
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    DirectSum.IsInternal (orthogonalPairFamily (𝕜 := 𝕜) (E := E) U) := by
  refine
    (DirectSum.isInternal_submodule_iff_isCompl
      (A := orthogonalPairFamily (𝕜 := 𝕜) (E := E) U)
      (i := true) (j := false) (by decide) ?_).2 ?_
  · ext b
    simp
  · simpa using U.isCompl_orthogonal_of_hasOrthogonalProjection

theorem subspaceProjectionRecovery_operatorEnd_trace_restrict_eq
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    LinearMap.trace 𝕜 U
        ((subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U).restrict
          (fun x _ => by
            rw [subspaceProjectionRecovery_operatorEnd_eq]
            exact U.starProjection_apply_mem x)) =
      LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) := by
  simpa using
    (LinearMap.trace_restrict_eq_of_forall_mem
      (R := 𝕜)
      (M := E)
      U
      (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U)
      (fun x => by
        rw [subspaceProjectionRecovery_operatorEnd_eq]
        exact U.starProjection_apply_mem x))

theorem subspaceProjectionRecovery_orthogonal_operatorEnd_trace_restrict_eq
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    LinearMap.trace 𝕜 Uᗮ
        ((subspaceProjectionRecovery_orthogonal_operatorEnd
            (𝕜 := 𝕜) (E := E) cutoff U).restrict
          (fun x _ => by
            rw [subspaceProjectionRecovery_orthogonal_operatorEnd_eq]
            exact (Uᗮ).starProjection_apply_mem x)) =
      LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_orthogonal_operatorEnd
          (𝕜 := 𝕜) (E := E) cutoff U) := by
  simpa using
    (LinearMap.trace_restrict_eq_of_forall_mem
      (R := 𝕜)
      (M := E)
      Uᗮ
      (subspaceProjectionRecovery_orthogonal_operatorEnd
        (𝕜 := 𝕜) (E := E) cutoff U)
      (fun x => by
        rw [subspaceProjectionRecovery_orthogonal_operatorEnd_eq]
        exact (Uᗮ).starProjection_apply_mem x))

noncomputable def subspaceProjectionRecovery_blockDiagonal_operatorEnd
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (T : Module.End 𝕜 E) :
    Module.End 𝕜 E :=
  subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U * T *
      subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U +
    subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U * T *
      subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U

noncomputable def subspaceProjectionRecovery_offDiagonal_operatorEnd
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (T : Module.End 𝕜 E) :
    Module.End 𝕜 E :=
  subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U * T *
      subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U +
    subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U * T *
      subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U

theorem subspaceProjectionRecovery_blockDiagonal_mapsTo_subspace
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (T : Module.End 𝕜 E) :
    Set.MapsTo
      (subspaceProjectionRecovery_blockDiagonal_operatorEnd
        (𝕜 := 𝕜) (E := E) cutoff U T)
      U
      U := by
  intro x hx
  have hPx :
      subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U x = x := by
    rw [subspaceProjectionRecovery_operatorEnd_eq]
    exact (U.starProjection_eq_self_iff (v := x)).2 hx
  have hQx :
      subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U x = 0 := by
    rw [subspaceProjectionRecovery_orthogonal_operatorEnd_eq]
    exact Submodule.starProjection_orthogonal_apply_eq_zero (K := U) hx
  change
    subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U
        (T (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U x)) +
      subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U
        (T (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U x)) ∈ U
  rw [hPx, hQx, T.map_zero, map_zero, add_zero]
  rw [subspaceProjectionRecovery_operatorEnd_eq]
  exact U.starProjection_apply_mem (T x)

theorem subspaceProjectionRecovery_blockDiagonal_mapsTo_orthogonal
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (T : Module.End 𝕜 E) :
    Set.MapsTo
      (subspaceProjectionRecovery_blockDiagonal_operatorEnd
        (𝕜 := 𝕜) (E := E) cutoff U T)
      Uᗮ
      Uᗮ := by
  intro x hx
  have hPx :
      subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U x = 0 := by
    rw [subspaceProjectionRecovery_operatorEnd_eq]
    exact (Submodule.starProjection_apply_eq_zero_iff (K := U)).2 hx
  have hQx :
      subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U x = x := by
    rw [subspaceProjectionRecovery_orthogonal_operatorEnd_eq]
    exact ((Uᗮ).starProjection_eq_self_iff (v := x)).2 hx
  change
    subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U
        (T (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U x)) +
      subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U
        (T (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U x)) ∈ Uᗮ
  rw [hPx, hQx, T.map_zero, map_zero, zero_add]
  rw [subspaceProjectionRecovery_orthogonal_operatorEnd_eq]
  exact (Uᗮ).starProjection_apply_mem (T x)

theorem subspaceProjectionRecovery_blockDiagonal_trace_eq_sum_trace_restrict
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (T : Module.End 𝕜 E) :
    LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_blockDiagonal_operatorEnd
          (𝕜 := 𝕜) (E := E) cutoff U T) =
      LinearMap.trace 𝕜 U
          ((subspaceProjectionRecovery_blockDiagonal_operatorEnd
              (𝕜 := 𝕜) (E := E) cutoff U T).restrict
            (subspaceProjectionRecovery_blockDiagonal_mapsTo_subspace
              (𝕜 := 𝕜) (E := E) cutoff U T)) +
        LinearMap.trace 𝕜 Uᗮ
          ((subspaceProjectionRecovery_blockDiagonal_operatorEnd
              (𝕜 := 𝕜) (E := E) cutoff U T).restrict
            (subspaceProjectionRecovery_blockDiagonal_mapsTo_orthogonal
              (𝕜 := 𝕜) (E := E) cutoff U T)) := by
  let A : Bool → Submodule 𝕜 E := orthogonalPairFamily (𝕜 := 𝕜) (E := E) U
  have hInternal :
      DirectSum.IsInternal A := orthogonalPairFamily_isInternal (𝕜 := 𝕜) (E := E) U
  have hMaps :
      ∀ b,
        Set.MapsTo
          (subspaceProjectionRecovery_blockDiagonal_operatorEnd
            (𝕜 := 𝕜) (E := E) cutoff U T)
          (A b)
          (A b) := by
    intro b
    cases b <;> simp [A, orthogonalPairFamily,
      subspaceProjectionRecovery_blockDiagonal_mapsTo_subspace,
      subspaceProjectionRecovery_blockDiagonal_mapsTo_orthogonal]
  simpa [A, orthogonalPairFamily, add_comm] using
    (LinearMap.trace_eq_sum_trace_restrict
      (R := 𝕜)
      (M := E)
      (ι := Bool)
      (N := A)
      hInternal
      hMaps)

theorem subspaceProjectionRecovery_offDiagonal_mapsTo_flip
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (T : Module.End 𝕜 E) (b : Bool) :
    Set.MapsTo
      (subspaceProjectionRecovery_offDiagonal_operatorEnd
        (𝕜 := 𝕜) (E := E) cutoff U T)
      (orthogonalPairFamily (𝕜 := 𝕜) (E := E) U b)
      (orthogonalPairFamily (𝕜 := 𝕜) (E := E) U (!b)) := by
  cases b
  · intro x hx
    have hPx :
        subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U x = 0 := by
      rw [subspaceProjectionRecovery_operatorEnd_eq]
      exact (Submodule.starProjection_apply_eq_zero_iff (K := U)).2 hx
    have hQx :
        subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U x = x := by
      rw [subspaceProjectionRecovery_orthogonal_operatorEnd_eq]
      exact ((Uᗮ).starProjection_eq_self_iff (v := x)).2 hx
    change
      subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U
          (T (subspaceProjectionRecovery_orthogonal_operatorEnd
            (𝕜 := 𝕜) (E := E) cutoff U x)) +
        subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U
          (T (subspaceProjectionRecovery_operatorEnd
            (𝕜 := 𝕜) (E := E) cutoff U x)) ∈ U
    rw [hPx, hQx, T.map_zero, map_zero, add_zero]
    rw [subspaceProjectionRecovery_operatorEnd_eq]
    exact U.starProjection_apply_mem (T x)
  · intro x hx
    have hPx :
        subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U x = x := by
      rw [subspaceProjectionRecovery_operatorEnd_eq]
      exact (U.starProjection_eq_self_iff (v := x)).2 hx
    have hQx :
        subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U x = 0 := by
      rw [subspaceProjectionRecovery_orthogonal_operatorEnd_eq]
      exact Submodule.starProjection_orthogonal_apply_eq_zero (K := U) hx
    change
      subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U
          (T (subspaceProjectionRecovery_orthogonal_operatorEnd
            (𝕜 := 𝕜) (E := E) cutoff U x)) +
        subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U
          (T (subspaceProjectionRecovery_operatorEnd
            (𝕜 := 𝕜) (E := E) cutoff U x)) ∈ Uᗮ
    rw [hPx, hQx, T.map_zero, map_zero, zero_add]
    rw [subspaceProjectionRecovery_orthogonal_operatorEnd_eq]
    exact (Uᗮ).starProjection_apply_mem (T x)

theorem subspaceProjectionRecovery_offDiagonal_trace_eq_zero
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (T : Module.End 𝕜 E) :
    LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_offDiagonal_operatorEnd
          (𝕜 := 𝕜) (E := E) cutoff U T) =
      0 := by
  let A : Bool → Submodule 𝕜 E := orthogonalPairFamily (𝕜 := 𝕜) (E := E) U
  have hInternal :
      DirectSum.IsInternal A := orthogonalPairFamily_isInternal (𝕜 := 𝕜) (E := E) U
  exact
    LinearMap.trace_eq_zero_of_mapsTo_ne
      (R := 𝕜)
      (M := E)
      (ι := Bool)
      (N := A)
      hInternal
      (!·)
      (by intro b; cases b <;> simp)
      (fun b => by
        simpa [A, orthogonalPairFamily] using
          subspaceProjectionRecovery_offDiagonal_mapsTo_flip
            (𝕜 := 𝕜) (E := E) cutoff U T b)

end CoherenceCalculusMathlibBridge
