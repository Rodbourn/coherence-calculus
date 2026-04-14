import CoherenceCalculusMathlibBridge.TopologyValidation
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

namespace CoherenceCalculusMathlibBridge

open Filter
open CoherenceCalculus
open scoped Topology

/--
Concrete recovery model obtained by using the star projection onto a complete
subspace as the observed operator, over the stabilized identity tower.
-/
noncomputable def subspaceProjectionRecovery
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    AbstractHilbertRecovery 𝕜 E :=
  stabilizedOperatorRecovery (𝕜 := 𝕜) (E := E) cutoff U.starProjection

noncomputable def subspaceProjectionObservedSequence
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (x : E) :
    Nat → E :=
  fun n => subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U |>.observed n x

noncomputable def subspaceProjectionDefectSequence
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (x : E) :
    Nat → E :=
  fun n => subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U |>.defect n x

theorem subspaceProjection_operator_isSelfAdjoint
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    IsSelfAdjoint U.starProjection := by
  exact isSelfAdjoint_starProjection (U := U)

theorem subspaceProjection_operator_isStarProjection
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    IsStarProjection U.starProjection := by
  exact isStarProjection_starProjection (U := U)

theorem subspaceProjection_decomposition
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (x : E) :
    U.starProjection x + Uᗮ.starProjection x = x := by
  exact Submodule.starProjection_add_starProjection_orthogonal (K := U) x

theorem subspaceProjection_norm_sq_decomposition
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (x : E) :
    ‖x‖ ^ 2 = ‖U.starProjection x‖ ^ 2 + ‖Uᗮ.starProjection x‖ ^ 2 := by
  simpa using Submodule.norm_sq_eq_add_norm_sq_starProjection (x := x) (S := U)

theorem subspaceProjection_mem_iff_norm
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (x : E) :
    x ∈ U ↔ ‖U.starProjection x‖ = ‖x‖ := by
  simpa using Submodule.mem_iff_norm_starProjection (U := U) x

theorem subspaceProjectionRecovery_observed_limit_eq
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (x : E) :
    ∃ y : E,
      Tendsto
          (subspaceProjectionObservedSequence (𝕜 := 𝕜) (E := E) cutoff U x)
          atTop
          (𝓝 y) ∧
        y = U.starProjection x := by
  simpa [subspaceProjectionObservedSequence, subspaceProjectionRecovery] using
    stabilizedObservedSequence_complete_limit_eq
      (𝕜 := 𝕜) (E := E) cutoff U.starProjection x

theorem subspaceProjectionRecovery_defect_limit_eq_zero
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (x : E) :
    ∃ y : E,
      Tendsto
          (subspaceProjectionDefectSequence (𝕜 := 𝕜) (E := E) cutoff U x)
          atTop
          (𝓝 y) ∧
        y = 0 := by
  simpa [subspaceProjectionDefectSequence, subspaceProjectionRecovery] using
    stabilizedDefectSequence_complete_limit_eq_zero
      (𝕜 := 𝕜) (E := E) cutoff U.starProjection x

theorem subspaceProjectionObservedSequence_subseq_cauchy
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (x : E) (phi : Nat → Nat) (hphi : Function.Injective phi) :
    CauchySeq (subspaceProjectionObservedSequence (𝕜 := 𝕜) (E := E) cutoff U x ∘ phi) := by
  have hC :
      CauchySeq (subspaceProjectionObservedSequence (𝕜 := 𝕜) (E := E) cutoff U x) := by
    simpa [subspaceProjectionObservedSequence, subspaceProjectionRecovery] using
      (subspaceProjectionRecovery (𝕜 := 𝕜) (E := E) cutoff U).observed_cauchySeq
        (x := x) trivial
  simpa [Function.comp] using hC.comp_injective hphi

end CoherenceCalculusMathlibBridge
