import CoherenceCalculusMathlibBridge.HilbertPositiveValidation
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

namespace CoherenceCalculusMathlibBridge

open CoherenceCalculus

/--
Validated Hilbert consumer slice for spectral/order consequences on the concrete
`U.starProjection` recovery model.
-/
theorem subspaceProjectionRecovery_operator_spectrumRestricts
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    SpectrumRestricts
      ((subspaceProjectionRecovery (𝕜 := ℂ) (E := E) cutoff U).operator)
      ContinuousMap.realToNNReal := by
  simpa [subspaceProjectionRecovery_operator_eq] using
    (subspaceProjectionRecovery_operator_isPositive (𝕜 := ℂ) (E := E) cutoff U).spectrumRestricts

theorem subspaceProjectionRecovery_operator_spectrum_subset_zero_one
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    spectrum ℂ ((subspaceProjectionRecovery (𝕜 := ℂ) (E := E) cutoff U).operator) ⊆
      ({0, 1} : Set ℂ) := by
  simpa [subspaceProjectionRecovery_operator_eq] using
    ((U.isIdempotentElem_starProjection).spectrum_subset ℂ)

theorem subspaceProjectionRecovery_operator_spectralRadius_eq_zero_or_one
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    spectralRadius ℂ ((subspaceProjectionRecovery (𝕜 := ℂ) (E := E) cutoff U).operator) = 0 ∨
      spectralRadius ℂ ((subspaceProjectionRecovery (𝕜 := ℂ) (E := E) cutoff U).operator) = 1 := by
  obtain ⟨z, hz, hrad⟩ := spectrum.exists_nnnorm_eq_spectralRadius
    ((subspaceProjectionRecovery (𝕜 := ℂ) (E := E) cutoff U).operator)
  have hz01 : z = 0 ∨ z = 1 := by
    simpa using
      (subspaceProjectionRecovery_operator_spectrum_subset_zero_one (E := E) cutoff U hz)
  cases hz01 with
  | inl hz0 =>
      left
      simpa [hz0] using hrad.symm
  | inr hz1 =>
      right
      simpa [hz1] using hrad.symm

theorem subspaceProjectionRecovery_operator_spectralRadius_le_one
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    spectralRadius ℂ ((subspaceProjectionRecovery (𝕜 := ℂ) (E := E) cutoff U).operator) ≤ 1 := by
  obtain hrad | hrad :=
    subspaceProjectionRecovery_operator_spectralRadius_eq_zero_or_one (E := E) cutoff U
  · simp [hrad]
  · simp [hrad]

theorem subspaceProjectionRecovery_orthogonal_operator_spectrumRestricts
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    SpectrumRestricts
      (ContinuousLinearMap.id ℂ E -
        (subspaceProjectionRecovery (𝕜 := ℂ) (E := E) cutoff U).operator)
      ContinuousMap.realToNNReal := by
  have hPos : (Uᗮ.starProjection).IsPositive := by
    exact ContinuousLinearMap.IsPositive.of_isStarProjection
      (subspaceProjection_operator_isStarProjection (𝕜 := ℂ) (E := E) Uᗮ)
  simpa [subspaceProjectionRecovery_orthogonal_operator (𝕜 := ℂ) (E := E) cutoff U] using
    hPos.spectrumRestricts

theorem subspaceProjectionRecovery_orthogonal_operator_spectrum_subset_zero_one
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    spectrum ℂ
        (ContinuousLinearMap.id ℂ E -
          (subspaceProjectionRecovery (𝕜 := ℂ) (E := E) cutoff U).operator) ⊆
      ({0, 1} : Set ℂ) := by
  simpa [subspaceProjectionRecovery_orthogonal_operator (𝕜 := ℂ) (E := E) cutoff U] using
    (((Uᗮ).isIdempotentElem_starProjection).spectrum_subset ℂ)

theorem subspaceProjectionRecovery_orthogonal_operator_spectralRadius_eq_zero_or_one
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    spectralRadius ℂ
        (ContinuousLinearMap.id ℂ E -
          (subspaceProjectionRecovery (𝕜 := ℂ) (E := E) cutoff U).operator) = 0 ∨
      spectralRadius ℂ
          (ContinuousLinearMap.id ℂ E -
            (subspaceProjectionRecovery (𝕜 := ℂ) (E := E) cutoff U).operator) = 1 := by
  obtain ⟨z, hz, hrad⟩ := spectrum.exists_nnnorm_eq_spectralRadius
    (ContinuousLinearMap.id ℂ E -
      (subspaceProjectionRecovery (𝕜 := ℂ) (E := E) cutoff U).operator)
  have hz01 : z = 0 ∨ z = 1 := by
    simpa using
      (subspaceProjectionRecovery_orthogonal_operator_spectrum_subset_zero_one
        (E := E) cutoff U hz)
  cases hz01 with
  | inl hz0 =>
      left
      simpa [hz0] using hrad.symm
  | inr hz1 =>
      right
      simpa [hz1] using hrad.symm

theorem subspaceProjectionRecovery_orthogonal_operator_spectralRadius_le_one
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
    (cutoff : Nat) (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    spectralRadius ℂ
        (ContinuousLinearMap.id ℂ E -
          (subspaceProjectionRecovery (𝕜 := ℂ) (E := E) cutoff U).operator) ≤ 1 := by
  obtain hrad | hrad :=
    subspaceProjectionRecovery_orthogonal_operator_spectralRadius_eq_zero_or_one
      (E := E) cutoff U
  · simp [hrad]
  · simp [hrad]

end CoherenceCalculusMathlibBridge
