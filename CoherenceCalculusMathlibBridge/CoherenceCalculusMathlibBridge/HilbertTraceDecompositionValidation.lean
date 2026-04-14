import CoherenceCalculusMathlibBridge.HilbertTraceRankValidation

namespace CoherenceCalculusMathlibBridge

open CoherenceCalculus
open Module

/--
Validated Hilbert consumer slice for trace decomposition across the concrete
projected and orthogonal projected pieces of the `U.starProjection` model.
-/
theorem subspaceProjectionRecovery_operator_trace_mul_comm
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (T : Module.End 𝕜 E) :
    LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U * T) =
      LinearMap.trace 𝕜 E
        (T * subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) := by
  simpa using
    (LinearMap.trace_mul_comm
      (R := 𝕜)
      (f := subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U)
      (g := T))

theorem subspaceProjectionRecovery_orthogonal_operator_trace_mul_comm
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (T : Module.End 𝕜 E) :
    LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_orthogonal_operatorEnd
          (𝕜 := 𝕜) (E := E) cutoff U * T) =
      LinearMap.trace 𝕜 E
        (T * subspaceProjectionRecovery_orthogonal_operatorEnd
          (𝕜 := 𝕜) (E := E) cutoff U) := by
  simpa using
    (LinearMap.trace_mul_comm
      (R := 𝕜)
      (f := subspaceProjectionRecovery_orthogonal_operatorEnd
        (𝕜 := 𝕜) (E := E) cutoff U)
      (g := T))

theorem subspaceProjectionRecovery_trace_left_split
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (T : Module.End 𝕜 E) :
    LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U * T) +
      LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_orthogonal_operatorEnd
          (𝕜 := 𝕜) (E := E) cutoff U * T) =
      LinearMap.trace 𝕜 E T := by
  have hsum :=
    subspaceProjectionRecovery_operatorEnd_add_orthogonal_eq_one
      (𝕜 := 𝕜) (E := E) cutoff U
  calc
    LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U * T) +
        LinearMap.trace 𝕜 E
          (subspaceProjectionRecovery_orthogonal_operatorEnd
            (𝕜 := 𝕜) (E := E) cutoff U * T) =
      LinearMap.trace 𝕜 E
        ((subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U * T) +
          (subspaceProjectionRecovery_orthogonal_operatorEnd
            (𝕜 := 𝕜) (E := E) cutoff U * T)) := by
          rw [← map_add]
    _ = LinearMap.trace 𝕜 E
          ((subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U +
              subspaceProjectionRecovery_orthogonal_operatorEnd
                (𝕜 := 𝕜) (E := E) cutoff U) * T) := by
          rw [add_mul]
    _ = LinearMap.trace 𝕜 E T := by rw [hsum, one_mul]

theorem subspaceProjectionRecovery_trace_right_split
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (T : Module.End 𝕜 E) :
    LinearMap.trace 𝕜 E
        (T * subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) +
      LinearMap.trace 𝕜 E
        (T * subspaceProjectionRecovery_orthogonal_operatorEnd
          (𝕜 := 𝕜) (E := E) cutoff U) =
      LinearMap.trace 𝕜 E T := by
  have hsum :=
    subspaceProjectionRecovery_operatorEnd_add_orthogonal_eq_one
      (𝕜 := 𝕜) (E := E) cutoff U
  calc
    LinearMap.trace 𝕜 E
        (T * subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) +
        LinearMap.trace 𝕜 E
          (T * subspaceProjectionRecovery_orthogonal_operatorEnd
            (𝕜 := 𝕜) (E := E) cutoff U) =
      LinearMap.trace 𝕜 E
        ((T * subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) +
          (T * subspaceProjectionRecovery_orthogonal_operatorEnd
            (𝕜 := 𝕜) (E := E) cutoff U)) := by
          rw [← map_add]
    _ = LinearMap.trace 𝕜 E
          (T *
            (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U +
              subspaceProjectionRecovery_orthogonal_operatorEnd
                (𝕜 := 𝕜) (E := E) cutoff U)) := by
          rw [mul_add]
    _ = LinearMap.trace 𝕜 E T := by rw [hsum, mul_one]

theorem subspaceProjectionRecovery_trace_operator_mul_orthogonal_eq_zero
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (T : Module.End 𝕜 E) :
    LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U * T *
          subspaceProjectionRecovery_orthogonal_operatorEnd
            (𝕜 := 𝕜) (E := E) cutoff U) =
      0 := by
  calc
    LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U * T *
          subspaceProjectionRecovery_orthogonal_operatorEnd
            (𝕜 := 𝕜) (E := E) cutoff U) =
      LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_orthogonal_operatorEnd
          (𝕜 := 𝕜) (E := E) cutoff U *
          (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U * T)) := by
          simpa [mul_assoc] using
            (LinearMap.trace_mul_comm
              (R := 𝕜)
              (f := subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U * T)
              (g := subspaceProjectionRecovery_orthogonal_operatorEnd
                (𝕜 := 𝕜) (E := E) cutoff U))
    _ = 0 := by
          have hz :
              subspaceProjectionRecovery_orthogonal_operatorEnd
                  (𝕜 := 𝕜) (E := E) cutoff U *
                (subspaceProjectionRecovery_operatorEnd
                    (𝕜 := 𝕜) (E := E) cutoff U * T) =
              0 := by
            rw [← mul_assoc,
              subspaceProjectionRecovery_orthogonal_operatorEnd_mul_operator_eq_zero
                (𝕜 := 𝕜) (E := E) cutoff U,
              zero_mul]
          simpa [hz]

theorem subspaceProjectionRecovery_trace_orthogonal_mul_operator_eq_zero
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (T : Module.End 𝕜 E) :
    LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_orthogonal_operatorEnd
            (𝕜 := 𝕜) (E := E) cutoff U * T *
          subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) =
      0 := by
  calc
    LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_orthogonal_operatorEnd
            (𝕜 := 𝕜) (E := E) cutoff U * T *
          subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) =
      LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U *
          (subspaceProjectionRecovery_orthogonal_operatorEnd
            (𝕜 := 𝕜) (E := E) cutoff U * T)) := by
          simpa [mul_assoc] using
            (LinearMap.trace_mul_comm
              (R := 𝕜)
              (f := subspaceProjectionRecovery_orthogonal_operatorEnd
                (𝕜 := 𝕜) (E := E) cutoff U * T)
              (g := subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U))
    _ = 0 := by
          have hz :
              subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U *
                (subspaceProjectionRecovery_orthogonal_operatorEnd
                    (𝕜 := 𝕜) (E := E) cutoff U * T) =
              0 := by
            rw [← mul_assoc,
              subspaceProjectionRecovery_operatorEnd_mul_orthogonal_eq_zero
                (𝕜 := 𝕜) (E := E) cutoff U,
              zero_mul]
          simpa [hz]

theorem subspaceProjectionRecovery_trace_diagonal_split
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (T : Module.End 𝕜 E) :
    LinearMap.trace 𝕜 E T =
      LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U * T *
          subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) +
      LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_orthogonal_operatorEnd
            (𝕜 := 𝕜) (E := E) cutoff U * T *
          subspaceProjectionRecovery_orthogonal_operatorEnd
            (𝕜 := 𝕜) (E := E) cutoff U) := by
  have hPIdem :
      IsIdempotentElem
        (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) :=
    (subspaceProjectionRecovery_operator_isProj (𝕜 := 𝕜) (E := E) cutoff U).isIdempotentElem
  have hQIdem :
      IsIdempotentElem
        (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) :=
    (subspaceProjectionRecovery_orthogonal_operator_isProj (𝕜 := 𝕜) (E := E) cutoff U).isIdempotentElem
  have hP :
      LinearMap.trace 𝕜 E
          (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U * T *
            subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) =
        LinearMap.trace 𝕜 E
          (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U * T) := by
    calc
      LinearMap.trace 𝕜 E
          (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U * T *
            subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) =
        LinearMap.trace 𝕜 E
          (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U *
            (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U * T)) := by
            simpa [mul_assoc] using
              (LinearMap.trace_mul_comm
                (R := 𝕜)
                (f := subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U * T)
                (g := subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U))
      _ = LinearMap.trace 𝕜 E
            (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U * T) := by
            have hmul :
                subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U *
                  (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U * T) =
                subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U * T := by
              rw [← mul_assoc, hPIdem.eq]
            simpa [hmul]
  have hQ :
      LinearMap.trace 𝕜 E
          (subspaceProjectionRecovery_orthogonal_operatorEnd
              (𝕜 := 𝕜) (E := E) cutoff U * T *
            subspaceProjectionRecovery_orthogonal_operatorEnd
              (𝕜 := 𝕜) (E := E) cutoff U) =
        LinearMap.trace 𝕜 E
          (subspaceProjectionRecovery_orthogonal_operatorEnd
            (𝕜 := 𝕜) (E := E) cutoff U * T) := by
      calc
        LinearMap.trace 𝕜 E
            (subspaceProjectionRecovery_orthogonal_operatorEnd
                (𝕜 := 𝕜) (E := E) cutoff U * T *
              subspaceProjectionRecovery_orthogonal_operatorEnd
                (𝕜 := 𝕜) (E := E) cutoff U) =
        LinearMap.trace 𝕜 E
            (subspaceProjectionRecovery_orthogonal_operatorEnd
              (𝕜 := 𝕜) (E := E) cutoff U *
              (subspaceProjectionRecovery_orthogonal_operatorEnd
                (𝕜 := 𝕜) (E := E) cutoff U * T)) := by
              simpa [mul_assoc] using
                (LinearMap.trace_mul_comm
                  (R := 𝕜)
                  (f := subspaceProjectionRecovery_orthogonal_operatorEnd
                    (𝕜 := 𝕜) (E := E) cutoff U * T)
                  (g := subspaceProjectionRecovery_orthogonal_operatorEnd
                    (𝕜 := 𝕜) (E := E) cutoff U))
        _ = LinearMap.trace 𝕜 E
              (subspaceProjectionRecovery_orthogonal_operatorEnd
                (𝕜 := 𝕜) (E := E) cutoff U * T) := by
              have hmul :
                  subspaceProjectionRecovery_orthogonal_operatorEnd
                      (𝕜 := 𝕜) (E := E) cutoff U *
                    (subspaceProjectionRecovery_orthogonal_operatorEnd
                        (𝕜 := 𝕜) (E := E) cutoff U * T) =
                  subspaceProjectionRecovery_orthogonal_operatorEnd
                    (𝕜 := 𝕜) (E := E) cutoff U * T := by
                rw [← mul_assoc, hQIdem.eq]
              simpa [hmul]
  calc
    LinearMap.trace 𝕜 E T =
      LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U * T) +
      LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_orthogonal_operatorEnd
          (𝕜 := 𝕜) (E := E) cutoff U * T) := by
            symm
            exact subspaceProjectionRecovery_trace_left_split (𝕜 := 𝕜) (E := E) cutoff U T
    _ =
      LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U * T *
          subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) +
      LinearMap.trace 𝕜 E
        (subspaceProjectionRecovery_orthogonal_operatorEnd
            (𝕜 := 𝕜) (E := E) cutoff U * T *
          subspaceProjectionRecovery_orthogonal_operatorEnd
            (𝕜 := 𝕜) (E := E) cutoff U) := by
            rw [hP, hQ]

theorem subspaceProjectionRecovery_trace_diagonal_split_right
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (cutoff : Nat) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (T : Module.End 𝕜 E) :
    LinearMap.trace 𝕜 E T =
      LinearMap.trace 𝕜 E
        (T * subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U *
          subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) +
      LinearMap.trace 𝕜 E
        (T * subspaceProjectionRecovery_orthogonal_operatorEnd
            (𝕜 := 𝕜) (E := E) cutoff U *
          subspaceProjectionRecovery_orthogonal_operatorEnd
            (𝕜 := 𝕜) (E := E) cutoff U) := by
  have hPIdem :
      IsIdempotentElem
        (subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) :=
    (subspaceProjectionRecovery_operator_isProj (𝕜 := 𝕜) (E := E) cutoff U).isIdempotentElem
  have hQIdem :
      IsIdempotentElem
        (subspaceProjectionRecovery_orthogonal_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) :=
    (subspaceProjectionRecovery_orthogonal_operator_isProj (𝕜 := 𝕜) (E := E) cutoff U).isIdempotentElem
  have hPr :
      LinearMap.trace 𝕜 E
          (T * subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U *
            subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) =
        LinearMap.trace 𝕜 E
          (T * subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) := by
    simpa [mul_assoc, hPIdem.eq]
  have hQr :
      LinearMap.trace 𝕜 E
          (T * subspaceProjectionRecovery_orthogonal_operatorEnd
              (𝕜 := 𝕜) (E := E) cutoff U *
            subspaceProjectionRecovery_orthogonal_operatorEnd
              (𝕜 := 𝕜) (E := E) cutoff U) =
        LinearMap.trace 𝕜 E
          (T * subspaceProjectionRecovery_orthogonal_operatorEnd
            (𝕜 := 𝕜) (E := E) cutoff U) := by
    simpa [mul_assoc, hQIdem.eq]
  calc
    LinearMap.trace 𝕜 E T =
      LinearMap.trace 𝕜 E
        (T * subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) +
      LinearMap.trace 𝕜 E
        (T * subspaceProjectionRecovery_orthogonal_operatorEnd
          (𝕜 := 𝕜) (E := E) cutoff U) := by
            symm
            exact subspaceProjectionRecovery_trace_right_split (𝕜 := 𝕜) (E := E) cutoff U T
    _ =
      LinearMap.trace 𝕜 E
        (T * subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U *
          subspaceProjectionRecovery_operatorEnd (𝕜 := 𝕜) (E := E) cutoff U) +
      LinearMap.trace 𝕜 E
        (T * subspaceProjectionRecovery_orthogonal_operatorEnd
            (𝕜 := 𝕜) (E := E) cutoff U *
          subspaceProjectionRecovery_orthogonal_operatorEnd
            (𝕜 := 𝕜) (E := E) cutoff U) := by
            rw [← hPr, ← hQr]

end CoherenceCalculusMathlibBridge
