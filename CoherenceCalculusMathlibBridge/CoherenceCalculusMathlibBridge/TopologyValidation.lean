import CoherenceCalculusMathlibBridge.ConcreteModels
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UniformSpace.Cauchy

namespace CoherenceCalculusMathlibBridge

open Filter
open CoherenceCalculus
open scoped Topology Uniformity

/--
Concrete sequence underlying the stabilized identity projection tower.

This is the first detached validation surface: an actual mathlib-facing sequence
on which we ask standard mathlib convergence theorems to recover the expected
limit.
-/
def stabilizedProjectionSequence
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (x : E) :
    Nat → E :=
  fun n => stabilizedIdentityProjectionTower (𝕜 := 𝕜) (E := E) cutoff |>.projection n x

theorem stabilizedProjectionSequence_tendsto_uniformity
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (x : E) :
    Tendsto
      (Prod.map
        (stabilizedProjectionSequence (𝕜 := 𝕜) (E := E) cutoff x)
        (stabilizedProjectionSequence (𝕜 := 𝕜) (E := E) cutoff x))
      atTop
      (𝓤 E) := by
  exact
    (cauchySeq_iff_tendsto).1
      (stabilizedIdentityProjectionTower_cauchySeq (𝕜 := 𝕜) (E := E) cutoff x)

theorem stabilizedProjectionSequence_subseq_cauchy
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (x : E) (phi : Nat → Nat) (hphi : Function.Injective phi) :
    CauchySeq (stabilizedProjectionSequence (𝕜 := 𝕜) (E := E) cutoff x ∘ phi) := by
  simpa [Function.comp, stabilizedProjectionSequence] using
    (stabilizedIdentityProjectionTower_cauchySeq (𝕜 := 𝕜) (E := E) cutoff x).comp_injective hphi

theorem stabilizedProjectionSequence_complete_limit_eq
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (x : E) :
    ∃ y : E,
      Tendsto (stabilizedProjectionSequence (𝕜 := 𝕜) (E := E) cutoff x) atTop (𝓝 y) ∧ y = x := by
  rcases cauchySeq_tendsto_of_complete
      (stabilizedIdentityProjectionTower_cauchySeq (𝕜 := 𝕜) (E := E) cutoff x) with
    ⟨y, hy⟩
  refine ⟨y, hy, ?_⟩
  exact
    tendsto_nhds_unique hy
      (stabilizedIdentityProjectionTower_tendsto_nhds (𝕜 := 𝕜) (E := E) cutoff x)

/-- Concrete observed sequence in the stabilized recovery model. -/
def stabilizedObservedSequence
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (operator : BoundedEndo 𝕜 E) (x : E) :
    Nat → E :=
  fun n => stabilizedOperatorRecovery (𝕜 := 𝕜) (E := E) cutoff operator |>.observed n x

theorem stabilizedObservedSequence_complete_limit_eq
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (operator : BoundedEndo 𝕜 E) (x : E) :
    ∃ y : E,
      Tendsto
          (stabilizedObservedSequence (𝕜 := 𝕜) (E := E) cutoff operator x)
          atTop
          (𝓝 y) ∧
        y = operator x := by
  have hC :
      CauchySeq (stabilizedObservedSequence (𝕜 := 𝕜) (E := E) cutoff operator x) := by
    simpa [stabilizedObservedSequence] using
      (stabilizedOperatorRecovery (𝕜 := 𝕜) (E := E) cutoff operator).observed_cauchySeq
        (x := x) trivial
  rcases cauchySeq_tendsto_of_complete hC with ⟨y, hy⟩
  refine ⟨y, hy, ?_⟩
  have hT :
      Tendsto
        (stabilizedObservedSequence (𝕜 := 𝕜) (E := E) cutoff operator x)
        atTop
        (𝓝 (operator x)) := by
    simpa [stabilizedObservedSequence] using
      stabilizedOperatorRecovery_observed_tendsto_nhds
        (𝕜 := 𝕜) (E := E) cutoff operator x
  exact tendsto_nhds_unique hy hT

/-- Concrete defect sequence in the stabilized recovery model. -/
def stabilizedDefectSequence
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (operator : BoundedEndo 𝕜 E) (x : E) :
    Nat → E :=
  fun n => stabilizedOperatorRecovery (𝕜 := 𝕜) (E := E) cutoff operator |>.defect n x

theorem stabilizedDefectSequence_complete_limit_eq_zero
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (operator : BoundedEndo 𝕜 E) (x : E) :
    ∃ y : E,
      Tendsto
          (stabilizedDefectSequence (𝕜 := 𝕜) (E := E) cutoff operator x)
          atTop
          (𝓝 y) ∧
        y = 0 := by
  have hC :
      CauchySeq (stabilizedDefectSequence (𝕜 := 𝕜) (E := E) cutoff operator x) := by
    simpa [stabilizedDefectSequence] using
      (stabilizedOperatorRecovery (𝕜 := 𝕜) (E := E) cutoff operator).defect_cauchySeq
        (x := x) trivial
  rcases cauchySeq_tendsto_of_complete hC with ⟨y, hy⟩
  refine ⟨y, hy, ?_⟩
  have hT :
      Tendsto
        (stabilizedDefectSequence (𝕜 := 𝕜) (E := E) cutoff operator x)
        atTop
        (𝓝 (0 : E)) := by
    simpa [stabilizedDefectSequence] using
      stabilizedOperatorRecovery_defect_tendsto_nhds_zero
        (𝕜 := 𝕜) (E := E) cutoff operator x
  exact tendsto_nhds_unique hy hT

/-- Concrete continuum sequence in the constant observed-law model. -/
def constantContinuumSequence
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (law : BoundedEndo 𝕜 E) (u : E) :
    Nat → E :=
  fun n =>
    (constantContinuumModel (𝕜 := 𝕜) (E := E) law).reconstruct n
      ((constantContinuumModel (𝕜 := 𝕜) (E := E) law).family.law n
        ((constantContinuumModel (𝕜 := 𝕜) (E := E) law).sample n u))

theorem constantContinuumSequence_tendsto_uniformity
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (law : BoundedEndo 𝕜 E) (u : E) :
    Tendsto
      (Prod.map
        (constantContinuumSequence (𝕜 := 𝕜) (E := E) law u)
        (constantContinuumSequence (𝕜 := 𝕜) (E := E) law u))
      atTop
      (𝓤 E) := by
  exact
    (cauchySeq_iff_tendsto).1
      (constantContinuumLaw_cauchySeq (𝕜 := 𝕜) (E := E) law u)

theorem constantContinuumSequence_subseq_cauchy
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (law : BoundedEndo 𝕜 E) (u : E) (phi : Nat → Nat) (hphi : Function.Injective phi) :
    CauchySeq (constantContinuumSequence (𝕜 := 𝕜) (E := E) law u ∘ phi) := by
  simpa [Function.comp, constantContinuumSequence] using
    (constantContinuumLaw_cauchySeq (𝕜 := 𝕜) (E := E) law u).comp_injective hphi

theorem constantContinuumSequence_complete_limit_eq
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (law : BoundedEndo 𝕜 E) (u : E) :
    ∃ y : E,
      Tendsto (constantContinuumSequence (𝕜 := 𝕜) (E := E) law u) atTop (𝓝 y) ∧ y = law u := by
  rcases cauchySeq_tendsto_of_complete
      (constantContinuumLaw_cauchySeq (𝕜 := 𝕜) (E := E) law u) with
    ⟨y, hy⟩
  refine ⟨y, hy, ?_⟩
  exact
    tendsto_nhds_unique hy
      (constantContinuumLaw_tendsto_nhds (𝕜 := 𝕜) (E := E) law u)

end CoherenceCalculusMathlibBridge
