import CoherenceCalculusMathlibBridge.ContinuumBattery
import Mathlib.Topology.UniformSpace.Cauchy

namespace CoherenceCalculusMathlibBridge

open Filter
open CoherenceCalculus
open scoped Topology

theorem eventuallyEqAtTop_tendsto_nhds
    {X : Type _} [TopologicalSpace X]
    {f : Nat → X} {x : X}
    (h : EventuallyEqAtTop f x) :
    Tendsto f atTop (𝓝 x) := by
  exact tendsto_nhds_of_eventually_eq h

theorem eventuallyEqAtTop_cauchySeq
    {X : Type _} [UniformSpace X]
    {f : Nat → X} {x : X}
    (h : EventuallyEqAtTop f x) :
    CauchySeq f := by
  exact (eventuallyEqAtTop_tendsto_nhds h).cauchySeq

theorem AbstractHilbertProjectionTower.projection_tendsto_nhds
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (tower : AbstractHilbertProjectionTower 𝕜 E)
    (x : E) :
    Tendsto (fun n => tower.projection n x) atTop (𝓝 x) := by
  exact eventuallyEqAtTop_tendsto_nhds (tower.faithful x)

theorem AbstractHilbertProjectionTower.projection_cauchySeq
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (tower : AbstractHilbertProjectionTower 𝕜 E)
    (x : E) :
    CauchySeq (fun n => tower.projection n x) := by
  exact (tower.projection_tendsto_nhds x).cauchySeq

theorem AbstractHilbertRecovery.defect_tendsto_nhds_zero
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (data : AbstractHilbertRecovery 𝕜 E)
    {x : E} (hx : data.domain x) :
    Tendsto (fun n => data.defect n x) atTop (𝓝 0) := by
  exact tendsto_nhds_of_eventually_eq (data.defect_vanishes x hx)

theorem AbstractHilbertRecovery.defect_cauchySeq
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (data : AbstractHilbertRecovery 𝕜 E)
    {x : E} (hx : data.domain x) :
    CauchySeq (fun n => data.defect n x) := by
  exact (data.defect_tendsto_nhds_zero hx).cauchySeq

theorem AbstractHilbertRecovery.observed_tendsto_nhds_operator
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (data : AbstractHilbertRecovery 𝕜 E)
    {x : E} (hx : data.domain x) :
    Tendsto (fun n => data.observed n x) atTop (𝓝 (data.operator x)) := by
  exact tendsto_nhds_of_eventually_eq (data.observed_recovers x hx)

theorem AbstractHilbertRecovery.observed_cauchySeq
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (data : AbstractHilbertRecovery 𝕜 E)
    {x : E} (hx : data.domain x) :
    CauchySeq (fun n => data.observed n x) := by
  exact (data.observed_tendsto_nhds_operator hx).cauchySeq

theorem AbstractContinuumReconstructionModel.reconstruct_sample_tendsto_nhds
    {𝕜 E X₀ : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (model : AbstractContinuumReconstructionModel 𝕜 E X₀)
    (u : X₀) :
    Tendsto
      (fun n => model.reconstruct n (model.sample n u))
      atTop
      (𝓝 (model.embed u)) := by
  exact tendsto_nhds_of_eventually_eq (model.reconstruct_sample u)

theorem AbstractContinuumReconstructionModel.reconstruct_sample_cauchySeq
    {𝕜 E X₀ : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (model : AbstractContinuumReconstructionModel 𝕜 E X₀)
    (u : X₀) :
    CauchySeq (fun n => model.reconstruct n (model.sample n u)) := by
  exact (model.reconstruct_sample_tendsto_nhds u).cauchySeq

theorem AbstractContinuumReconstructionModel.consistent_tendsto_nhds
    {𝕜 E X₀ : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (model : AbstractContinuumReconstructionModel 𝕜 E X₀)
    (law : X₀ → E)
    (consistent : AsymptoticConsistency model.family model.toDatum law)
    (u : X₀) :
    Tendsto
      (fun n => model.reconstruct n (model.family.law n (model.sample n u)))
      atTop
      (𝓝 (law u)) := by
  exact tendsto_nhds_of_eventually_eq (consistent u)

theorem AbstractContinuumReconstructionModel.consistent_cauchySeq
    {𝕜 E X₀ : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (model : AbstractContinuumReconstructionModel 𝕜 E X₀)
    (law : X₀ → E)
    (consistent : AsymptoticConsistency model.family model.toDatum law)
    (u : X₀) :
    CauchySeq
      (fun n => model.reconstruct n (model.family.law n (model.sample n u))) := by
  exact (model.consistent_tendsto_nhds law consistent u).cauchySeq

end CoherenceCalculusMathlibBridge
