import CoherenceCalculusMathlibBridge.TopologicalBattery

namespace CoherenceCalculusMathlibBridge

open Filter
open CoherenceCalculus
open scoped Topology

def stabilizedProjection
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) :
    Nat → BoundedEndo 𝕜 E
  | n => if cutoff ≤ n then ContinuousLinearMap.id 𝕜 E else 0

theorem stabilizedProjection_eventuallyEq
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (x : E) :
    EventuallyEqAtTop
      (fun n => stabilizedProjection (𝕜 := 𝕜) (E := E) cutoff n x)
      x := by
  rw [EventuallyEqAtTop, Filter.eventually_atTop]
  refine ⟨cutoff, ?_⟩
  intro n hn
  simp [stabilizedProjection, hn]

def stabilizedIdentityProjectionTower
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) :
    AbstractHilbertProjectionTower 𝕜 E where
  projection := stabilizedProjection (𝕜 := 𝕜) (E := E) cutoff
  faithful := stabilizedProjection_eventuallyEq (𝕜 := 𝕜) (E := E) cutoff
  nested := True
  orthogonal := True

theorem stabilizedIdentityProjectionTower_tendsto_nhds
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (x : E) :
    Tendsto
      (fun n => stabilizedIdentityProjectionTower (𝕜 := 𝕜) (E := E) cutoff |>.projection n x)
      atTop
      (𝓝 x) := by
  exact (stabilizedIdentityProjectionTower cutoff).projection_tendsto_nhds x

theorem stabilizedIdentityProjectionTower_cauchySeq
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (x : E) :
    CauchySeq
      (fun n => stabilizedIdentityProjectionTower (𝕜 := 𝕜) (E := E) cutoff |>.projection n x) := by
  exact (stabilizedIdentityProjectionTower cutoff).projection_cauchySeq x

def stabilizedObserved
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (operator : BoundedEndo 𝕜 E) :
    Nat → BoundedEndo 𝕜 E
  | n => if cutoff ≤ n then operator else 0

def stabilizedDefect
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (operator : BoundedEndo 𝕜 E) :
    Nat → BoundedEndo 𝕜 E
  | n => if cutoff ≤ n then 0 else operator

theorem stabilizedObserved_eventuallyEq
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (operator : BoundedEndo 𝕜 E) (x : E) :
    EventuallyEqAtTop
      (fun n => stabilizedObserved (𝕜 := 𝕜) (E := E) cutoff operator n x)
      (operator x) := by
  rw [EventuallyEqAtTop, Filter.eventually_atTop]
  refine ⟨cutoff, ?_⟩
  intro n hn
  simp [stabilizedObserved, hn]

theorem stabilizedDefect_eventuallyEq_zero
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (operator : BoundedEndo 𝕜 E) (x : E) :
    EventuallyEqAtTop
      (fun n => stabilizedDefect (𝕜 := 𝕜) (E := E) cutoff operator n x)
      0 := by
  rw [EventuallyEqAtTop, Filter.eventually_atTop]
  refine ⟨cutoff, ?_⟩
  intro n hn
  simp [stabilizedDefect, hn]

def stabilizedOperatorRecovery
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (operator : BoundedEndo 𝕜 E) :
    AbstractHilbertRecovery 𝕜 E where
  tower := stabilizedIdentityProjectionTower cutoff
  domain := fun _ => True
  operator := operator
  observed := stabilizedObserved (𝕜 := 𝕜) (E := E) cutoff operator
  defect := stabilizedDefect (𝕜 := 𝕜) (E := E) cutoff operator
  domain_stable := by
    intro n x hx
    trivial
  defect_vanishes := by
    intro x hx
    exact stabilizedDefect_eventuallyEq_zero (𝕜 := 𝕜) (E := E) cutoff operator x
  observed_recovers := by
    intro x hx
    exact stabilizedObserved_eventuallyEq (𝕜 := 𝕜) (E := E) cutoff operator x

theorem stabilizedOperatorRecovery_observed_tendsto_nhds
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (operator : BoundedEndo 𝕜 E) (x : E) :
    Tendsto
      (fun n => stabilizedOperatorRecovery (𝕜 := 𝕜) (E := E) cutoff operator |>.observed n x)
      atTop
      (𝓝 (operator x)) := by
  exact (stabilizedOperatorRecovery cutoff operator).observed_tendsto_nhds_operator trivial

theorem stabilizedOperatorRecovery_defect_tendsto_nhds_zero
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (cutoff : Nat) (operator : BoundedEndo 𝕜 E) (x : E) :
    Tendsto
      (fun n => stabilizedOperatorRecovery (𝕜 := 𝕜) (E := E) cutoff operator |>.defect n x)
      atTop
      (𝓝 0) := by
  exact (stabilizedOperatorRecovery cutoff operator).defect_tendsto_nhds_zero trivial

def constantObservedFamily
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (law : BoundedEndo 𝕜 E) :
    DiscreteRealizedLawFamily where
  Realization := fun _ => PUnit
  Observed := fun _ => E
  horizon := fun n => n
  realization := fun _ => PUnit.unit
  law := fun _ => law

def constantContinuumModel
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (law : BoundedEndo 𝕜 E) :
    AbstractContinuumReconstructionModel 𝕜 E E where
  family := constantObservedFamily law
  embed := fun u => u
  sample := fun _ u => u
  reconstruct := fun _ y => y
  reconstruct_sample := by
    intro u
    exact Filter.Eventually.of_forall (fun _ => rfl)

theorem constantContinuumLaw_consistent
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (law : BoundedEndo 𝕜 E) :
    AsymptoticConsistency
      (constantContinuumModel (𝕜 := 𝕜) (E := E) law).family
      (constantContinuumModel (𝕜 := 𝕜) (E := E) law).toDatum
      law := by
  intro u
  exact Filter.Eventually.of_forall (fun _ => rfl)

theorem constantContinuumLaw_tendsto_nhds
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (law : BoundedEndo 𝕜 E) (u : E) :
    Tendsto
      (fun n =>
        (constantContinuumModel (𝕜 := 𝕜) (E := E) law).reconstruct n
          ((constantContinuumModel (𝕜 := 𝕜) (E := E) law).family.law n
            ((constantContinuumModel (𝕜 := 𝕜) (E := E) law).sample n u)))
      atTop
      (𝓝 (law u)) := by
  exact
    (constantContinuumModel law).consistent_tendsto_nhds
      law
      (constantContinuumLaw_consistent law)
      u

theorem constantContinuumLaw_cauchySeq
    {𝕜 E : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (law : BoundedEndo 𝕜 E) (u : E) :
    CauchySeq
      (fun n =>
        (constantContinuumModel (𝕜 := 𝕜) (E := E) law).reconstruct n
          ((constantContinuumModel (𝕜 := 𝕜) (E := E) law).family.law n
            ((constantContinuumModel (𝕜 := 𝕜) (E := E) law).sample n u))) := by
  exact
    (constantContinuumModel law).consistent_cauchySeq
      law
      (constantContinuumLaw_consistent law)
      u

end CoherenceCalculusMathlibBridge
