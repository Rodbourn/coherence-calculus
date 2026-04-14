import CoherenceCalculus.PartIII.DerivedBridgeCore
import CoherenceCalculus.PartIV.ClosureCurrentCoordinateBridgeCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentContinuumCore

Detached continuum extension of the no-stage closure-current law.

`ClosureCurrentCoordinateBridgeCore` reduced the detached microscopic lane to
its honest no-stage discrete primitive: a local-event four-state law together
with its balanced quotient. The next step is not an endpoint representative or
carrier-level PDE. It is the Part III-type continuum extension of that
discrete law.

This file does that in the smallest clean way available on the detached lane:

* a pure four-state update map is read as a refinement-constant discrete family;
* the same construction is repeated for the reduced hidden balanced law;
* the corresponding continuum laws are forced by the existing Part III
  reconstruction and uniqueness machinery;
* the reduced hidden continuum law is recorded explicitly as the balanced
  quotient of the four-state continuum law.

Nothing here is claimed on the bedrock-certified Part I / Part II spine. This
is a detached Part IV bridge theorem layer only.
-/

namespace ClosureCurrent

/-- A pure four-state update map already determines a refinement-compatible
constant family on the explicit state carrier. -/
def StateDynamics.refinementCompatibleFamily
    (data : StateDynamics) :
    RefinementCompatibleFamily where
  family := {
    Realization := fun _ => State → State
    Observed := fun _ => State
    horizon := fun n => n
    realization := fun _ => data.step
    law := fun _ => data.step
  }
  compare := fun {_ _} _ x => x
  compare_refl := by
    intro _ _
    rfl
  compare_trans := by
    intro _ _ _ _ _ _
    rfl
  intertwines := by
    intro _ _ _ _
    rfl
  transported_data_agree := True

/-- The refinement-constant four-state family carries the identity
reconstruction datum on the explicit state carrier. -/
def StateDynamics.reconstructionDatum
    (data : StateDynamics) :
    ContinuumReconstructionDatum
      data.refinementCompatibleFamily.family
      State
      State where
  limits := bridgeEventualLimitInterface State
  embed := fun x => x
  sample := fun _ x => x
  reconstruct := fun _ x => x
  reconstruct_sample := by
    intro x
    exact bridgeEventuallyEq_of_shift (fun _ => x) x 0 (fun _ => rfl)

/-- The four-state continuum law forced by the refinement-constant family is
just the same explicit four-state update map. -/
def StateDynamics.continuumLaw
    (data : StateDynamics) :
    State → State :=
  data.step

/-- The refinement-constant four-state family is asymptotically consistent with
its explicit four-state update law exactly, not just approximately. -/
theorem StateDynamics.asymptoticConsistency
    (data : StateDynamics) :
    AsymptoticConsistency
      data.refinementCompatibleFamily.family
      data.reconstructionDatum
      data.continuumLaw := by
  intro x
  exact bridgeEventuallyEq_of_shift (fun _ => data.step x) (data.step x) 0
    (fun _ => rfl)

/-- Exact stabilized form of the refinement-constant four-state family. -/
def StateDynamics.stableDiscreteFamily
    (data : StateDynamics) :
    StableDiscreteFamily
      data.refinementCompatibleFamily.family
      data.reconstructionDatum where
  stability_witness := 0
  stable :=
    ∀ n : Nat, ∀ x : State,
      data.reconstructionDatum.reconstruct n
          (data.refinementCompatibleFamily.family.law n
            (data.reconstructionDatum.sample n x)) =
        data.continuumLaw x

/-- The refinement-constant four-state family is already exactly stable at
every stage. -/
theorem StateDynamics.stableDiscreteFamily_stable
    (data : StateDynamics) :
    data.stableDiscreteFamily.stable := by
  intro _ _
  rfl

/-- Any continuum law asymptotically consistent with the refinement-constant
four-state family agrees pointwise with the explicit four-state update map. -/
theorem StateDynamics.continuumUniqueness
    (data : StateDynamics)
    {L : State → State}
    (hL : AsymptoticConsistency
      data.refinementCompatibleFamily.family
      data.reconstructionDatum
      L) :
    ∀ x : State, L x = data.continuumLaw x := by
  exact
    (continuum_identification_on_dense_test_domain
      data.refinementCompatibleFamily.family
      data.reconstructionDatum
      hL
      data.asymptoticConsistency
      (identityContinuumSymmetryTransport
        data.refinementCompatibleFamily.family
        data.reconstructionDatum)).1

/-- Continuum laws admissible for the refinement-constant four-state family are
exactly those asymptotically consistent with the identity reconstruction
datum. -/
def StateDynamics.limitClass
    (data : StateDynamics) :
    ContinuumLimitClass (State → State) where
  admissible := AsymptoticConsistency
    data.refinementCompatibleFamily.family
    data.reconstructionDatum

/-- Strengthened stable continuum class for the four-state refinement-constant
family. -/
def StateDynamics.stableLimitClass
    (data : StateDynamics) :
    ContinuumLimitClass (State → State) where
  admissible := fun L =>
    data.stableDiscreteFamily.stable ∧
      AsymptoticConsistency
        data.refinementCompatibleFamily.family
        data.reconstructionDatum
        L

/-- The explicit four-state update map is admissible for its continuum limit
class. -/
theorem StateDynamics.continuumLaw_admissible
    (data : StateDynamics) :
    data.limitClass.admissible data.continuumLaw := by
  exact data.asymptoticConsistency

/-- Any law admissible for the four-state continuum limit class is pointwise
forced to agree with the explicit four-state update map. -/
theorem StateDynamics.limitClass_pointwise_forcing
    (data : StateDynamics)
    {other : State → State}
    (hother : data.limitClass.admissible other) :
    ∀ x : State, other x = data.continuumLaw x := by
  exact data.continuumUniqueness hother

/-- The explicit four-state update map is admissible for the strengthened
stable continuum limit class. -/
theorem StateDynamics.stableContinuumLaw_admissible
    (data : StateDynamics) :
    data.stableLimitClass.admissible data.continuumLaw := by
  exact ⟨data.stableDiscreteFamily_stable, data.asymptoticConsistency⟩

/-- Any law admissible for the strengthened stable four-state limit class is
pointwise forced to agree with the explicit four-state update map. -/
theorem StateDynamics.stableLimitClass_pointwise_forcing
    (data : StateDynamics)
    {other : State → State}
    (hother : data.stableLimitClass.admissible other) :
    ∀ x : State, other x = data.continuumLaw x := by
  exact data.continuumUniqueness hother.2

/-- The refinement-constant four-state family already forces its continuum law
on the same Part III limit-class surface used elsewhere in the bridge lane. -/
theorem StateDynamics.continuumLaw_forced
    (data : StateDynamics) :
    ForcedContinuumLaw data.limitClass data.continuumLaw := by
  exact
    discrete_to_continuum_forcing_principle
      data.limitClass
      data.continuumLaw
      data.continuumLaw_admissible
      (fun other hother => funext (data.limitClass_pointwise_forcing hother))

/-- A pure reduced hidden update map already determines a refinement-compatible
constant family on the balanced hidden carrier. -/
def ReducedObservedDynamics.hiddenRefinementCompatibleFamily
    (data : ReducedObservedDynamics) :
    RefinementCompatibleFamily where
  family := {
    Realization := fun _ => BalancedCoordinates → BalancedCoordinates
    Observed := fun _ => BalancedCoordinates
    horizon := fun n => n
    realization := fun _ => data.hiddenStep
    law := fun _ => data.hiddenStep
  }
  compare := fun {_ _} _ x => x
  compare_refl := by
    intro _ _
    rfl
  compare_trans := by
    intro _ _ _ _ _ _
    rfl
  intertwines := by
    intro _ _ _ _
    rfl
  transported_data_agree := True

/-- Identity reconstruction datum on the balanced hidden carrier for the
refinement-constant reduced hidden law. -/
def ReducedObservedDynamics.hiddenReconstructionDatum
    (data : ReducedObservedDynamics) :
    ContinuumReconstructionDatum
      data.hiddenRefinementCompatibleFamily.family
      BalancedCoordinates
      BalancedCoordinates where
  limits := bridgeEventualLimitInterface BalancedCoordinates
  embed := fun x => x
  sample := fun _ x => x
  reconstruct := fun _ x => x
  reconstruct_sample := by
    intro x
    exact bridgeEventuallyEq_of_shift (fun _ => x) x 0 (fun _ => rfl)

/-- The reduced hidden continuum law forced by the refinement-constant family
is exactly the explicit reduced hidden update map. -/
def ReducedObservedDynamics.hiddenContinuumLaw
    (data : ReducedObservedDynamics) :
    BalancedCoordinates → BalancedCoordinates :=
  data.hiddenStep

/-- The refinement-constant reduced hidden family is asymptotically consistent
with its explicit reduced hidden update map. -/
theorem ReducedObservedDynamics.hiddenAsymptoticConsistency
    (data : ReducedObservedDynamics) :
    AsymptoticConsistency
      data.hiddenRefinementCompatibleFamily.family
      data.hiddenReconstructionDatum
      data.hiddenContinuumLaw := by
  intro x
  exact bridgeEventuallyEq_of_shift
    (fun _ => data.hiddenStep x)
    (data.hiddenStep x)
    0
    (fun _ => rfl)

/-- Any continuum law asymptotically consistent with the refinement-constant
reduced hidden family agrees pointwise with the explicit reduced hidden update
map. -/
theorem ReducedObservedDynamics.hiddenContinuumUniqueness
    (data : ReducedObservedDynamics)
    {L : BalancedCoordinates → BalancedCoordinates}
    (hL : AsymptoticConsistency
      data.hiddenRefinementCompatibleFamily.family
      data.hiddenReconstructionDatum
      L) :
    ∀ x : BalancedCoordinates, L x = data.hiddenContinuumLaw x := by
  exact
    (continuum_identification_on_dense_test_domain
      data.hiddenRefinementCompatibleFamily.family
      data.hiddenReconstructionDatum
      hL
      data.hiddenAsymptoticConsistency
      (identityContinuumSymmetryTransport
        data.hiddenRefinementCompatibleFamily.family
        data.hiddenReconstructionDatum)).1

/-- Continuum limit class for the refinement-constant reduced hidden family. -/
def ReducedObservedDynamics.hiddenLimitClass
    (data : ReducedObservedDynamics) :
    ContinuumLimitClass (BalancedCoordinates → BalancedCoordinates) where
  admissible := AsymptoticConsistency
    data.hiddenRefinementCompatibleFamily.family
    data.hiddenReconstructionDatum

/-- The explicit reduced hidden update map is admissible for its continuum
limit class. -/
theorem ReducedObservedDynamics.hiddenContinuumLaw_admissible
    (data : ReducedObservedDynamics) :
    data.hiddenLimitClass.admissible data.hiddenContinuumLaw := by
  exact data.hiddenAsymptoticConsistency

/-- Any law admissible for the reduced hidden continuum limit class is
pointwise forced to agree with the explicit reduced hidden update map. -/
theorem ReducedObservedDynamics.hiddenLimitClass_pointwise_forcing
    (data : ReducedObservedDynamics)
    {other : BalancedCoordinates → BalancedCoordinates}
    (hother : data.hiddenLimitClass.admissible other) :
    ∀ x : BalancedCoordinates, other x = data.hiddenContinuumLaw x := by
  exact data.hiddenContinuumUniqueness hother

/-- The refinement-constant reduced hidden family already forces its continuum
law on the same Part III limit-class surface. -/
theorem ReducedObservedDynamics.hiddenContinuumLaw_forced
    (data : ReducedObservedDynamics) :
    ForcedContinuumLaw data.hiddenLimitClass data.hiddenContinuumLaw := by
  exact
    discrete_to_continuum_forcing_principle
      data.hiddenLimitClass
      data.hiddenContinuumLaw
      data.hiddenContinuumLaw_admissible
      (fun other hother =>
        funext (data.hiddenLimitClass_pointwise_forcing hother))

/-- The no-stage local-event four-state law already carries a forced
four-state continuum law. -/
theorem LocalEventFourStateLaw.stateContinuumLaw_forced
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ForcedContinuumLaw
      data.stateDynamics.limitClass
      data.stateDynamics.continuumLaw := by
  exact data.stateDynamics.continuumLaw_forced

/-- The no-stage local-event four-state law already carries a forced reduced
hidden continuum law on the balanced quotient carrier. -/
theorem LocalEventFourStateLaw.reducedContinuumLaw_forced
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ForcedContinuumLaw
      data.toLocalEventStateBridge.reducedDynamics.hiddenLimitClass
      data.toLocalEventStateBridge.reducedDynamics.hiddenContinuumLaw := by
  exact data.toLocalEventStateBridge.reducedDynamics.hiddenContinuumLaw_forced

/-- The reduced hidden continuum law is exactly the balanced quotient of the
four-state continuum law. -/
theorem LocalEventFourStateLaw.reducedContinuumLaw_quotient
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ∀ x : BalancedCoordinates,
      data.toLocalEventStateBridge.reducedDynamics.hiddenContinuumLaw x =
        BalancedCoordinates.projectState
          (data.stateDynamics.continuumLaw x.toState) := by
  intro x
  rfl

/-- The reduced observed readout is exactly the selected projection of the
balanced hidden carrier on the no-stage local-event four-state law. -/
theorem LocalEventFourStateLaw.observedContinuumReadout
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    ∀ x : BalancedCoordinates,
      data.toLocalEventStateBridge.reducedDynamics.observedReadout x =
        selectedProjection data.framed.object.bridge x.toState := by
  intro x
  rfl

/-- Continuum surface of the no-stage detached local-event four-state law. The
Part III reconstruction machinery already forces the explicit four-state
continuum law and the reduced hidden continuum law, and the latter is the
balanced quotient of the former. -/
theorem LocalEventFourStateLaw.continuumSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateLaw Index Time Carrier Law) :
    Nonempty (PairExchangeCurrent data.framed.object.currentCarrier data.framed.object.Leg) ∧
      data.framed.object.currentDirectReturnCompatible ∧
      data.framed.object.visiblePrimitiveReadoutAutonomous ∧
      data.framed.object.minimalVisibleQuotients ∧
      ForcedContinuumLaw
        data.stateDynamics.limitClass
        data.stateDynamics.continuumLaw ∧
      ForcedContinuumLaw
        data.toLocalEventStateBridge.reducedDynamics.hiddenLimitClass
        data.toLocalEventStateBridge.reducedDynamics.hiddenContinuumLaw ∧
      (∀ x : BalancedCoordinates,
        data.toLocalEventStateBridge.reducedDynamics.hiddenContinuumLaw x =
          BalancedCoordinates.projectState
            (data.stateDynamics.continuumLaw x.toState)) ∧
      (∀ x : BalancedCoordinates,
        data.toLocalEventStateBridge.reducedDynamics.observedReadout x =
          selectedProjection data.framed.object.bridge x.toState) := by
  obtain ⟨hcurrent, hdirret, haut, hmin, _, _, _, _, _⟩ := data.surface
  exact
    ⟨hcurrent,
      hdirret,
      haut,
      hmin,
      data.stateContinuumLaw_forced,
      data.reducedContinuumLaw_forced,
      data.reducedContinuumLaw_quotient,
      data.observedContinuumReadout⟩

end ClosureCurrent

end CoherenceCalculus
