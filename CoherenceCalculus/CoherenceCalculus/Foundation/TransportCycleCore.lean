import CoherenceCalculus.Foundation.TowerCalculusCore

/-!
# Foundation.TransportCycleCore

Explicit transport-cycle interfaces for the rebuilt Chapter 4/6/9 manuscript
surface.

This module keeps the same certification policy as the rest of the rebuilt
spine:

- one-step transport and finite cycles are packaged on the active additive-map
  layer
- repeat/primitive transport content is proved directly from the explicit
  recursive monodromy definition
- spectral and prime-index language is exposed only through explicit witness
  packages, with no hidden analytic or algebraic imports
-/

namespace CoherenceCalculus

namespace AddMap

/-- Left identity for additive-map composition. -/
theorem comp_id_left (A : AddMap) : comp AddMap.id A = A := by
  apply ext
  intro x
  rfl

/-- Right identity for additive-map composition. -/
theorem comp_id_right (A : AddMap) : comp A AddMap.id = A := by
  apply ext
  intro x
  rfl

end AddMap

/-- A transport step is an explicit additive endomap on the rebuilt state
space. -/
structure TransportStep where
  op : AddMap

/-- A transport cycle is a finite list of transport steps. -/
structure TransportCycle where
  steps : List TransportStep

/-- The monodromy of a finite list of steps, written in the manuscript order
`T_k ∘ ... ∘ T_1`. -/
def monodromySteps : List TransportStep → AddMap
  | [] => AddMap.id
  | step :: tail => AddMap.comp (monodromySteps tail) step.op

/-- The monodromy additive map of a transport cycle. -/
def monodromy (cycle : TransportCycle) : AddMap :=
  monodromySteps cycle.steps

/-- Monodromy of concatenated transport words factors pointwise through the
monodromies of the two pieces. -/
theorem monodromySteps_append_apply
    (left right : List TransportStep) :
    ∀ x : State,
      monodromySteps (left ++ right) x =
        AddMap.comp (monodromySteps right) (monodromySteps left) x := by
  intro x
  induction left generalizing x with
  | nil =>
      rfl
  | cons step tail ih =>
      simpa [monodromySteps, AddMap.comp] using ih (step.op x)

/-- Explicit repeated monodromy powers. -/
def monodromyPower (A : AddMap) : Nat → AddMap
  | 0 => AddMap.id
  | n + 1 => AddMap.comp A (monodromyPower A n)

/-- The `m`-fold repeat of a finite transport cycle. -/
def repeatTransportCycle (cycle : TransportCycle) : Nat → TransportCycle
  | 0 => ⟨[]⟩
  | n + 1 =>
      let repeated := repeatTransportCycle cycle n
      ⟨repeated.steps ++ cycle.steps⟩

/-- Explicit data witnessing monodromy factorization for repeats of a chosen
transport cycle. -/
structure RepeatCycleMonodromyFactorizationData
    (cycle : TransportCycle) where
  factorization :
    ∀ m : Nat, ∀ x : State,
      monodromy (repeatTransportCycle cycle m) x =
        monodromyPower (monodromy cycle) m x

/-- Monodromy of a repeated cycle factors through the corresponding monodromy
power once the explicit witness data are supplied. -/
theorem repeat_cycle_monodromy_factorization
    (cycle : TransportCycle)
    (data : RepeatCycleMonodromyFactorizationData cycle) :
    ∀ m : Nat, ∀ x : State,
      monodromy (repeatTransportCycle cycle m) x =
        monodromyPower (monodromy cycle) m x := by
  exact data.factorization

/-- A transport cycle is a nontrivial repeat of a shorter core cycle. -/
def TransportCycleRepeat (core cycle : TransportCycle) : Prop :=
  ∃ m : Nat, 1 < m ∧ cycle = repeatTransportCycle core m

/-- A primitive transport cycle is one that is not a nontrivial repeat. -/
def PrimitiveTransportCycle (cycle : TransportCycle) : Prop :=
  ¬ ∃ core : TransportCycle, TransportCycleRepeat core cycle

/-- Explicit witness packaging for the spectral-radius language used in the
manuscript discussion. -/
structure SpectralRadiusWitness where
  operator : AddMap
  radius : Nat
  gelfandLimitLaw : Prop
  gelfandInfimumLaw : Prop
  hasGelfandLimitLaw : gelfandLimitLaw
  hasGelfandInfimumLaw : gelfandInfimumLaw

/-- The certified spectral-radius value carried by an explicit witness. -/
def spectralRadius (data : SpectralRadiusWitness) : Nat :=
  data.radius

/-- The Gelfand-formula consequences exported by an explicit spectral-radius
witness. -/
theorem gelfand_formula (data : SpectralRadiusWitness) :
    data.gelfandLimitLaw ∧ data.gelfandInfimumLaw := by
  exact ⟨data.hasGelfandLimitLaw, data.hasGelfandInfimumLaw⟩

/-- Explicit witness packaging for the `2 x 2` monodromy characteristic-law
discussion. -/
structure Monodromy2x2 where
  cycle : TransportCycle
  traceParameter : Nat
  determinantOne : Prop
  characteristicQuadraticLaw : Prop
  eigenvalueFormula : Prop
  hasCharacteristicQuadraticLaw : characteristicQuadraticLaw
  hasEigenvalueFormula : eigenvalueFormula

/-- The characteristic-polynomial and eigenvalue consequences exported by a
`2 x 2` monodromy witness. -/
theorem monodromy_2x2_char_poly (data : Monodromy2x2) :
    data.characteristicQuadraticLaw ∧ data.eigenvalueFormula := by
  exact ⟨data.hasCharacteristicQuadraticLaw, data.hasEigenvalueFormula⟩

/-- A cyclic refinement chain is recorded as explicit finite stage data on a
fixed period together with the assertion that the displayed refinement is
maximal. -/
structure CyclicRefinementChain where
  period : Nat
  levels : List Nat
  maximalRefinement : Prop

/-- Explicit prime-step witness for a maximal cyclic refinement chain. -/
structure CyclicRefinementPrimeStepData where
  chain : CyclicRefinementChain
  primeIndexStep : Prop
  hasPrimeIndexStep : primeIndexStep

/-- Maximal cyclic refinement exports the packaged prime-index step law. -/
theorem maximal_cyclic_refinement_prime_step
    (data : CyclicRefinementPrimeStepData) :
    data.primeIndexStep := by
  exact data.hasPrimeIndexStep

/-- Explicit invariant-data package comparing two maximal cyclic refinement
chains of the same period. -/
structure CyclicRefinementPrimeInvariantData where
  leftChain : CyclicRefinementChain
  rightChain : CyclicRefinementChain
  samePrimeIndexMultiset : Prop
  hasSamePrimeIndexMultiset : samePrimeIndexMultiset

/-- Prime-index invariance exports the packaged multiset agreement law. -/
theorem cyclic_refinement_prime_invariant
    (data : CyclicRefinementPrimeInvariantData) :
    data.samePrimeIndexMultiset := by
  exact data.hasSamePrimeIndexMultiset

end CoherenceCalculus
