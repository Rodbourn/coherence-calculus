import CoherenceCalculusMathlibBridge.AbstractHilbert

namespace CoherenceCalculusMathlibBridge

open CoherenceCalculus

/--
Identity symmetry transport for a continuum reconstruction datum.

This is the clean bridge-side witness used to specialize the certified Part III
continuum-identification theorem to detached mathlib realizations.
-/
def identityContinuumSymmetryTransport
    (F : DiscreteRealizedLawFamily) {X₀ X : Type}
    (datum : ContinuumReconstructionDatum F X₀ X) :
    ContinuumSymmetryTransport F datum where
  spaceMap := fun x => x
  domainMap := fun u => u
  discreteMap := fun _ y => y
  sample_intertwines := by
    intro n u
    rfl
  reconstruct_intertwines := by
    intro n y
    rfl
  law_commutes := by
    intro n y
    rfl

/-- The natural limit class of continuum laws consistent with a fixed detached
mathlib realization. -/
def consistencyLimitClass
    (F : DiscreteRealizedLawFamily) {X₀ X : Type}
    (datum : ContinuumReconstructionDatum F X₀ X) :
    ContinuumLimitClass (X₀ → X) where
  admissible := AsymptoticConsistency F datum

theorem ContinuumContract.law_unique
    {F : DiscreteRealizedLawFamily} {X₀ X : Type}
    (contract : ContinuumContract F X₀ X)
    {L' : X₀ → X}
    (hL' : AsymptoticConsistency F contract.datum L') :
    ∀ u : X₀, contract.law u = L' u := by
  exact
    (continuum_identification_on_dense_test_domain
      F contract.datum contract.consistent hL'
      (identityContinuumSymmetryTransport F contract.datum)).1

theorem ContinuumContract.law_forced
    {F : DiscreteRealizedLawFamily} {X₀ X : Type}
    (contract : ContinuumContract F X₀ X)
    (hunique :
      ∀ other : X₀ → X,
        AsymptoticConsistency F contract.datum other → other = contract.law) :
    ForcedContinuumLaw (consistencyLimitClass F contract.datum) contract.law := by
  exact
    discrete_to_continuum_forcing
      (consistencyLimitClass F contract.datum)
      contract.law
      contract.consistent
      hunique

theorem AbstractContinuumReconstructionModel.reconstruct_sample_limit
    {𝕜 E X₀ : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (model : AbstractContinuumReconstructionModel 𝕜 E X₀)
    (u : X₀) :
    model.toDatum.limits.tendsTo
      (fun n => model.toDatum.reconstruct n (model.toDatum.sample n u))
      (model.toDatum.embed u) := by
  exact model.toDatum.reconstruct_sample u

theorem AbstractContinuumReconstructionModel.consistent_laws_agree
    {𝕜 E X₀ : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (model : AbstractContinuumReconstructionModel 𝕜 E X₀)
    {L L' : X₀ → E}
    (hL : AsymptoticConsistency model.family model.toDatum L)
    (hL' : AsymptoticConsistency model.family model.toDatum L') :
    ∀ u : X₀, L u = L' u := by
  exact
    (continuum_identification_on_dense_test_domain
      model.family
      model.toDatum
      hL
      hL'
      (identityContinuumSymmetryTransport model.family model.toDatum)).1

theorem AbstractContinuumReconstructionModel.consistent_law_forced
    {𝕜 E X₀ : Type _}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (model : AbstractContinuumReconstructionModel 𝕜 E X₀)
    (L : X₀ → E)
    (hL : AsymptoticConsistency model.family model.toDatum L)
    (hunique :
      ∀ other : X₀ → E,
        AsymptoticConsistency model.family model.toDatum other → other = L) :
    ForcedContinuumLaw (consistencyLimitClass model.family model.toDatum) L := by
  exact
    discrete_to_continuum_forcing
      (consistencyLimitClass model.family model.toDatum)
      L
      hL
      hunique

end CoherenceCalculusMathlibBridge
