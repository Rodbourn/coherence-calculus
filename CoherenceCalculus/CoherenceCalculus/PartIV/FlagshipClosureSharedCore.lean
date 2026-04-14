import CoherenceCalculus.PartIV.ObserverSelectionCore

/-!
# PartIV.FlagshipClosureSharedCore

Shared closure helper for the Part IV flagship lanes.

This isolates the common continuum-forcing step used across the phase, wave,
gauge, and geometric lanes once singleton endpoint data and a
pairing-compatible representative have already been fixed.
-/

namespace CoherenceCalculus

namespace FlagshipShared

/-- Once the endpoint class and its pairing-compatible representative are
already fixed, the remaining continuum-side work is only admissibility and
uniqueness in the selected observer's continuum class. -/
theorem forcedContinuumFromEndpointFacts
    {Law : Type}
    (cls : ContinuumLimitClass Law)
    (target : Law)
    {singleton representative : Prop}
    (hsingleton : singleton)
    (hrepresentative : representative)
    (targetAdmissible : cls.admissible target)
    (targetUnique : ∀ other : Law, cls.admissible other → other = target) :
    singleton ∧ representative ∧ ForcedContinuumLaw cls target := by
  exact
    ⟨hsingleton,
      hrepresentative,
      discrete_to_continuum_forcing_principle
        cls target targetAdmissible targetUnique⟩

end FlagshipShared

end CoherenceCalculus
