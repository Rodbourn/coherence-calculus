namespace CoherenceCalculus
namespace AppendixHorizons

/-!
This detached appendix lane packages the genuinely oblique / spectral /
trace-level appendix material. The emphasis is the same as elsewhere in the
rebuild: every extra analytic ingredient is explicit and local.
-/

/-- Appendix oblique-horizon interface. -/
structure ObliqueHorizon (State : Type) where
  project : State → State
  shadow : State → State
  splitWitness : ∀ x : State, State
  idempotentWitness : Prop
  complementaryWitness : Prop

/-- Basic algebraic package for an oblique horizon split. -/
structure idempotent_split_algebra where
  witness : Prop

/-- Appendix oblique block-decomposition carrier. -/
structure obliqueCompression (State : Type) where
  pp : State → State
  pq : State → State
  qp : State → State
  qq : State → State

/-- Appendix oblique HFT-1 carrier. -/
structure oblique_hft1 where
  witness : Prop

/-- Appendix oblique coherence-defect carrier. -/
structure obliqueCoherenceDefect (State : Type) where
  defect : State → State

/-- Appendix oblique chain-rule carrier. -/
structure oblique_chain_rule where
  witness : Prop

/-- Appendix oblique product-rule carrier. -/
structure oblique_product_rule where
  witness : Prop

/-- Documentary stability note for the oblique appendix. -/
structure oblique_stability_note where
  statement : Prop

/-- Appendix metricization carrier for an oblique horizon. -/
structure oblique_metricization where
  witness : Prop

/-- Appendix spectral-horizon-family interface. -/
structure SpectralHorizonFamily (Index Band State : Type) where
  horizon : Index → State → State
  band : Band → State → State
  monotoneWitness : Prop
  rightContinuousWitness : Prop
  limitWitness : Prop

/-- Documentary bounded/unbounded scope note for the spectral appendix. -/
structure spectral_horizon_unbounded_scope where
  statement : Prop

/-- Appendix band-projection carrier. -/
def bandProjection {Index Band State : Type}
    (family : SpectralHorizonFamily Index Band State) :
    Band → State → State :=
  family.band

/-- Appendix resolution-measure carrier. -/
structure resolutionMeasure (Band : Type) where
  mass : Band → Nat

/-- Appendix band-energy/measure identity carrier. -/
structure band_energy_measure where
  witness : Prop

/-- Appendix continuous spectral telescoping carrier. -/
structure spectral_telescoping where
  witness : Prop

/-- Documentary discrete-tower special-case note for the spectral appendix. -/
structure discrete_tower_special_case where
  statement : Prop

/-- Appendix joint horizon-trace / band-trace carrier. -/
structure horizonTraceBandTrace (Projection Operator : Type) where
  horizonTrace : Projection → Operator → Nat
  bandTrace : Projection → Operator → Nat

/-- Appendix two-level trace-splitting carrier. -/
structure two_level_trace_splitting where
  witness : Prop

/-- Appendix discrete-tower trace telescoping carrier. -/
structure trace_telescope_tower where
  witness : Prop

/-- Appendix spectral trace-measure carrier. -/
structure spectralTraceMeasure (Band : Type) where
  mass : Band → Nat

/-- Appendix band-trace/measure identity carrier. -/
structure band_trace_measure where
  witness : Prop

/-- Appendix spectral trace-telescoping carrier. -/
structure trace_telescope_spectral where
  witness : Prop

end AppendixHorizons
end CoherenceCalculus
