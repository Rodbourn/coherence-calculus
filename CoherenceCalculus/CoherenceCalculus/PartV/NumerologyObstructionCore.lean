import CoherenceCalculus.PartV.ConstantCandidateCore

namespace CoherenceCalculus

/-- A visible obstruction witness certifies that a formula-facing surface is not
an autonomous carrier for the candidate it tries to support. -/
theorem search_surface_obstruction_blocks_autonomy
    {State View Law : Type}
    {view : State → View} {law : State → Law}
    (data : SearchSurfaceObstructionData view law) :
    ¬ AutonomousCarrier view law := by
  intro hauto
  apply data.different_law
  exact hauto data.left data.right data.same_view

/-- The same obstruction packaged on a formula-facing surface is the abstract
anti-numerology theorem: equal displayed formulas are not enough when the target
law still distinguishes states. -/
theorem numerology_attack_on_formula_surface
    {State Formula Scalar : Type}
    (surface : FormulaSearchSurface State Formula Scalar)
    (data : SearchSurfaceObstructionData surface.display surface.candidate) :
    ¬ AutonomousCarrier surface.display surface.candidate := by
  exact search_surface_obstruction_blocks_autonomy data

end CoherenceCalculus
