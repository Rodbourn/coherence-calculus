import CoherenceCalculus.PartV.NumerologyObstructionCore
import CoherenceCalculus.PartV.CoherentPrimitiveCore

namespace CoherenceCalculus

/-- On the coherent Part V search surface, a single threshold-obstruction
witness certifies that threshold statistics are not an autonomous constant
carrier. -/
theorem threshold_statistics_not_autonomous_constant_carrier
    {Channel State Threshold Profile Scalar Horizon : Type}
    (surface : CoherentSchurCandidateSurface
      Channel State Threshold Profile Scalar Horizon)
    (data : SearchSurfaceObstructionData
      surface.thresholdView surface.localInvariant) :
    ¬ ThresholdAutonomousCarrier surface := by
  exact search_surface_obstruction_blocks_autonomy data

/-- The first coherent constant-search package therefore splits cleanly into a
negative threshold-autonomy statement and a positive profile-autonomy statement.
-/
theorem coherentPrimitiveThresholdObstruction
    {Channel State Threshold Profile Scalar Horizon : Type}
    (datum : CoherentPrimitiveConstantSearchDatum
      Channel State Threshold Profile Scalar Horizon)
    (data : SearchSurfaceObstructionData
      datum.surface.thresholdView datum.surface.localInvariant) :
    ¬ ThresholdAutonomousCarrier datum.surface := by
  exact threshold_statistics_not_autonomous_constant_carrier datum.surface data

/-- The coherent primitive constant-search datum still keeps the profile-side
autonomy originally built into the coherent search surface. -/
theorem coherentPrimitiveProfileAutonomy
    {Channel State Threshold Profile Scalar Horizon : Type}
    (datum : CoherentPrimitiveConstantSearchDatum
      Channel State Threshold Profile Scalar Horizon) :
    AutonomousCarrier datum.surface.profileView datum.surface.localInvariant := by
  exact datum.surface.profile_autonomous

/-- The coherent primitive constant-search datum splits cleanly into the
threshold obstruction and the retained profile-side autonomy. -/
theorem coherentPrimitiveSearchSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    (datum : CoherentPrimitiveConstantSearchDatum
      Channel State Threshold Profile Scalar Horizon)
    (data : SearchSurfaceObstructionData
      datum.surface.thresholdView datum.surface.localInvariant) :
    (¬ ThresholdAutonomousCarrier datum.surface) ∧
      AutonomousCarrier datum.surface.profileView datum.surface.localInvariant := by
  exact
    ⟨coherentPrimitiveThresholdObstruction datum data,
      coherentPrimitiveProfileAutonomy datum⟩

/-- The first coherent constant-search package therefore splits cleanly into a
negative threshold-autonomy statement and a positive profile-autonomy statement.
-/
theorem coherent_primitive_constant_search_requires_profile_level_data
    {Channel State Threshold Profile Scalar Horizon : Type}
    (datum : CoherentPrimitiveConstantSearchDatum
      Channel State Threshold Profile Scalar Horizon)
    (data : SearchSurfaceObstructionData
      datum.surface.thresholdView datum.surface.localInvariant) :
    (¬ ThresholdAutonomousCarrier datum.surface) ∧
      AutonomousCarrier datum.surface.profileView datum.surface.localInvariant := by
  exact coherentPrimitiveSearchSurface datum data

/-- The constant-search package constructed from the first coherent primitive
interface inherits the same threshold obstruction and profile-level autonomy. -/
theorem coherentInterfaceThresholdObstruction
    {Channel State Threshold Profile Scalar Horizon : Type}
    (interface : CoherentDirectReturnInterface Channel Scalar)
    (thresholdView : State → Threshold)
    (profileView : State → Profile)
    (localInvariant : State → Scalar)
    (horizonCut : Horizon)
    (profile_autonomous : AutonomousCarrier profileView localInvariant)
    (data : SearchSurfaceObstructionData thresholdView localInvariant) :
    let datum :=
      coherentPrimitiveConstantSearchDatumOfInterface
        interface thresholdView profileView localInvariant horizonCut
        profile_autonomous
    ¬ ThresholdAutonomousCarrier datum.surface := by
  intro datum
  exact coherentPrimitiveThresholdObstruction datum data

/-- The constant-search package constructed from the first coherent primitive
interface keeps the same profile-side autonomy as the constructed coherent
search surface. -/
theorem coherentInterfaceProfileAutonomy
    {Channel State Threshold Profile Scalar Horizon : Type}
    (interface : CoherentDirectReturnInterface Channel Scalar)
    (thresholdView : State → Threshold)
    (profileView : State → Profile)
    (localInvariant : State → Scalar)
    (horizonCut : Horizon)
    (profile_autonomous : AutonomousCarrier profileView localInvariant) :
    let datum :=
      coherentPrimitiveConstantSearchDatumOfInterface
        interface thresholdView profileView localInvariant horizonCut
        profile_autonomous
    AutonomousCarrier datum.surface.profileView datum.surface.localInvariant := by
  intro datum
  exact coherentPrimitiveProfileAutonomy datum

/-- The coherent constant-search package constructed from the first coherent
primitive interface splits cleanly into the threshold obstruction and the
retained profile-side autonomy. -/
theorem coherentInterfaceSearchSurface
    {Channel State Threshold Profile Scalar Horizon : Type}
    (interface : CoherentDirectReturnInterface Channel Scalar)
    (thresholdView : State → Threshold)
    (profileView : State → Profile)
    (localInvariant : State → Scalar)
    (horizonCut : Horizon)
    (profile_autonomous : AutonomousCarrier profileView localInvariant)
    (data : SearchSurfaceObstructionData thresholdView localInvariant) :
    let datum :=
      coherentPrimitiveConstantSearchDatumOfInterface
        interface thresholdView profileView localInvariant horizonCut
        profile_autonomous
    (¬ ThresholdAutonomousCarrier datum.surface) ∧
      AutonomousCarrier datum.surface.profileView datum.surface.localInvariant := by
  intro datum
  exact coherentPrimitiveSearchSurface datum data

/-- The constant-search package constructed from the first coherent primitive
interface inherits the same threshold obstruction and profile-level autonomy. -/
theorem coherent_interface_search_requires_profile_level_data
    {Channel State Threshold Profile Scalar Horizon : Type}
    (interface : CoherentDirectReturnInterface Channel Scalar)
    (thresholdView : State → Threshold)
    (profileView : State → Profile)
    (localInvariant : State → Scalar)
    (horizonCut : Horizon)
    (profile_autonomous : AutonomousCarrier profileView localInvariant)
    (data : SearchSurfaceObstructionData thresholdView localInvariant) :
    let datum :=
      coherentPrimitiveConstantSearchDatumOfInterface
        interface thresholdView profileView localInvariant horizonCut
        profile_autonomous
    (¬ ThresholdAutonomousCarrier datum.surface) ∧
      AutonomousCarrier datum.surface.profileView datum.surface.localInvariant := by
  exact coherentInterfaceSearchSurface
    interface thresholdView profileView localInvariant horizonCut
    profile_autonomous data

end CoherenceCalculus
