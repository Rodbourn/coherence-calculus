namespace CoherenceCalculus

/-- A search surface is autonomous for `law` when the visible carrier already
determines the value of that law. -/
def AutonomousCarrier {State View Law : Type}
    (view : State → View) (law : State → Law) : Prop :=
  ∀ x y : State, view x = view y → law x = law y

/-- A direct witness that a collapsed search surface forgets information needed
for the target law. -/
structure SearchSurfaceObstructionData {State View Law : Type}
    (view : State → View) (law : State → Law) where
  left : State
  right : State
  same_view : view left = view right
  different_law : law left ≠ law right

/-- A formula-facing surface packages the displayed carrier together with the
target scalar that one might try to read off from it. -/
structure FormulaSearchSurface (State Formula Scalar : Type) where
  display : State → Formula
  candidate : State → Scalar

/-- A two-channel primitive packet with its first scalar closure coefficient. -/
structure TwoChannelPrimitiveDatum (Channel Scalar : Type) where
  direct : Channel
  ret : Channel
  closureScalar : Scalar

/-- The first coherent Part V search surface: a forced primitive packet, a
collapsed threshold view, a fuller profile view, and the dressed local scalar
carried on that profile. -/
structure CoherentSchurCandidateSurface
    (Channel State Threshold Profile Scalar Horizon : Type) where
  primitive : TwoChannelPrimitiveDatum Channel Scalar
  thresholdView : State → Threshold
  profileView : State → Profile
  localInvariant : State → Scalar
  horizonCut : Horizon
  profile_autonomous : AutonomousCarrier profileView localInvariant

/-- A primitive constant search datum records that the primitive scalar used by
the search is exactly the first coherent closure scalar. -/
structure CoherentPrimitiveConstantSearchDatum
    (Channel State Threshold Profile Scalar Horizon : Type) where
  surface : CoherentSchurCandidateSurface Channel State Threshold Profile Scalar Horizon
  primitiveScalar : Scalar
  primitiveScalar_exact : primitiveScalar = surface.primitive.closureScalar

/-- Threshold-autonomy for the coherent Part V search surface. -/
def ThresholdAutonomousCarrier
    {Channel State Threshold Profile Scalar Horizon : Type}
    (surface : CoherentSchurCandidateSurface
      Channel State Threshold Profile Scalar Horizon) : Prop :=
  AutonomousCarrier surface.thresholdView surface.localInvariant

end CoherenceCalculus
