import CoherenceCalculus.Foundation.BedrockContinuationCore
import CoherenceCalculus.Foundation.DefectRuleCore
import CoherenceCalculus.Foundation.MetricCore

/-!
# Foundation.AutonomyCore

Realized exactification and scale-autonomy grammar on the rebuilt horizon core.

This file keeps the defect-side autonomy statements constructive and
import-free. The key design choice is that an autonomous scale law is encoded
as an explicit state map that factors through the horizon projection itself.
That avoids quotient carriers, implicit selectors, and any appeal to choice.
-/

namespace CoherenceCalculus

/-- A realized exactification generator is a state evolution together with the
explicit claim that it realizes the bedrock termination and continuation
interfaces on the chosen realized lane. -/
structure RealizedExactificationGenerator where
  toFun : State → State
  realizesBedrockTermination : Prop
  realizesBedrockContinuation : Prop

/-- The realized generator carries both bedrock clauses on the chosen
realization lane. -/
def realized_generator_carries_bedrock_law
    (X : RealizedExactificationGenerator) :
    Prop :=
  X.realizesBedrockTermination ∧ X.realizesBedrockContinuation

/-- A scale law is autonomous at horizon `h` when its output already lies in
the observable sector and the projected generator factors through the horizon
projection by that law. -/
def AutonomousScaleLaw
    (T : HorizonTower) (h : Nat)
    (X : RealizedExactificationGenerator)
    (L : State → State) : Prop :=
  (∀ y : State, (T.π h).toFun (L y) = L y) ∧
    ∀ x : State, (T.π h).toFun (X.toFun x) = L ((T.π h).toFun x)

/-- The autonomy defect is the mismatch between the projected realized
generator and a chosen autonomous scale candidate. -/
def autonomyDefect
    (T : HorizonTower) (h : Nat)
    (X : RealizedExactificationGenerator)
    (L : State → State) (x : State) : State :=
  State.sub ((T.π h).toFun (X.toFun x)) (L ((T.π h).toFun x))

/-- A horizon is autonomous for the realized exactification generator when some
explicit scale law factors the projected generator through that horizon. -/
def AutonomousHorizon
    (T : HorizonTower) (h : Nat)
    (X : RealizedExactificationGenerator) : Prop :=
  ∃ L : State → State, AutonomousScaleLaw T h X L

/-- Approximate autonomy on a chosen region means that one explicit scale law
controls the energy of the autonomy defect by a fixed budget. -/
def ApproximateAutonomy
    (T : HorizonTower) (h : Nat)
    (X : RealizedExactificationGenerator)
    (region : State → Prop) (ε : Nat) : Prop :=
  ∃ L : State → State,
    ∀ x : State, region x → State.energy (autonomyDefect T h X L x) ≤ ε

/-- The projected generator depends only on the observable horizon data. -/
def horizonFiberInvariant
    (T : HorizonTower) (h : Nat)
    (X : RealizedExactificationGenerator) : Prop :=
  ∀ x x' : State,
    (T.π h).toFun x = (T.π h).toFun x' →
      (T.π h).toFun (X.toFun x) = (T.π h).toFun (X.toFun x')

/-- Any autonomous scale law kills the autonomy defect identically. -/
theorem autonomous_scale_law_zero_defect
    (T : HorizonTower) (h : Nat)
    (X : RealizedExactificationGenerator)
    (L : State → State)
    (hL : AutonomousScaleLaw T h X L) :
    ∀ x : State, autonomyDefect T h X L x = State.zero := by
  intro x
  rcases hL with ⟨_hobs, hfactor⟩
  unfold autonomyDefect
  rw [hfactor x]
  exact State.sub_self (L ((T.π h).toFun x))

/-- Autonomous scale laws are exactly the laws for which projected generator
output depends only on observable horizon data. The law is unique on the
observable sector. -/
theorem autonomy_criterion_uniqueness
    (T : HorizonTower) (h : Nat)
    (X : RealizedExactificationGenerator) :
    (∃ L : State → State, AutonomousScaleLaw T h X L) ↔
      horizonFiberInvariant T h X := by
  constructor
  · intro hlaw
    rcases hlaw with ⟨L, hL⟩
    rcases hL with ⟨_hobs, hfactor⟩
    intro x x' hproj
    calc
      (T.π h).toFun (X.toFun x) = L ((T.π h).toFun x) := hfactor x
      _ = L ((T.π h).toFun x') := by rw [hproj]
      _ = (T.π h).toFun (X.toFun x') := (hfactor x').symm
  · intro hfiber
    let L : State → State := fun y => (T.π h).toFun (X.toFun y)
    refine ⟨L, ?_⟩
    refine ⟨?_, ?_⟩
    · intro y
      change (T.π h).toFun ((T.π h).toFun (X.toFun y)) = (T.π h).toFun (X.toFun y)
      exact (T.π h).idem (X.toFun y)
    · intro x
      change (T.π h).toFun (X.toFun x) = (T.π h).toFun (X.toFun ((T.π h).toFun x))
      apply hfiber x ((T.π h).toFun x)
      exact ((T.π h).idem x).symm

/-- Autonomous scale laws agreeing with the projected generator are unique on
projection-fixed states. -/
theorem autonomous_scale_law_unique
    (T : HorizonTower) (h : Nat)
    (X : RealizedExactificationGenerator)
    {L L' : State → State}
    (hL : AutonomousScaleLaw T h X L)
    (hL' : AutonomousScaleLaw T h X L') :
    ∀ y : State, (T.π h).toFun y = y → L y = L' y := by
  intro y hy
  rcases hL with ⟨_hobs, hfactor⟩
  rcases hL' with ⟨_hobs', hfactor'⟩
  calc
    L y = L ((T.π h).toFun y) := by rw [hy]
    _ = (T.π h).toFun (X.toFun y) := (hfactor y).symm
    _ = L' ((T.π h).toFun y) := hfactor' y
    _ = L' y := by rw [hy]

/-- The coherence defect of the realized generator splits into the autonomy
defect plus the visible mismatch between the chosen scale law and the generator
restricted to the observable sector. -/
theorem coherence_defect_and_autonomy_defect
    (T : HorizonTower) (h : Nat)
    (X : RealizedExactificationGenerator)
    (L : State → State) (x : State) :
    coherenceDefect T h X.toFun x =
      State.add
        (autonomyDefect T h X L x)
        (State.sub (L ((T.π h).toFun x)) (X.toFun ((T.π h).toFun x))) := by
  unfold coherenceDefect autonomyDefect
  exact
    (sub_eq_add_sub
      ((T.π h).toFun (X.toFun x))
      (L ((T.π h).toFun x))
      (X.toFun ((T.π h).toFun x))).symm

end CoherenceCalculus
