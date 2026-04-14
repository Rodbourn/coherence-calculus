import CoherenceCalculus.Foundation.PairingCore
import CoherenceCalculus.Foundation.ClosureTransportCore
import CoherenceCalculus.Foundation.CharacteristicTransportCore
import CoherenceCalculus.Foundation.ProjectionCalculusCore

/-!
# Foundation.HorizonComplexCore

One manuscript-facing horizon-complex object on the active Part I spine.

The rebuilt foundation already separates three layers:

* the concrete local carrier `State`,
* the horizon calculus carried by a nested projection tower,
* the nilpotent boundary and its defect algebra after a cut.

This file packages that structure into one derived object.

`HorizonBundle` is the carrier together with its horizon cuts. `HorizonComplex`
adds a nilpotent boundary to that bundle, so the observed boundary, leakage,
return, defect, and Schur-style residual-return grammar all belong to one
manuscript-facing type.

The constructions here do not add a new primitive carrier. They expose the
Part I calculus as a single structured object that later realized and physical
fields can live on.
-/

namespace CoherenceCalculus

/-- The local carrier together with its horizon cuts.

The carrier is the active rebuilt `State`; the only explicit datum is the
projection tower. The canonical pairing remains the rebuilt coordinate pairing
on that carrier. -/
structure HorizonBundle where
  tower : HorizonTower

namespace HorizonBundle

/-- The horizon projection at stage `h`. -/
def projection (bundle : HorizonBundle) (h : Nat) : Projection :=
  bundle.tower.π h

/-- The visible cut at horizon `h`. -/
def visible (bundle : HorizonBundle) (h : Nat) : State → State :=
  (bundle.projection h).toFun

/-- The shadow complement at horizon `h`. -/
def shadow (bundle : HorizonBundle) (h : Nat) : State → State :=
  shadowProj bundle.tower h

/-- The canonical pairing on the local carrier. -/
def pairing (_bundle : HorizonBundle) : State → State → Nat :=
  State.pair

/-- The bundle pairing recovers the rebuilt state energy on the diagonal. -/
theorem pairing_self (bundle : HorizonBundle) (x : State) :
    bundle.pairing x x = State.energy x :=
  State.pair_self x

end HorizonBundle

/-- A horizon complex is a horizon bundle equipped with a nilpotent boundary.

This is the native Part I object for the cut/defect calculus: full closure
holds on the complex itself, and failure of closure appears only after a
horizon cut. -/
structure HorizonComplex extends HorizonBundle where
  boundary : AddMap
  boundary_nilpotent : isNilpotent boundary.toFun

namespace HorizonComplex

/-- The visible boundary induced by cutting the full boundary at horizon `h`. -/
def observedBoundary (complex : HorizonComplex) (h : Nat) : State → State :=
  observedOp complex.toHorizonBundle.tower h complex.boundary.toFun

/-- Observable-to-shadow transport induced by the boundary at horizon `h`. -/
def leakage (complex : HorizonComplex) (h : Nat) : State → State :=
  leakageOp complex.toHorizonBundle.tower h complex.boundary.toFun

/-- Shadow-to-observable return induced by the boundary at horizon `h`. -/
def returnMap (complex : HorizonComplex) (h : Nat) : State → State :=
  returnOp complex.toHorizonBundle.tower h complex.boundary.toFun

/-- Round-trip defect induced by cutting the full boundary at horizon `h`. -/
def defect (complex : HorizonComplex) (h : Nat) : State → State :=
  defectOp complex.toHorizonBundle.tower h complex.boundary.toFun

/-- Packaged visible boundary map. -/
def observedBoundaryMap (complex : HorizonComplex) (h : Nat) : AddMap :=
  AddMap.observedMap complex.toHorizonBundle.tower h complex.boundary

/-- Packaged defect map. -/
def defectMap (complex : HorizonComplex) (h : Nat) : AddMap :=
  AddMap.defectMap complex.toHorizonBundle.tower h complex.boundary

/-- The residual-return field of the horizon complex at one cut and one chosen
shadow propagator. -/
def residualReturnField
    (complex : HorizonComplex) (h : Nat) (shadowPropagator : AddMap) :
    ResidualReturnField :=
  residualReturnFieldOf (complex.toHorizonBundle.projection h) complex.boundary shadowPropagator

/-- Full closure holds on the horizon complex before any cut is applied. -/
theorem boundary_square_zero (complex : HorizonComplex) (x : State) :
    complex.boundary (complex.boundary x) = State.zero :=
  complex.boundary_nilpotent x

/-- The boundary of the visible cut splits into its visible and leakage parts
across the same horizon cut. -/
theorem boundary_split (complex : HorizonComplex) (h : Nat) (x : State) :
    State.add (complex.observedBoundary h x) (complex.leakage h x) =
      complex.boundary (complex.toHorizonBundle.visible h x) := by
  simpa [HorizonComplex.observedBoundary, HorizonComplex.leakage] using
    observed_leakage_split complex.toHorizonBundle.tower h complex.boundary.toFun x

/-- HFT-1 on a horizon complex: the square of the observed boundary is the
negated round-trip defect. -/
theorem hft1 (complex : HorizonComplex) (h : Nat) (x : State) :
    complex.observedBoundary h (complex.observedBoundary h x) =
      State.negate (complex.defect h x) := by
  simpa [HorizonComplex.observedBoundary, HorizonComplex.defect] using
    HFT1_general_nilpotent
      complex.toHorizonBundle.tower h complex.boundary x complex.boundary_nilpotent

/-- For a visible state, the full boundary decomposes into observed boundary and
leakage, and one more application of the boundary returns the defect law on the
cut. -/
theorem through_horizon_decomposition
    (complex : HorizonComplex) (h : Nat) (u : State)
    (hu : complex.toHorizonBundle.visible h u = u) :
    complex.boundary u =
        State.add (complex.observedBoundary h u) (complex.leakage h u) ∧
      complex.observedBoundary h (complex.observedBoundary h u) =
        State.negate (complex.defect h u) := by
  constructor
  · have hsplit :
        State.add (complex.observedBoundary h u) (complex.leakage h u) =
          complex.boundary ((complex.toHorizonBundle.visible h) u) := by
      simpa [HorizonBundle.visible, HorizonComplex.observedBoundary,
        HorizonComplex.leakage] using
        observed_leakage_split
          complex.toHorizonBundle.tower h complex.boundary.toFun u
    simpa [hu] using hsplit.symm
  · exact complex.hft1 h u

/-- The returned residual of a horizon complex is exactly the Schur correction
at the chosen cut. -/
theorem returnedResidual_eq_schur
    (complex : HorizonComplex) (h : Nat) (shadowPropagator : AddMap) :
    returnedResidual (complex.residualReturnField h shadowPropagator) =
      schurComplement
        (complex.toHorizonBundle.projection h) complex.boundary shadowPropagator := by
  simpa [HorizonComplex.residualReturnField] using
    CoherenceCalculus.returnedResidual_eq_schur
      (complex.toHorizonBundle.projection h) complex.boundary shadowPropagator

end HorizonComplex

/-- The canonical horizon bundle on the closure-forced state carrier. -/
def canonicalHorizonBundle : HorizonBundle where
  tower := closureTower

/-- The canonical horizon complex on the closure-forced state carrier. -/
def canonicalHorizonComplex : HorizonComplex where
  toHorizonBundle := canonicalHorizonBundle
  boundary := trueBoundary
  boundary_nilpotent := trueBoundary_nilpotent

/-- After the stable dimension becomes fully visible, the canonical horizon
bundle reveals the whole state. -/
theorem canonical_visible_after_stable_dimension (h : Nat) (x : State) :
    canonicalHorizonBundle.visible (h + 4) x = x := by
  simpa [HorizonBundle.visible, HorizonBundle.projection, canonicalHorizonBundle]
    using closureProjection_after_stable_dimension h x

/-- After the stable dimension becomes fully visible, no shadow remains on the
canonical horizon bundle. -/
theorem canonical_shadow_after_stable_dimension (h : Nat) (x : State) :
    canonicalHorizonBundle.shadow (h + 4) x = State.zero := by
  simpa [HorizonBundle.shadow, canonicalHorizonBundle]
    using closureShadow_after_stable_dimension h x

/-- The closure-forced realization already carries the canonical horizon
complex: full closure, HFT-1 on every cut, and eventual exact visibility after
four further refinements. -/
theorem canonicalHorizonComplex_surface :
    (∀ x : State,
      canonicalHorizonComplex.boundary (canonicalHorizonComplex.boundary x) =
        State.zero) ∧
      (∀ h : Nat, ∀ x : State,
        canonicalHorizonComplex.observedBoundary h
            (canonicalHorizonComplex.observedBoundary h x) =
          State.negate (canonicalHorizonComplex.defect h x)) ∧
      (∀ h : Nat, ∀ x : State, canonicalHorizonBundle.visible (h + 4) x = x) ∧
      (∀ h : Nat, ∀ x : State, canonicalHorizonBundle.shadow (h + 4) x = State.zero) := by
  refine ⟨canonicalHorizonComplex.boundary_square_zero, ?_, ?_, ?_⟩
  · intro h x
    exact canonicalHorizonComplex.hft1 h x
  · exact canonical_visible_after_stable_dimension
  · exact canonical_shadow_after_stable_dimension

namespace CharacteristicHorizonRealization

/-- The underlying horizon bundle of a characteristic horizon realization. -/
def horizonBundle {Time : Type} (R : CharacteristicHorizonRealization Time) :
    HorizonBundle where
  tower := R.tower

/-- Every characteristic horizon realization lives on a horizon complex with the
canonical full boundary. -/
def horizonComplex {Time : Type} (R : CharacteristicHorizonRealization Time) :
    HorizonComplex where
  toHorizonBundle := R.horizonBundle
  boundary := trueBoundary
  boundary_nilpotent := trueBoundary_nilpotent

/-- Every characteristic horizon realization transports the Part I horizon
complex laws unchanged. -/
theorem horizonComplexSurface {Time : Type}
    (R : CharacteristicHorizonRealization Time) :
    (∀ x : State,
      R.horizonComplex.boundary (R.horizonComplex.boundary x) = State.zero) ∧
      (∀ h : Nat, ∀ x : State,
        R.horizonComplex.observedBoundary h
            (R.horizonComplex.observedBoundary h x) =
          State.negate (R.horizonComplex.defect h x)) ∧
      (∀ t : Time, ∀ h : Nat, ∀ x : State,
        R.U t (R.horizonComplex.observedBoundary h x) =
            R.horizonComplex.observedBoundary h (R.U t x) ∧
          R.U t (R.horizonComplex.defect h x) =
            R.horizonComplex.defect h (R.U t x)) := by
  refine ⟨R.horizonComplex.boundary_square_zero, ?_, ?_⟩
  · intro h x
    exact R.horizonComplex.hft1 h x
  · intro t h x
    obtain ⟨_hhft, hobs, hdef⟩ := characteristic_realization R t h x
    exact ⟨by simpa [HorizonComplex.observedBoundary, CharacteristicHorizonRealization.horizonComplex],
      by simpa [HorizonComplex.defect, CharacteristicHorizonRealization.horizonComplex] using hdef⟩

end CharacteristicHorizonRealization

end CoherenceCalculus
