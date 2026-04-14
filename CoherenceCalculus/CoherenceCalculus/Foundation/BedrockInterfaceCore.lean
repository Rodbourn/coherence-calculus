import CoherenceCalculus.Foundation.MetricCore

/-!
# Foundation.BedrockInterfaceCore

Manuscript-facing interface bundles for the Part I bedrock section.

The active theorem spine is carried by the rebuilt concrete `State`,
`HorizonTower`, and `EnergyHorizonTower` objects. This file supplies the small
abstract interface layer needed to tag the manuscript's bedrock definitions
honestly without reintroducing archived algebraic hierarchies.
-/

namespace CoherenceCalculus

/-- Abstract additive state-space interface used by the manuscript bedrock. -/
structure AdditiveStateSpace where
  Carrier : Type
  zero : Carrier
  add : Carrier → Carrier → Carrier
  neg : Carrier → Carrier
  add_assoc : ∀ x y z : Carrier, add (add x y) z = add x (add y z)
  add_comm : ∀ x y : Carrier, add x y = add y x
  add_zero : ∀ x : Carrier, add x zero = x
  add_left_neg : ∀ x : Carrier, add (neg x) x = zero

/-- Abstract energy-pairing interface on an additive state space. The certified
surface keeps the codomain arithmetic explicit and elementary. -/
structure EnergyPairing (X : AdditiveStateSpace) where
  pair : X.Carrier → X.Carrier → Nat
  add_left :
    ∀ x y z : X.Carrier, pair (X.add x y) z = pair x z + pair y z
  add_right :
    ∀ x y z : X.Carrier, pair x (X.add y z) = pair x y + pair x z
  symmetric : ∀ x y : X.Carrier, pair x y = pair y x
  nonnegative : ∀ x : X.Carrier, 0 ≤ pair x x
  definite : ∀ x : X.Carrier, pair x x = 0 → x = X.zero

/-- A finite coherence space is an additive state space equipped with an energy
pairing. -/
structure FiniteCoherenceSpace where
  stateSpace : AdditiveStateSpace
  energy : EnergyPairing stateSpace

/-- Manuscript-facing name for the active orthogonal horizon-tower package. -/
abbrev EnergyOrthogonalTower := EnergyHorizonTower

end CoherenceCalculus
