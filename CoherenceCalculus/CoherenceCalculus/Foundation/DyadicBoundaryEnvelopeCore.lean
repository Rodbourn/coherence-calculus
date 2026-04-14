import CoherenceCalculus.Foundation.DyadicIdentificationCore

/-!
# Foundation.DyadicBoundaryEnvelopeCore

Finite horizon envelopes for dyadic boundary points.

The clean dyadic identification layer says when two binary presentations should
be treated as the same boundary point candidate. This module repackages that
data as a quotient-free envelope object:

- an exact point presentation gives one binary thread
- an ambiguous-tail presentation gives an ordered lower/upper pair

The finite observer can then read lower and upper interval views from that
envelope without importing a quotient construction.
-/

namespace CoherenceCalculus

namespace DyadicAmbiguousWitness

/-- If a stage `n` sits `k` steps before the split stage of an ambiguous-tail
witness, then the two interval descriptions are still exactly equal there. -/
theorem intervals_eq_of_split_eq
    {digits₁ digits₂ : Nat → BinaryDigit}
    (w : DyadicAmbiguousWitness digits₁ digits₂)
    {n k : Nat}
    (h : n + k = w.split.stage) :
    intervalsOfDigits digits₁ n = intervalsOfDigits digits₂ n := by
  apply intervalsOfDigits_eq_of_eq_later (n := n) (k := k)
  rw [h]
  exact w.split.common_interval

end DyadicAmbiguousWitness

/-- A quotient-free dyadic boundary envelope: either an exact binary thread or a
classified ambiguous-tail pair. -/
inductive DyadicBoundaryEnvelope : Type where
  | exact (digits : Nat → BinaryDigit) : DyadicBoundaryEnvelope
  | ambiguous
      {lowerDigits upperDigits : Nat → BinaryDigit}
      (w : DyadicAmbiguousWitness lowerDigits upperDigits) :
      DyadicBoundaryEnvelope

namespace DyadicBoundaryEnvelope

/-- Lower binary presentation carried by a dyadic boundary envelope. -/
def lowerDigits : DyadicBoundaryEnvelope → Nat → BinaryDigit
  | .exact digits => digits
  | .ambiguous (lowerDigits := lowerDigits) _ => lowerDigits

/-- Upper binary presentation carried by a dyadic boundary envelope. -/
def upperDigits : DyadicBoundaryEnvelope → Nat → BinaryDigit
  | .exact digits => digits
  | .ambiguous (upperDigits := upperDigits) _ => upperDigits

/-- Lower finite-horizon interval seen from a dyadic boundary envelope. -/
def lowerInterval (E : DyadicBoundaryEnvelope) (n : Nat) : DyadicInterval n :=
  intervalsOfDigits E.lowerDigits n

/-- Upper finite-horizon interval seen from a dyadic boundary envelope. -/
def upperInterval (E : DyadicBoundaryEnvelope) (n : Nat) : DyadicInterval n :=
  intervalsOfDigits E.upperDigits n

/-- Every dyadic boundary envelope carries clean boundary-identification data
between its lower and upper presentations. -/
def identified : (E : DyadicBoundaryEnvelope) →
    DyadicBoundaryIdentification E.lowerDigits E.upperDigits
  | .exact digits => DyadicBoundaryIdentification.refl digits
  | .ambiguous w => .ambiguousLeftRight w

/-- Turn arbitrary boundary-identification data into its canonical ordered
boundary-envelope form. -/
def ofIdentification
    {digits₁ digits₂ : Nat → BinaryDigit}
    (h : DyadicBoundaryIdentification digits₁ digits₂) :
    DyadicBoundaryEnvelope :=
  match h with
  | .exact _ => .exact digits₁
  | .ambiguousLeftRight w => .ambiguous w
  | .ambiguousRightLeft w => .ambiguous w

/-- The canonical midpoint ambiguity defines a dyadic boundary envelope. -/
def midpoint : DyadicBoundaryEnvelope :=
  .ambiguous midpointDigits_ambiguousWitness

end DyadicBoundaryEnvelope

end CoherenceCalculus
