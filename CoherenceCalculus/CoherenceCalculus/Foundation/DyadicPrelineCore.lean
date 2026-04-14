import CoherenceCalculus.Foundation.DyadicComparisonCore

/-!
# Foundation.DyadicPrelineCore

Quotient-free dyadic pre-line presentations.

This layer does not form a quotient. A pre-line point is still an explicit
binary presentation, together with the clean identification/comparison data
developed below it. The purpose of this module is to package the current
certified surface as a genuine derived object without pretending that the final
normalized line has already been constructed.
-/

namespace CoherenceCalculus

/-- A dyadic pre-line point is an explicit binary presentation. -/
structure DyadicPrelinePoint where
  digits : Nat → BinaryDigit

namespace DyadicPrelinePoint

/-- Every pre-line presentation induces a dyadic unit-point candidate. -/
def unitPoint (x : DyadicPrelinePoint) : DyadicUnitPoint :=
  unitPointOfDigits x.digits

/-- Quotient-free boundary identification between pre-line presentations. -/
abbrev Identified (x y : DyadicPrelinePoint) : Type :=
  DyadicBoundaryIdentification x.digits y.digits

/-- Quotient-free comparison between pre-line presentations. -/
abbrev Comparison (x y : DyadicPrelinePoint) : Type :=
  DyadicBoundaryComparison x.digits y.digits

/-- Strict-left comparison between pre-line presentations. -/
abbrev StrictLeft (x y : DyadicPrelinePoint) : Type :=
  DyadicStrictSeparation x.digits y.digits

/-- Every pre-line presentation is identified with itself. -/
def identified_refl (x : DyadicPrelinePoint) : Identified x x :=
  DyadicBoundaryIdentification.refl x.digits

/-- Identification of pre-line presentations is symmetric. -/
def identified_symm {x y : DyadicPrelinePoint} :
    Identified x y → Identified y x :=
  DyadicBoundaryIdentification.symm

/-- Identification of pre-line presentations is transitive. -/
def identified_trans {x y z : DyadicPrelinePoint} :
    Identified x y → Identified y z → Identified x z :=
  DyadicBoundaryIdentification.trans

/-- Comparison of pre-line presentations is symmetric. -/
def comparison_symm {x y : DyadicPrelinePoint} :
    Comparison x y → Comparison y x :=
  DyadicBoundaryComparison.symm

/-- Comparison transports across an identified presentation on the left. -/
def comparison_of_identified_left
    {x x' y : DyadicPrelinePoint}
    (h : Identified x x') (c : Comparison x' y) :
    Comparison x y :=
  DyadicBoundaryComparison.trans_identified_left h c

/-- Comparison transports across an identified presentation on the right. -/
def comparison_of_identified_right
    {x y y' : DyadicPrelinePoint}
    (c : Comparison x y) (h : Identified y y') :
    Comparison x y' :=
  DyadicBoundaryComparison.trans_identified_right c h

/-- Comparison is presentation-invariant on both sides. -/
def comparison_congr
    {x x' y y' : DyadicPrelinePoint}
    (hx : Identified x x') (c : Comparison x' y') (hy : Identified y' y) :
    Comparison x y :=
  comparison_of_identified_right (comparison_of_identified_left hx c) hy

/-- Identified and strict-left comparison are incompatible. -/
theorem false_of_identified_and_strictLeft
    {x y : DyadicPrelinePoint}
    (h : Identified x y) (s : StrictLeft x y) :
    False := by
  exact DyadicBoundaryComparison.false_of_identified_and_strictLeft h s

/-- Identified and strict-right comparison are incompatible. -/
theorem false_of_identified_and_strictRight
    {x y : DyadicPrelinePoint}
    (h : Identified x y) (s : StrictLeft y x) :
    False := by
  exact DyadicBoundaryComparison.false_of_identified_and_strictRight h s

/-- Opposite strict comparisons are incompatible. -/
theorem false_of_strictLeft_and_strictRight
    {x y : DyadicPrelinePoint}
    (sLeft : StrictLeft x y) (sRight : StrictLeft y x) :
    False := by
  exact DyadicBoundaryComparison.false_of_strictLeft_and_strictRight sLeft sRight

/-- Strict-left comparison is transitive. -/
def strictLeft_trans
    {x y z : DyadicPrelinePoint}
    (sXY : StrictLeft x y) (sYZ : StrictLeft y z) :
    Comparison x z :=
  DyadicBoundaryComparison.strictLeft_trans sXY sYZ

/-- Strict-right comparison is transitive. -/
def strictRight_trans
    {x y z : DyadicPrelinePoint}
    (sYX : StrictLeft y x) (sZY : StrictLeft z y) :
    Comparison x z :=
  DyadicBoundaryComparison.strictRight_trans sYX sZY

/-- Canonical left-endpoint presentation. -/
def leftEndpoint : DyadicPrelinePoint where
  digits := fun _ => BinaryDigit.left

/-- Canonical right-endpoint presentation. -/
def rightEndpoint : DyadicPrelinePoint where
  digits := fun _ => BinaryDigit.right

/-- The canonical left-endpoint presentation induces the canonical left unit
point candidate. -/
theorem leftEndpoint_unitPoint :
    leftEndpoint.unitPoint = leftUnitPoint := rfl

/-- Lower presentation in the canonical midpoint ambiguity pair. -/
def midpointLower : DyadicPrelinePoint where
  digits := midpointLowerDigits

/-- Upper presentation in the canonical midpoint ambiguity pair. -/
def midpointUpper : DyadicPrelinePoint where
  digits := midpointUpperDigits

/-- Lower presentation in the canonical quarter-point ambiguity pair. -/
def quarterLower : DyadicPrelinePoint where
  digits
    | 0 => BinaryDigit.left
    | 1 => BinaryDigit.left
    | _ + 2 => BinaryDigit.right

/-- Upper presentation in the canonical quarter-point ambiguity pair. -/
def quarterUpper : DyadicPrelinePoint where
  digits
    | 0 => BinaryDigit.left
    | 1 => BinaryDigit.right
    | _ + 2 => BinaryDigit.left

/-- Lower presentation in the canonical three-quarter-point ambiguity pair. -/
def threeQuarterLower : DyadicPrelinePoint where
  digits
    | 0 => BinaryDigit.right
    | 1 => BinaryDigit.left
    | _ + 2 => BinaryDigit.right

/-- Upper presentation in the canonical three-quarter-point ambiguity pair. -/
def threeQuarterUpper : DyadicPrelinePoint where
  digits
    | 0 => BinaryDigit.right
    | 1 => BinaryDigit.right
    | _ + 2 => BinaryDigit.left

/-- The canonical midpoint ambiguity pair is boundary-identified. -/
def midpoint_identified : Identified midpointLower midpointUpper :=
  DyadicBoundaryIdentification.midpoint

/-- The canonical midpoint ambiguity pair is comparable as an identified pair. -/
def midpoint_comparison : Comparison midpointLower midpointUpper :=
  .identified midpoint_identified

/-- The canonical midpoint ambiguity pair is also identified in the reverse
orientation. -/
def midpoint_identified_symm : Identified midpointUpper midpointLower :=
  identified_symm midpoint_identified

end DyadicPrelinePoint

end CoherenceCalculus
