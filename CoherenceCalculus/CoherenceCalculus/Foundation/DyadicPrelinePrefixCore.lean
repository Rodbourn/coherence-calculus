import CoherenceCalculus.Foundation.DyadicPrelineWitnessCore
import CoherenceCalculus.Foundation.DyadicPrefixCore

/-!
# Foundation.DyadicPrelinePrefixCore

Common-prefix transport for dyadic pre-line presentations.

This packages the digit-level prefix transport on the quotient-free dyadic
pre-line. Every finite dyadic subinterval inherits the same clean comparison
and ambiguous-boundary structure by prefixing the canonical landmark
presentations with a common finite binary word.
-/

namespace CoherenceCalculus

namespace DyadicPrelinePoint

/-- Prepend one binary digit to a dyadic pre-line presentation. -/
def prependDigit (b : BinaryDigit) (x : DyadicPrelinePoint) : DyadicPrelinePoint where
  digits := prependDigitDigits b x.digits

/-- Prepend `left` to a dyadic pre-line presentation. -/
def prependLeft (x : DyadicPrelinePoint) : DyadicPrelinePoint :=
  prependDigit BinaryDigit.left x

/-- Prepend `right` to a dyadic pre-line presentation. -/
def prependRight (x : DyadicPrelinePoint) : DyadicPrelinePoint :=
  prependDigit BinaryDigit.right x

/-- Prepend a finite binary word to a dyadic pre-line presentation. -/
def prependWord : List BinaryDigit → DyadicPrelinePoint → DyadicPrelinePoint
  | [], x => x
  | b :: word, x => prependDigit b (prependWord word x)

/-- Common-prefix transport of boundary identification by one digit. -/
def identified_prependDigit
    (b : BinaryDigit) {x y : DyadicPrelinePoint}
    (h : Identified x y) :
    Identified (prependDigit b x) (prependDigit b y) :=
  match b with
  | BinaryDigit.left => DyadicBoundaryIdentification.prependLeft h
  | BinaryDigit.right => DyadicBoundaryIdentification.prependRight h

/-- Common-prefix transport of strict-left comparison by one digit. -/
def strictLeft_prependDigit
    (b : BinaryDigit) {x y : DyadicPrelinePoint}
    (s : StrictLeft x y) :
    StrictLeft (prependDigit b x) (prependDigit b y) :=
  match b with
  | BinaryDigit.left => DyadicStrictSeparation.prependLeft s
  | BinaryDigit.right => DyadicStrictSeparation.prependRight s

/-- Common-prefix transport of quotient-free comparison by one digit. -/
def comparison_prependDigit
    (b : BinaryDigit) {x y : DyadicPrelinePoint}
    (c : Comparison x y) :
    Comparison (prependDigit b x) (prependDigit b y) :=
  match b with
  | BinaryDigit.left => DyadicBoundaryComparison.prependLeft c
  | BinaryDigit.right => DyadicBoundaryComparison.prependRight c

/-- Common-prefix transport of boundary identification by a finite word. -/
def identified_prependWord :
    (word : List BinaryDigit) →
      {x y : DyadicPrelinePoint} →
        Identified x y →
          Identified (prependWord word x) (prependWord word y)
  | [], _, _, h => h
  | b :: word, _, _, h =>
      identified_prependDigit b (identified_prependWord word h)

/-- Common-prefix transport of strict-left comparison by a finite word. -/
def strictLeft_prependWord :
    (word : List BinaryDigit) →
      {x y : DyadicPrelinePoint} →
        StrictLeft x y →
          StrictLeft (prependWord word x) (prependWord word y)
  | [], _, _, s => s
  | b :: word, _, _, s =>
      strictLeft_prependDigit b (strictLeft_prependWord word s)

/-- Common-prefix transport of quotient-free comparison by a finite word. -/
def comparison_prependWord :
    (word : List BinaryDigit) →
      {x y : DyadicPrelinePoint} →
        Comparison x y →
          Comparison (prependWord word x) (prependWord word y)
  | [], _, _, c => c
  | b :: word, _, _, c =>
      comparison_prependDigit b (comparison_prependWord word c)

/-- Canonical midpoint-lower presentation in the dyadic subinterval determined
by a finite prefix. -/
def midpointLowerOfWord (word : List BinaryDigit) : DyadicPrelinePoint :=
  prependWord word midpointLower

/-- Canonical midpoint-upper presentation in the dyadic subinterval determined
by a finite prefix. -/
def midpointUpperOfWord (word : List BinaryDigit) : DyadicPrelinePoint :=
  prependWord word midpointUpper

/-- Canonical quarter-lower presentation in the dyadic subinterval determined
by a finite prefix. -/
def quarterLowerOfWord (word : List BinaryDigit) : DyadicPrelinePoint :=
  prependWord word quarterLower

/-- Canonical quarter-upper presentation in the dyadic subinterval determined
by a finite prefix. -/
def quarterUpperOfWord (word : List BinaryDigit) : DyadicPrelinePoint :=
  prependWord word quarterUpper

/-- Canonical three-quarter-lower presentation in the dyadic subinterval
determined by a finite prefix. -/
def threeQuarterLowerOfWord (word : List BinaryDigit) : DyadicPrelinePoint :=
  prependWord word threeQuarterLower

/-- Canonical three-quarter-upper presentation in the dyadic subinterval
determined by a finite prefix. -/
def threeQuarterUpperOfWord (word : List BinaryDigit) : DyadicPrelinePoint :=
  prependWord word threeQuarterUpper

/-- Left endpoint of the dyadic subinterval determined by a finite prefix. -/
def leftEndpointOfWord (word : List BinaryDigit) : DyadicPrelinePoint :=
  prependWord word leftEndpoint

/-- Right endpoint of the dyadic subinterval determined by a finite prefix. -/
def rightEndpointOfWord (word : List BinaryDigit) : DyadicPrelinePoint :=
  prependWord word rightEndpoint

/-- Every finite dyadic subinterval inherits the canonical midpoint ambiguity
pair. -/
def midpoint_identified_ofWord (word : List BinaryDigit) :
    Identified (midpointLowerOfWord word) (midpointUpperOfWord word) :=
  identified_prependWord word midpoint_identified

/-- The canonical midpoint ambiguity pair in every finite dyadic subinterval is
comparable as an identified pair. -/
def midpoint_comparison_ofWord (word : List BinaryDigit) :
    Comparison (midpointLowerOfWord word) (midpointUpperOfWord word) :=
  comparison_prependWord word midpoint_comparison

/-- Every finite dyadic subinterval inherits the canonical quarter ambiguity
pair. -/
def quarter_identified_ofWord (word : List BinaryDigit) :
    Identified (quarterLowerOfWord word) (quarterUpperOfWord word) :=
  identified_prependWord word quarter_identified

/-- Every finite dyadic subinterval inherits the canonical three-quarter
ambiguity pair. -/
def threeQuarter_identified_ofWord (word : List BinaryDigit) :
    Identified (threeQuarterLowerOfWord word) (threeQuarterUpperOfWord word) :=
  identified_prependWord word threeQuarter_identified

/-- The left endpoint of every finite dyadic subinterval lies strictly left of
its lower quarter presentation. -/
def leftEndpoint_strictQuarterLower_ofWord (word : List BinaryDigit) :
    StrictLeft (leftEndpointOfWord word) (quarterLowerOfWord word) :=
  strictLeft_prependWord word leftEndpoint_strictQuarterLower

/-- The upper quarter presentation of every finite dyadic subinterval lies
strictly left of its lower midpoint presentation. -/
def quarterUpper_strictMidpointLower_ofWord (word : List BinaryDigit) :
    StrictLeft (quarterUpperOfWord word) (midpointLowerOfWord word) :=
  strictLeft_prependWord word quarterUpper_strictMidpointLower

/-- The upper midpoint presentation of every finite dyadic subinterval lies
strictly left of its lower three-quarter presentation. -/
def midpointUpper_strictThreeQuarterLower_ofWord (word : List BinaryDigit) :
    StrictLeft (midpointUpperOfWord word) (threeQuarterLowerOfWord word) :=
  strictLeft_prependWord word midpointUpper_strictThreeQuarterLower

/-- The upper three-quarter presentation of every finite dyadic subinterval
lies strictly left of its right endpoint. -/
def threeQuarterUpper_strictRightEndpoint_ofWord (word : List BinaryDigit) :
    StrictLeft (threeQuarterUpperOfWord word) (rightEndpointOfWord word) :=
  strictLeft_prependWord word threeQuarterUpper_strictRightEndpoint

/-- The left endpoint of every finite dyadic subinterval lies strictly left of
its lower midpoint presentation. -/
def leftEndpoint_strictMidpointLower_ofWord (word : List BinaryDigit) :
    StrictLeft (leftEndpointOfWord word) (midpointLowerOfWord word) :=
  strictLeft_prependWord word leftEndpoint_strictMidpointLower

/-- The upper midpoint presentation of every finite dyadic subinterval lies
strictly left of its right endpoint. -/
def midpointUpper_strictRightEndpoint_ofWord (word : List BinaryDigit) :
    StrictLeft (midpointUpperOfWord word) (rightEndpointOfWord word) :=
  strictLeft_prependWord word midpointUpper_strictRightEndpoint

end DyadicPrelinePoint

end CoherenceCalculus
