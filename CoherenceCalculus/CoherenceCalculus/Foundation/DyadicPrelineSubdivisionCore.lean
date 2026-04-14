import CoherenceCalculus.Foundation.DyadicPrelinePrefixCore

/-!
# Foundation.DyadicPrelineSubdivisionCore

Generic finite dyadic subdivision on the quotient-free pre-line.

This layer converts the prefixed landmark transport into a true finite
subdivision language. Every finite binary word determines a dyadic subinterval
with:

- persistent exterior boundaries
- a classified shared child boundary
- strict left/right order from the exterior boundaries to the split boundary

The point is to phrase the dyadic line as a recursive hierarchy of finite
subintervals, not as a disconnected list of isolated named examples.
-/

namespace CoherenceCalculus

namespace DyadicPrelinePoint

/-- Prepending a concatenated word is the same as successive prefix transport. -/
theorem prependWord_append
    (word₁ word₂ : List BinaryDigit) (x : DyadicPrelinePoint) :
    prependWord (word₁ ++ word₂) x = prependWord word₁ (prependWord word₂ x) := by
  induction word₁ generalizing x with
  | nil =>
      rfl
  | cons b word ih =>
      change prependDigit b (prependWord (word ++ word₂) x) =
          prependDigit b (prependWord word (prependWord word₂ x))
      rw [ih]

/-- Prepending `left` to the canonical left endpoint preserves its interval
thread exactly. -/
theorem leftEndpoint_prependLeft_exact :
    ∀ n,
      intervalsOfDigits leftEndpoint.digits n =
        intervalsOfDigits (prependLeft leftEndpoint).digits n
  | 0 => rfl
  | n + 1 => by
      calc
        intervalsOfDigits leftEndpoint.digits (n + 1)
            = leftChildInterval (intervalsOfDigits leftEndpoint.digits n) := by
                rw [intervalsOfDigits]
                rfl
        _ = leftChildInterval (intervalsOfDigits (prependLeft leftEndpoint).digits n) := by
              rw [leftEndpoint_prependLeft_exact n]
        _ = intervalsOfDigits (prependLeft leftEndpoint).digits (n + 1) := by
              rw [intervalsOfDigits]
              cases n with
              | zero =>
                  rfl
              | succ n =>
                  rfl

/-- Prepending `right` to the canonical right endpoint preserves its interval
thread exactly. -/
theorem rightEndpoint_prependRight_exact :
    ∀ n,
      intervalsOfDigits rightEndpoint.digits n =
        intervalsOfDigits (prependRight rightEndpoint).digits n
  | 0 => rfl
  | n + 1 => by
      calc
        intervalsOfDigits rightEndpoint.digits (n + 1)
            = rightChildInterval (intervalsOfDigits rightEndpoint.digits n) := by
                rw [intervalsOfDigits]
                rfl
        _ = rightChildInterval (intervalsOfDigits (prependRight rightEndpoint).digits n) := by
              rw [rightEndpoint_prependRight_exact n]
        _ = intervalsOfDigits (prependRight rightEndpoint).digits (n + 1) := by
              rw [intervalsOfDigits]
              cases n with
              | zero =>
                  rfl
              | succ n =>
                  rfl

/-- The canonical left endpoint is exactly identified with its left-prefixed
presentation. -/
def leftEndpoint_identifies_prependLeft : Identified leftEndpoint (prependLeft leftEndpoint) :=
  .exact leftEndpoint_prependLeft_exact

/-- The canonical right endpoint is exactly identified with its right-prefixed
presentation. -/
def rightEndpoint_identifies_prependRight : Identified rightEndpoint (prependRight rightEndpoint) :=
  .exact rightEndpoint_prependRight_exact

/-- Lower presentation of the shared child boundary in the dyadic subinterval
determined by a finite prefix. -/
def splitBoundaryLowerOfWord (word : List BinaryDigit) : DyadicPrelinePoint :=
  rightEndpointOfWord (word ++ [BinaryDigit.left])

/-- Upper presentation of the shared child boundary in the dyadic subinterval
determined by a finite prefix. -/
def splitBoundaryUpperOfWord (word : List BinaryDigit) : DyadicPrelinePoint :=
  leftEndpointOfWord (word ++ [BinaryDigit.right])

/-- Every prefixed dyadic subinterval has distinct left and right boundaries. -/
def leftEndpoint_strictRightEndpoint_ofWord (word : List BinaryDigit) :
    StrictLeft (leftEndpointOfWord word) (rightEndpointOfWord word) :=
  strictLeft_prependWord word leftEndpoint_strictRightEndpoint

/-- Every prefixed dyadic subinterval has a clean left-to-right comparison from
its left boundary to its right boundary. -/
def leftEndpoint_rightEndpoint_comparison_ofWord (word : List BinaryDigit) :
    Comparison (leftEndpointOfWord word) (rightEndpointOfWord word) :=
  .strictLeft (leftEndpoint_strictRightEndpoint_ofWord word)

/-- The split boundary in every prefixed dyadic subinterval is identified
across its left-child and right-child presentations. -/
def splitBoundary_identified_ofWord (word : List BinaryDigit) :
    Identified (splitBoundaryLowerOfWord word) (splitBoundaryUpperOfWord word) := by
  unfold splitBoundaryLowerOfWord splitBoundaryUpperOfWord rightEndpointOfWord leftEndpointOfWord
  rw [prependWord_append, prependWord_append]
  change Identified (prependWord word midpointLower) (prependWord word midpointUpper)
  exact midpoint_identified_ofWord word

/-- The split boundary in every prefixed dyadic subinterval is comparable as an
identified pair. -/
def splitBoundary_comparison_ofWord (word : List BinaryDigit) :
    Comparison (splitBoundaryLowerOfWord word) (splitBoundaryUpperOfWord word) :=
  .identified (splitBoundary_identified_ofWord word)

/-- The exterior left boundary of every prefixed dyadic subinterval is exactly
identified with the exterior left boundary of its left child. -/
def leftEndpoint_identifies_leftChildBoundary_ofWord (word : List BinaryDigit) :
    Identified (leftEndpointOfWord word) (leftEndpointOfWord (word ++ [BinaryDigit.left])) := by
  unfold leftEndpointOfWord
  rw [prependWord_append]
  exact identified_prependWord word leftEndpoint_identifies_prependLeft

/-- The exterior right boundary of every prefixed dyadic subinterval is exactly
identified with the exterior right boundary of its right child. -/
def rightChildBoundary_identifies_rightEndpoint_ofWord (word : List BinaryDigit) :
    Identified (rightEndpointOfWord (word ++ [BinaryDigit.right])) (rightEndpointOfWord word) := by
  unfold rightEndpointOfWord
  rw [prependWord_append]
  exact identified_symm (identified_prependWord word rightEndpoint_identifies_prependRight)

/-- In every prefixed dyadic subinterval, the exterior left boundary lies
strictly left of the lower split-boundary presentation. -/
def leftEndpoint_strict_splitBoundaryLower_ofWord (word : List BinaryDigit) :
    StrictLeft (leftEndpointOfWord word) (splitBoundaryLowerOfWord word) := by
  unfold splitBoundaryLowerOfWord rightEndpointOfWord
  rw [prependWord_append]
  change StrictLeft (leftEndpointOfWord word) (prependWord word midpointLower)
  exact leftEndpoint_strictMidpointLower_ofWord word

/-- In every prefixed dyadic subinterval, the upper split-boundary presentation
lies strictly left of the exterior right boundary. -/
def splitBoundaryUpper_strict_rightEndpoint_ofWord (word : List BinaryDigit) :
    StrictLeft (splitBoundaryUpperOfWord word) (rightEndpointOfWord word) := by
  unfold splitBoundaryUpperOfWord leftEndpointOfWord
  rw [prependWord_append]
  change StrictLeft (prependWord word midpointUpper) (rightEndpointOfWord word)
  exact midpointUpper_strictRightEndpoint_ofWord word

end DyadicPrelinePoint

end CoherenceCalculus
