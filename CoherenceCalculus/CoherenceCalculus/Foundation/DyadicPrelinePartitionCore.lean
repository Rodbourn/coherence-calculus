import CoherenceCalculus.Foundation.DyadicPrelineSubdivisionCore

/-!
# Foundation.DyadicPrelinePartitionCore

Recursive finite partition order on the dyadic pre-line.

This module turns the generic subdivision frame into a recursive comparison
calculus over finite binary words. The key notion is a forward comparison:
either exact identification or strict left-to-right separation. This is the
orientation that composes cleanly through recursive finite subdivisions.
-/

namespace CoherenceCalculus

namespace DyadicPrelinePoint

/-- Forward comparison on the dyadic pre-line means either exact identification
or strict left-to-right separation. -/
inductive ForwardComparison (x y : DyadicPrelinePoint) : Type where
  | identified : Identified x y → ForwardComparison x y
  | strictLeft : StrictLeft x y → ForwardComparison x y

namespace ForwardComparison

/-- Forget a forward comparison to the ambient quotient-free comparison type. -/
def toComparison {x y : DyadicPrelinePoint} :
    ForwardComparison x y → Comparison x y
  | .identified h => .identified h
  | .strictLeft s => .strictLeft s

/-- Forward comparison composes transitively. -/
def trans {x y z : DyadicPrelinePoint} :
    ForwardComparison x y → ForwardComparison y z → ForwardComparison x z
  | .identified hxy, .identified hyz =>
      .identified (identified_trans hxy hyz)
  | .identified hxy, .strictLeft syz =>
      .strictLeft (DyadicStrictSeparation.of_identified_left hxy syz)
  | .strictLeft sxy, .identified hyz =>
      .strictLeft (DyadicStrictSeparation.of_identified_right sxy hyz)
  | .strictLeft sxy, .strictLeft syz =>
      .strictLeft (sxy.trans syz)

end ForwardComparison

/-- In every prefixed dyadic subinterval, the exterior left boundary lies
strictly left of the right child's left boundary. -/
def leftEndpoint_strict_rightChildBoundary_ofWord (word : List BinaryDigit) :
    StrictLeft (leftEndpointOfWord word) (leftEndpointOfWord (word ++ [BinaryDigit.right])) :=
  DyadicStrictSeparation.of_identified_right
    (leftEndpoint_strict_splitBoundaryLower_ofWord word)
    (splitBoundary_identified_ofWord word)

/-- In every prefixed dyadic subinterval, the left child's right boundary lies
strictly left of the exterior right boundary. -/
def leftChildBoundary_strict_rightEndpoint_ofWord (word : List BinaryDigit) :
    StrictLeft (rightEndpointOfWord (word ++ [BinaryDigit.left])) (rightEndpointOfWord word) :=
  DyadicStrictSeparation.of_identified_left
    (splitBoundary_identified_ofWord word)
    (splitBoundaryUpper_strict_rightEndpoint_ofWord word)

/-- The parent left boundary compares forward to the left boundary of any
finite descendant subinterval. -/
noncomputable def leftEndpoint_forward_ofSuffix
    (word : List BinaryDigit) (suffix : List BinaryDigit) :
    ForwardComparison
      (leftEndpointOfWord word)
      (leftEndpointOfWord (word ++ suffix)) := by
  induction suffix generalizing word with
  | nil =>
      rw [List.append_nil]
      exact .identified (identified_refl (leftEndpointOfWord word))
  | cons b suffix ih =>
      cases b with
      | left =>
          have hStep :
              ForwardComparison
                (leftEndpointOfWord word)
                (leftEndpointOfWord (word ++ [BinaryDigit.left])) :=
            .identified (leftEndpoint_identifies_leftChildBoundary_ofWord word)
          have hTail :
              ForwardComparison
                (leftEndpointOfWord (word ++ [BinaryDigit.left]))
                (leftEndpointOfWord ((word ++ [BinaryDigit.left]) ++ suffix)) :=
            ih (word ++ [BinaryDigit.left])
          have hAssoc :
              word ++ BinaryDigit.left :: suffix =
                (word ++ [BinaryDigit.left]) ++ suffix := by
            calc
              word ++ BinaryDigit.left :: suffix
                  = word ++ ([BinaryDigit.left] ++ suffix) := by
                      exact congrArg (List.append word)
                        (show BinaryDigit.left :: suffix = [BinaryDigit.left] ++ suffix by rfl)
              _ = (word ++ [BinaryDigit.left]) ++ suffix := by
                    exact (List.append_assoc word [BinaryDigit.left] suffix).symm
          have hComp :
              ForwardComparison
                (leftEndpointOfWord word)
                (leftEndpointOfWord ((word ++ [BinaryDigit.left]) ++ suffix)) :=
            ForwardComparison.trans hStep hTail
          exact hAssoc ▸ hComp
      | right =>
          have hStep :
              ForwardComparison
                (leftEndpointOfWord word)
                (leftEndpointOfWord (word ++ [BinaryDigit.right])) :=
            .strictLeft (leftEndpoint_strict_rightChildBoundary_ofWord word)
          have hTail :
              ForwardComparison
                (leftEndpointOfWord (word ++ [BinaryDigit.right]))
                (leftEndpointOfWord ((word ++ [BinaryDigit.right]) ++ suffix)) :=
            ih (word ++ [BinaryDigit.right])
          have hAssoc :
              word ++ BinaryDigit.right :: suffix =
                (word ++ [BinaryDigit.right]) ++ suffix := by
            calc
              word ++ BinaryDigit.right :: suffix
                  = word ++ ([BinaryDigit.right] ++ suffix) := by
                      exact congrArg (List.append word)
                        (show BinaryDigit.right :: suffix = [BinaryDigit.right] ++ suffix by rfl)
              _ = (word ++ [BinaryDigit.right]) ++ suffix := by
                    exact (List.append_assoc word [BinaryDigit.right] suffix).symm
          have hComp :
              ForwardComparison
                (leftEndpointOfWord word)
                (leftEndpointOfWord ((word ++ [BinaryDigit.right]) ++ suffix)) :=
            ForwardComparison.trans hStep hTail
          exact hAssoc ▸ hComp

/-- The right boundary of any finite descendant subinterval compares forward to
the parent right boundary. -/
noncomputable def rightEndpoint_forward_toPrefix
    (word : List BinaryDigit) (suffix : List BinaryDigit) :
    ForwardComparison
      (rightEndpointOfWord (word ++ suffix))
      (rightEndpointOfWord word) := by
  induction suffix generalizing word with
  | nil =>
      rw [List.append_nil]
      exact .identified (identified_refl (rightEndpointOfWord word))
  | cons b suffix ih =>
      cases b with
      | left =>
          have hTail :
              ForwardComparison
                (rightEndpointOfWord ((word ++ [BinaryDigit.left]) ++ suffix))
                (rightEndpointOfWord (word ++ [BinaryDigit.left])) :=
            ih (word ++ [BinaryDigit.left])
          have hStep :
              ForwardComparison
                (rightEndpointOfWord (word ++ [BinaryDigit.left]))
                (rightEndpointOfWord word) :=
            .strictLeft (leftChildBoundary_strict_rightEndpoint_ofWord word)
          have hAssoc :
              word ++ BinaryDigit.left :: suffix =
                (word ++ [BinaryDigit.left]) ++ suffix := by
            calc
              word ++ BinaryDigit.left :: suffix
                  = word ++ ([BinaryDigit.left] ++ suffix) := by
                      exact congrArg (List.append word)
                        (show BinaryDigit.left :: suffix = [BinaryDigit.left] ++ suffix by rfl)
              _ = (word ++ [BinaryDigit.left]) ++ suffix := by
                    exact (List.append_assoc word [BinaryDigit.left] suffix).symm
          have hComp :
              ForwardComparison
                (rightEndpointOfWord ((word ++ [BinaryDigit.left]) ++ suffix))
                (rightEndpointOfWord word) :=
            ForwardComparison.trans hTail hStep
          exact hAssoc ▸ hComp
      | right =>
          have hTail :
              ForwardComparison
                (rightEndpointOfWord ((word ++ [BinaryDigit.right]) ++ suffix))
                (rightEndpointOfWord (word ++ [BinaryDigit.right])) :=
            ih (word ++ [BinaryDigit.right])
          have hStep :
              ForwardComparison
                (rightEndpointOfWord (word ++ [BinaryDigit.right]))
                (rightEndpointOfWord word) :=
            .identified (rightChildBoundary_identifies_rightEndpoint_ofWord word)
          have hAssoc :
              word ++ BinaryDigit.right :: suffix =
                (word ++ [BinaryDigit.right]) ++ suffix := by
            calc
              word ++ BinaryDigit.right :: suffix
                  = word ++ ([BinaryDigit.right] ++ suffix) := by
                      exact congrArg (List.append word)
                        (show BinaryDigit.right :: suffix = [BinaryDigit.right] ++ suffix by rfl)
              _ = (word ++ [BinaryDigit.right]) ++ suffix := by
                    exact (List.append_assoc word [BinaryDigit.right] suffix).symm
          have hComp :
              ForwardComparison
                (rightEndpointOfWord ((word ++ [BinaryDigit.right]) ++ suffix))
                (rightEndpointOfWord word) :=
            ForwardComparison.trans hTail hStep
          exact hAssoc ▸ hComp

/-- Any boundary in the left child of a dyadic subinterval compares forward to
any boundary in the right child of the same dyadic subinterval. -/
noncomputable def siblingBoundary_forward
    (word leftSuffix rightSuffix : List BinaryDigit) :
    ForwardComparison
      (rightEndpointOfWord ((word ++ [BinaryDigit.left]) ++ leftSuffix))
      (leftEndpointOfWord ((word ++ [BinaryDigit.right]) ++ rightSuffix)) := by
  have hLeft :
      ForwardComparison
        (rightEndpointOfWord ((word ++ [BinaryDigit.left]) ++ leftSuffix))
        (rightEndpointOfWord (word ++ [BinaryDigit.left])) := by
    exact rightEndpoint_forward_toPrefix (word ++ [BinaryDigit.left]) leftSuffix
  have hMid :
      ForwardComparison
        (rightEndpointOfWord (word ++ [BinaryDigit.left]))
        (leftEndpointOfWord (word ++ [BinaryDigit.right])) :=
    .identified (splitBoundary_identified_ofWord word)
  have hRight :
      ForwardComparison
        (leftEndpointOfWord (word ++ [BinaryDigit.right]))
        (leftEndpointOfWord ((word ++ [BinaryDigit.right]) ++ rightSuffix)) := by
    exact leftEndpoint_forward_ofSuffix (word ++ [BinaryDigit.right]) rightSuffix
  exact ForwardComparison.trans hLeft (ForwardComparison.trans hMid hRight)

/-- The sibling-boundary comparison forgets to an ambient quotient-free
comparison. -/
noncomputable def siblingBoundary_comparison
    (word leftSuffix rightSuffix : List BinaryDigit) :
    Comparison
      (rightEndpointOfWord ((word ++ [BinaryDigit.left]) ++ leftSuffix))
      (leftEndpointOfWord ((word ++ [BinaryDigit.right]) ++ rightSuffix)) :=
  (siblingBoundary_forward word leftSuffix rightSuffix).toComparison

end DyadicPrelinePoint

end CoherenceCalculus
