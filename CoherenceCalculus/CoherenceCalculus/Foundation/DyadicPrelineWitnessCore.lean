import CoherenceCalculus.Foundation.DyadicPrelineCore

/-!
# Foundation.DyadicPrelineWitnessCore

Constructive finite comparison witnesses for dyadic pre-line presentations.

This layer adds explicit shallow split witnesses on top of the quotient-free
pre-line presentations. It does not claim total comparison for arbitrary
presentations; it records the certified finite witness patterns that already
yield clean strict comparison.
-/

namespace CoherenceCalculus

namespace DyadicPrelinePoint

/-- A root-stage left/right split witness between two pre-line presentations. -/
def rootSplitWitness
    {x y : DyadicPrelinePoint}
    (hx : x.digits 0 = BinaryDigit.left)
    (hy : y.digits 0 = BinaryDigit.right) :
    DyadicLeftRightWitness x.digits y.digits where
  stage := 0
  common_interval := rfl
  left_digit := hx
  right_digit := hy

/-- A stage-one split witness inside the left child of the root interval. -/
def leftChildSplitWitness
    {x y : DyadicPrelinePoint}
    (hx0 : x.digits 0 = BinaryDigit.left)
    (hy0 : y.digits 0 = BinaryDigit.left)
    (hx1 : x.digits 1 = BinaryDigit.left)
    (hy1 : y.digits 1 = BinaryDigit.right) :
    DyadicLeftRightWitness x.digits y.digits where
  stage := 1
  common_interval := by
    calc
      intervalsOfDigits x.digits 1 = leftChildInterval rootInterval := by
        rw [intervalsOfDigits, hx0]
        rw [show intervalsOfDigits x.digits 0 = rootInterval by rfl]
      _ = intervalsOfDigits y.digits 1 := by
        rw [intervalsOfDigits, hy0]
        rw [show intervalsOfDigits y.digits 0 = rootInterval by rfl]
  left_digit := hx1
  right_digit := hy1

/-- A stage-one split witness inside the right child of the root interval. -/
def rightChildSplitWitness
    {x y : DyadicPrelinePoint}
    (hx0 : x.digits 0 = BinaryDigit.right)
    (hy0 : y.digits 0 = BinaryDigit.right)
    (hx1 : x.digits 1 = BinaryDigit.left)
    (hy1 : y.digits 1 = BinaryDigit.right) :
    DyadicLeftRightWitness x.digits y.digits where
  stage := 1
  common_interval := by
    calc
      intervalsOfDigits x.digits 1 = rightChildInterval rootInterval := by
        rw [intervalsOfDigits, hx0]
        rw [show intervalsOfDigits x.digits 0 = rootInterval by rfl]
      _ = intervalsOfDigits y.digits 1 := by
        rw [intervalsOfDigits, hy0]
        rw [show intervalsOfDigits y.digits 0 = rootInterval by rfl]
  left_digit := hx1
  right_digit := hy1

/-- A stage-two split witness inside the left-left grandchild of the root
interval. -/
def leftLeftSplitWitness
    {x y : DyadicPrelinePoint}
    (hx0 : x.digits 0 = BinaryDigit.left)
    (hy0 : y.digits 0 = BinaryDigit.left)
    (hx1 : x.digits 1 = BinaryDigit.left)
    (hy1 : y.digits 1 = BinaryDigit.left)
    (hx2 : x.digits 2 = BinaryDigit.left)
    (hy2 : y.digits 2 = BinaryDigit.right) :
    DyadicLeftRightWitness x.digits y.digits where
  stage := 2
  common_interval := by
    have h1 : intervalsOfDigits x.digits 1 = intervalsOfDigits y.digits 1 := by
      exact intervalsOfDigits_step_eq_of_eq_left
        (n := 0)
        (show intervalsOfDigits x.digits 0 = intervalsOfDigits y.digits 0 by rfl)
        hx0 hy0
    exact intervalsOfDigits_step_eq_of_eq_left (n := 1) h1 hx1 hy1
  left_digit := hx2
  right_digit := hy2

/-- A stage-two split witness inside the left-right grandchild of the root
interval. -/
def leftRightSplitWitness
    {x y : DyadicPrelinePoint}
    (hx0 : x.digits 0 = BinaryDigit.left)
    (hy0 : y.digits 0 = BinaryDigit.left)
    (hx1 : x.digits 1 = BinaryDigit.right)
    (hy1 : y.digits 1 = BinaryDigit.right)
    (hx2 : x.digits 2 = BinaryDigit.left)
    (hy2 : y.digits 2 = BinaryDigit.right) :
    DyadicLeftRightWitness x.digits y.digits where
  stage := 2
  common_interval := by
    have h1 : intervalsOfDigits x.digits 1 = intervalsOfDigits y.digits 1 := by
      exact intervalsOfDigits_step_eq_of_eq_left
        (n := 0)
        (show intervalsOfDigits x.digits 0 = intervalsOfDigits y.digits 0 by rfl)
        hx0 hy0
    exact intervalsOfDigits_step_eq_of_eq_right (n := 1) h1 hx1 hy1
  left_digit := hx2
  right_digit := hy2

/-- A stage-two split witness inside the right-left grandchild of the root
interval. -/
def rightLeftSplitWitness
    {x y : DyadicPrelinePoint}
    (hx0 : x.digits 0 = BinaryDigit.right)
    (hy0 : y.digits 0 = BinaryDigit.right)
    (hx1 : x.digits 1 = BinaryDigit.left)
    (hy1 : y.digits 1 = BinaryDigit.left)
    (hx2 : x.digits 2 = BinaryDigit.left)
    (hy2 : y.digits 2 = BinaryDigit.right) :
    DyadicLeftRightWitness x.digits y.digits where
  stage := 2
  common_interval := by
    have h1 : intervalsOfDigits x.digits 1 = intervalsOfDigits y.digits 1 := by
      exact intervalsOfDigits_step_eq_of_eq_right
        (n := 0)
        (show intervalsOfDigits x.digits 0 = intervalsOfDigits y.digits 0 by rfl)
        hx0 hy0
    exact intervalsOfDigits_step_eq_of_eq_left (n := 1) h1 hx1 hy1
  left_digit := hx2
  right_digit := hy2

/-- A stage-two split witness inside the right-right grandchild of the root
interval. -/
def rightRightSplitWitness
    {x y : DyadicPrelinePoint}
    (hx0 : x.digits 0 = BinaryDigit.right)
    (hy0 : y.digits 0 = BinaryDigit.right)
    (hx1 : x.digits 1 = BinaryDigit.right)
    (hy1 : y.digits 1 = BinaryDigit.right)
    (hx2 : x.digits 2 = BinaryDigit.left)
    (hy2 : y.digits 2 = BinaryDigit.right) :
    DyadicLeftRightWitness x.digits y.digits where
  stage := 2
  common_interval := by
    have h1 : intervalsOfDigits x.digits 1 = intervalsOfDigits y.digits 1 := by
      exact intervalsOfDigits_step_eq_of_eq_right
        (n := 0)
        (show intervalsOfDigits x.digits 0 = intervalsOfDigits y.digits 0 by rfl)
        hx0 hy0
    exact intervalsOfDigits_step_eq_of_eq_right (n := 1) h1 hx1 hy1
  left_digit := hx2
  right_digit := hy2

/-- A root split followed by left/left refinement yields strict-left
comparison. -/
def strictLeft_of_rootSplit_next_left_left
    {x y : DyadicPrelinePoint}
    (hx0 : x.digits 0 = BinaryDigit.left)
    (hy0 : y.digits 0 = BinaryDigit.right)
    (hx1 : x.digits 1 = BinaryDigit.left)
    (hy1 : y.digits 1 = BinaryDigit.left) :
    StrictLeft x y :=
  (rootSplitWitness hx0 hy0).strict_two_steps_of_next_left_left hx1 hy1

/-- A root split followed by left/right refinement yields strict-left
comparison. -/
def strictLeft_of_rootSplit_next_left_right
    {x y : DyadicPrelinePoint}
    (hx0 : x.digits 0 = BinaryDigit.left)
    (hy0 : y.digits 0 = BinaryDigit.right)
    (hx1 : x.digits 1 = BinaryDigit.left)
    (hy1 : y.digits 1 = BinaryDigit.right) :
    StrictLeft x y :=
  (rootSplitWitness hx0 hy0).strict_two_steps_of_next_left_right hx1 hy1

/-- A root split followed by right/right refinement yields strict-left
comparison. -/
def strictLeft_of_rootSplit_next_right_right
    {x y : DyadicPrelinePoint}
    (hx0 : x.digits 0 = BinaryDigit.left)
    (hy0 : y.digits 0 = BinaryDigit.right)
    (hx1 : x.digits 1 = BinaryDigit.right)
    (hy1 : y.digits 1 = BinaryDigit.right) :
    StrictLeft x y :=
  (rootSplitWitness hx0 hy0).strict_two_steps_of_next_right_right hx1 hy1

/-- The canonical right-endpoint presentation induces the constant-right unit
point candidate. -/
theorem rightEndpoint_unitPoint :
    rightEndpoint.unitPoint = unitPointOfDigits (fun _ => BinaryDigit.right) := rfl

/-- The canonical endpoints already admit a strict-left comparison witness. -/
def leftEndpoint_strictRightEndpoint : StrictLeft leftEndpoint rightEndpoint :=
  strictLeft_of_rootSplit_next_left_right rfl rfl rfl rfl

/-- The canonical endpoints compare left-to-right. -/
def leftEndpoint_rightEndpoint_comparison : Comparison leftEndpoint rightEndpoint :=
  .strictLeft leftEndpoint_strictRightEndpoint

/-- The canonical left endpoint lies strictly left of the upper midpoint
presentation. -/
def leftEndpoint_strictMidpointUpper : StrictLeft leftEndpoint midpointUpper :=
  strictLeft_of_rootSplit_next_left_left rfl rfl rfl rfl

/-- The canonical left endpoint compares strictly left of the upper midpoint
presentation. -/
def leftEndpoint_midpointUpper_comparison : Comparison leftEndpoint midpointUpper :=
  .strictLeft leftEndpoint_strictMidpointUpper

/-- The lower midpoint presentation lies strictly left of the canonical right
endpoint. -/
def midpointLower_strictRightEndpoint : StrictLeft midpointLower rightEndpoint :=
  strictLeft_of_rootSplit_next_right_right rfl rfl rfl rfl

/-- The lower midpoint presentation compares strictly left of the canonical
right endpoint. -/
def midpointLower_rightEndpoint_comparison : Comparison midpointLower rightEndpoint :=
  .strictLeft midpointLower_strictRightEndpoint

/-- Stage-one left-child split witness for the canonical left endpoint and the
lower midpoint presentation. -/
def leftEndpoint_midpointLower_witness :
    DyadicLeftRightWitness leftEndpoint.digits midpointLower.digits :=
  leftChildSplitWitness rfl rfl rfl rfl

/-- The canonical left endpoint lies strictly left of the lower midpoint
presentation. -/
def leftEndpoint_strictMidpointLower : StrictLeft leftEndpoint midpointLower :=
  leftEndpoint_midpointLower_witness.strict_two_steps_of_next_left_right rfl rfl

/-- The canonical left endpoint compares strictly left of the lower midpoint
presentation. -/
def leftEndpoint_midpointLower_comparison : Comparison leftEndpoint midpointLower :=
  .strictLeft leftEndpoint_strictMidpointLower

/-- Stage-one right-child split witness for the upper midpoint presentation and
the canonical right endpoint. -/
def midpointUpper_rightEndpoint_witness :
    DyadicLeftRightWitness midpointUpper.digits rightEndpoint.digits :=
  rightChildSplitWitness rfl rfl rfl rfl

/-- The upper midpoint presentation lies strictly left of the canonical right
endpoint. -/
def midpointUpper_strictRightEndpoint : StrictLeft midpointUpper rightEndpoint :=
  midpointUpper_rightEndpoint_witness.strict_two_steps_of_next_left_right rfl rfl

/-- The upper midpoint presentation compares strictly left of the canonical
right endpoint. -/
def midpointUpper_rightEndpoint_comparison : Comparison midpointUpper rightEndpoint :=
  .strictLeft midpointUpper_strictRightEndpoint

/-- Stage-one left-child split witness for the canonical quarter ambiguity
pair. -/
def quarter_witness :
    DyadicLeftRightWitness quarterLower.digits quarterUpper.digits :=
  leftChildSplitWitness rfl rfl rfl rfl

/-- The canonical quarter ambiguity pair forms an explicit ambiguous-tail
witness. -/
def quarter_ambiguousWitness :
    DyadicAmbiguousWitness quarterLower.digits quarterUpper.digits where
  split := quarter_witness
  inward_left := by
    intro m
    have hIndex : quarter_witness.stage + 1 + m = m + 2 := by
      rw [show quarter_witness.stage = 1 by rfl]
      calc
        1 + 1 + m = 2 + m := by rfl
        _ = m + 2 := Nat.add_comm 2 m
    rw [hIndex]
    rfl
  inward_right := by
    intro m
    have hIndex : quarter_witness.stage + 1 + m = m + 2 := by
      rw [show quarter_witness.stage = 1 by rfl]
      calc
        1 + 1 + m = 2 + m := by rfl
        _ = m + 2 := Nat.add_comm 2 m
    rw [hIndex]
    rfl

/-- The canonical quarter ambiguity pair is boundary-identified. -/
def quarter_identified : Identified quarterLower quarterUpper :=
  .ambiguousLeftRight quarter_ambiguousWitness

/-- The canonical quarter ambiguity pair is comparable as an identified pair. -/
def quarter_comparison : Comparison quarterLower quarterUpper :=
  .identified quarter_identified

/-- The canonical quarter ambiguity pair is also identified in the reverse
orientation. -/
def quarter_identified_symm : Identified quarterUpper quarterLower :=
  identified_symm quarter_identified

/-- Stage-one right-child split witness for the canonical three-quarter
ambiguity pair. -/
def threeQuarter_witness :
    DyadicLeftRightWitness threeQuarterLower.digits threeQuarterUpper.digits :=
  rightChildSplitWitness rfl rfl rfl rfl

/-- The canonical three-quarter ambiguity pair forms an explicit ambiguous-tail
witness. -/
def threeQuarter_ambiguousWitness :
    DyadicAmbiguousWitness threeQuarterLower.digits threeQuarterUpper.digits where
  split := threeQuarter_witness
  inward_left := by
    intro m
    have hIndex : threeQuarter_witness.stage + 1 + m = m + 2 := by
      rw [show threeQuarter_witness.stage = 1 by rfl]
      calc
        1 + 1 + m = 2 + m := by rfl
        _ = m + 2 := Nat.add_comm 2 m
    rw [hIndex]
    rfl
  inward_right := by
    intro m
    have hIndex : threeQuarter_witness.stage + 1 + m = m + 2 := by
      rw [show threeQuarter_witness.stage = 1 by rfl]
      calc
        1 + 1 + m = 2 + m := by rfl
        _ = m + 2 := Nat.add_comm 2 m
    rw [hIndex]
    rfl

/-- The canonical three-quarter ambiguity pair is boundary-identified. -/
def threeQuarter_identified : Identified threeQuarterLower threeQuarterUpper :=
  .ambiguousLeftRight threeQuarter_ambiguousWitness

/-- The canonical three-quarter ambiguity pair is comparable as an identified
pair. -/
def threeQuarter_comparison : Comparison threeQuarterLower threeQuarterUpper :=
  .identified threeQuarter_identified

/-- The canonical three-quarter ambiguity pair is also identified in the
reverse orientation. -/
def threeQuarter_identified_symm :
    Identified threeQuarterUpper threeQuarterLower :=
  identified_symm threeQuarter_identified

/-- Stage-two left-left split witness for the canonical left endpoint and the
lower quarter presentation. -/
def leftEndpoint_quarterLower_witness :
    DyadicLeftRightWitness leftEndpoint.digits quarterLower.digits :=
  leftLeftSplitWitness rfl rfl rfl rfl rfl rfl

/-- The canonical left endpoint lies strictly left of the lower quarter
presentation. -/
def leftEndpoint_strictQuarterLower : StrictLeft leftEndpoint quarterLower :=
  leftEndpoint_quarterLower_witness.strict_two_steps_of_next_left_right rfl rfl

/-- The canonical left endpoint compares strictly left of the lower quarter
presentation. -/
def leftEndpoint_quarterLower_comparison : Comparison leftEndpoint quarterLower :=
  .strictLeft leftEndpoint_strictQuarterLower

/-- Stage-two left-right split witness for the upper quarter presentation and
the lower midpoint presentation. -/
def quarterUpper_midpointLower_witness :
    DyadicLeftRightWitness quarterUpper.digits midpointLower.digits :=
  leftRightSplitWitness rfl rfl rfl rfl rfl rfl

/-- The upper quarter presentation lies strictly left of the lower midpoint
presentation. -/
def quarterUpper_strictMidpointLower : StrictLeft quarterUpper midpointLower :=
  quarterUpper_midpointLower_witness.strict_two_steps_of_next_left_right rfl rfl

/-- The upper quarter presentation compares strictly left of the lower midpoint
presentation. -/
def quarterUpper_midpointLower_comparison : Comparison quarterUpper midpointLower :=
  .strictLeft quarterUpper_strictMidpointLower

/-- Stage-two right-left split witness for the upper midpoint presentation and
the lower three-quarter presentation. -/
def midpointUpper_threeQuarterLower_witness :
    DyadicLeftRightWitness midpointUpper.digits threeQuarterLower.digits :=
  rightLeftSplitWitness rfl rfl rfl rfl rfl rfl

/-- The upper midpoint presentation lies strictly left of the lower
three-quarter presentation. -/
def midpointUpper_strictThreeQuarterLower :
    StrictLeft midpointUpper threeQuarterLower :=
  midpointUpper_threeQuarterLower_witness.strict_two_steps_of_next_left_right rfl rfl

/-- The upper midpoint presentation compares strictly left of the lower
three-quarter presentation. -/
def midpointUpper_threeQuarterLower_comparison :
    Comparison midpointUpper threeQuarterLower :=
  .strictLeft midpointUpper_strictThreeQuarterLower

/-- Stage-two right-right split witness for the upper three-quarter
presentation and the canonical right endpoint. -/
def threeQuarterUpper_rightEndpoint_witness :
    DyadicLeftRightWitness threeQuarterUpper.digits rightEndpoint.digits :=
  rightRightSplitWitness rfl rfl rfl rfl rfl rfl

/-- The upper three-quarter presentation lies strictly left of the canonical
right endpoint. -/
def threeQuarterUpper_strictRightEndpoint :
    StrictLeft threeQuarterUpper rightEndpoint :=
  threeQuarterUpper_rightEndpoint_witness.strict_two_steps_of_next_left_right rfl rfl

/-- The upper three-quarter presentation compares strictly left of the
canonical right endpoint. -/
def threeQuarterUpper_rightEndpoint_comparison :
    Comparison threeQuarterUpper rightEndpoint :=
  .strictLeft threeQuarterUpper_strictRightEndpoint

end DyadicPrelinePoint

end CoherenceCalculus
