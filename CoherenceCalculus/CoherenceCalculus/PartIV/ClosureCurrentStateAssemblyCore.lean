import CoherenceCalculus.PartIV.ClosureCurrentAutonomyLawCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentStateAssemblyCore

Explicit state assembly for the detached closure-current lane.

`ClosureCurrentAutonomyLawCore` reduced the detached flagship equation to one
unified selected-cut state field, but still through an arbitrary hidden-state
realization

`PairExchangeCurrent -> State`.

This file replaces that black-box realization by the first explicit current-side
assembly:

* a signed readout on pair-current values;
* a four-leg frame for the first closure-stable bulk event;
* a concrete state obtained by summing the oriented pair current incident to
  each framed leg.

The resulting package is still detached from the certified bedrock spine. Its
role is narrower and honest: it shows that the hidden current can already be
read as a concrete four-coordinate state before any carrier-level PDE or
analytic representative is chosen.
-/

namespace ClosureCurrent

/-- Signed visible readout of one pair-current carrier value. This is the
smallest additional realization layer needed to turn the detached current into
an explicit `State`: a zero value reads as zero signed count, and reversal
reads as signed negation. -/
structure SignedExchangeReadout (carrier : PairExchangeCarrier) where
  toSignedCount : carrier.Value → SignedCount
  map_zero : toSignedCount carrier.zero = SignedCount.zero
  map_reverse :
    ∀ x : carrier.Value,
      toSignedCount (carrier.reverse x) = SignedCount.negate (toSignedCount x)

/-- Explicit four-leg frame for the first closure-stable bulk event. The
pairwise distinctness clauses keep the frame honest as a genuine four-leg local
carrier rather than a repeated-coordinate encoding. -/
structure FourLegFrame (Leg : Type) where
  l0 : Leg
  l1 : Leg
  l2 : Leg
  l3 : Leg
  l01 : l0 ≠ l1
  l02 : l0 ≠ l2
  l03 : l0 ≠ l3
  l12 : l1 ≠ l2
  l13 : l1 ≠ l3
  l23 : l2 ≠ l3

/-- The `i`-th leg of the four-leg frame. -/
def FourLegFrame.at
    {Leg : Type}
    (frame : FourLegFrame Leg) :
    Fin 4 → Leg
  | ⟨0, _⟩ => frame.l0
  | ⟨1, _⟩ => frame.l1
  | ⟨2, _⟩ => frame.l2
  | ⟨3, _⟩ => frame.l3

/-- Signed sum of the current emitted from one leg to the four framed legs. -/
def legFlux
    {carrier : PairExchangeCarrier}
    {Leg : Type}
    (readout : SignedExchangeReadout carrier)
    (frame : FourLegFrame Leg)
    (current : PairExchangeCurrent carrier Leg)
    (leg : Leg) :
    SignedCount :=
  SignedCount.addCount
    (SignedCount.addCount
      (readout.toSignedCount (current.value leg frame.l0))
      (readout.toSignedCount (current.value leg frame.l1)))
    (SignedCount.addCount
      (readout.toSignedCount (current.value leg frame.l2))
      (readout.toSignedCount (current.value leg frame.l3)))

/-- Explicit state assembled from the pair current by reading the net signed
pair flux at each framed leg. -/
def assembledState
    {carrier : PairExchangeCarrier}
    {Leg : Type}
    (readout : SignedExchangeReadout carrier)
    (frame : FourLegFrame Leg)
    (current : PairExchangeCurrent carrier Leg) :
    State :=
  ⟨legFlux readout frame current frame.l0,
    legFlux readout frame current frame.l1,
    legFlux readout frame current frame.l2,
    legFlux readout frame current frame.l3⟩

/-- Canonical six-slot readout of a framed pair current. Once a genuine
four-leg frame is fixed, the unordered pair slots are exactly the six
diophantine slots counted by `binomial 4 2`. -/
def localSlotReadout
    {carrier : PairExchangeCarrier}
    {Leg : Type}
    (readout : SignedExchangeReadout carrier)
    (frame : FourLegFrame Leg)
    (current : PairExchangeCurrent carrier Leg) :
    LocalSlotCarrier
  | .s12 => readout.toSignedCount (current.value frame.l0 frame.l1)
  | .s13 => readout.toSignedCount (current.value frame.l0 frame.l2)
  | .s14 => readout.toSignedCount (current.value frame.l0 frame.l3)
  | .s23 => readout.toSignedCount (current.value frame.l1 frame.l2)
  | .s24 => readout.toSignedCount (current.value frame.l1 frame.l3)
  | .s34 => readout.toSignedCount (current.value frame.l2 frame.l3)

/-- Current-side name for the canonical intrinsic six-slot overlap law from
Part I. -/
abbrev localSlotOverlapLaw : LocalSlot → LocalSlot → SignedCount :=
  canonicalIntrinsicOverlapLaw

/-- The current-side overlap law inherits intrinsic adjacency invariance from
the Part I canonical six-slot law. -/
theorem localSlotOverlapLaw_intrinsic :
    IntrinsicAdjacencyInvariant localSlotOverlapLaw := by
  exact canonicalIntrinsicOverlapLaw_intrinsic

/-- The Part I six-slot channel calculus already applies to the canonical
overlap law on the local pair carrier. -/
theorem localSlotOverlapLaw_channelSurface :
    ∃ a b c : SignedCount,
      ∃ l1 l2 l3 : SignedCount,
        (∀ α β : LocalSlot,
          localSlotOverlapLaw α β =
            match intrinsicSlotAdjacency α β with
            | .equal => a
            | .adjacent => b
            | .disjoint => c) ∧
        l1 =
          SignedCount.addCount
            (SignedCount.addCount a (signedCount_nsmul 4 b)) c ∧
        l2 =
          SignedCount.addCount
            (SignedCount.subCount a (signedCount_nsmul 2 b)) c ∧
        l3 = SignedCount.subCount a c := by
  exact canonicalIntrinsicOverlapLaw_channelSurface

/-- Current-side name for the Part I canonical overlap parameters. -/
abbrev canonicalLocalSlotOverlapParameters : IntrinsicSlotParameters :=
  canonicalIntrinsicOverlapParameters

/-- The current-side overlap law inherits its normal form from the Part I
canonical six-slot law. -/
theorem localSlotOverlapLaw_normalForm :
    isIntrinsicNormalForm
      localSlotOverlapLaw
      canonicalLocalSlotOverlapParameters := by
  exact canonicalIntrinsicOverlapLaw_normalForm

/-- The current-side overlap law inherits unique canonical normal form from the
Part I six-slot carrier calculus. -/
theorem localSlotOverlapLaw_existsUniqueCanonicalNormalForm :
    ∃ p : IntrinsicSlotParameters,
      (isIntrinsicNormalForm localSlotOverlapLaw p ∧
        p.diagonal = SignedCount.ofNat 2 ∧
        p.adjacent = SignedCount.ofNat 1 ∧
        p.disjoint = SignedCount.zero) ∧
      ∀ q : IntrinsicSlotParameters,
        (isIntrinsicNormalForm localSlotOverlapLaw q ∧
          q.diagonal = SignedCount.ofNat 2 ∧
          q.adjacent = SignedCount.ofNat 1 ∧
          q.disjoint = SignedCount.zero) →
        q = p := by
  exact canonicalIntrinsicOverlapLaw_existsUniqueCanonicalNormalForm

/-- Any six-slot law in canonical normal form `(2, 1, 0)` already agrees
pointwise with the current-side overlap law. This is the rigid current-side
law imported from the Part I carrier calculus. -/
theorem pointwise_eq_localSlotOverlapLaw_of_normalForm
    {A : LocalSlot → LocalSlot → SignedCount}
    {p : IntrinsicSlotParameters}
    (hA : isIntrinsicNormalForm A p)
    (hdiag : p.diagonal = SignedCount.ofNat 2)
    (hadj : p.adjacent = SignedCount.ofNat 1)
    (hdis : p.disjoint = SignedCount.zero) :
    ∀ α β : LocalSlot, A α β = localSlotOverlapLaw α β := by
  exact pointwise_eq_canonicalIntrinsicOverlapLaw_of_normalForm hA hdiag hadj hdis

/-- Total signed content of a visible state. -/
def stateTotal (x : State) : SignedCount :=
  SignedCount.addCount
    (SignedCount.addCount x.c0 x.c1)
    (SignedCount.addCount x.c2 x.c3)

/-- Balanced visible state: the total signed content vanishes. -/
structure BalancedState where
  toState : State
  balanced : stateTotal toState = SignedCount.zero

namespace BalancedState

/-- Extensionality for balanced states: the visible state determines the
balanced-state package. -/
theorem ext {x y : BalancedState} (h : x.toState = y.toState) : x = y := by
  cases x with
  | mk xState xBalanced =>
      cases y with
      | mk yState yBalanced =>
          cases h
          have hproof : xBalanced = yBalanced := Subsingleton.elim _ _
          cases hproof
          rfl

end BalancedState

private theorem signedCount_negate_negate (a : SignedCount) :
    SignedCount.negate (SignedCount.negate a) = a := by
  apply SignedCount.ext <;> rfl

private theorem signedCount_negate_zero :
    SignedCount.negate SignedCount.zero = SignedCount.zero := by
  apply SignedCount.ext <;> rfl

private theorem signedCount_negate_addCount (a b : SignedCount) :
    SignedCount.negate (SignedCount.addCount a b) =
      SignedCount.addCount (SignedCount.negate a) (SignedCount.negate b) := by
  apply signedCount_eq_of_rawEquivalent
  have hleft :
      RawEquivalent
        (SignedCount.toRaw (SignedCount.negate (SignedCount.addCount a b)))
        (RawCount.negate (RawCount.add (SignedCount.toRaw a) (SignedCount.toRaw b))) := by
    exact rawEquivalent_negate (addCount_sound a b)
  have hright :
      RawEquivalent
        (SignedCount.toRaw (SignedCount.addCount (SignedCount.negate a) (SignedCount.negate b)))
        (RawCount.add
          (SignedCount.toRaw (SignedCount.negate a))
          (SignedCount.toRaw (SignedCount.negate b))) := by
    exact addCount_sound (SignedCount.negate a) (SignedCount.negate b)
  have hmid :
      RawEquivalent
        (RawCount.negate (RawCount.add (SignedCount.toRaw a) (SignedCount.toRaw b)))
        (RawCount.add
          (SignedCount.toRaw (SignedCount.negate a))
          (SignedCount.toRaw (SignedCount.negate b))) := by
    exact rawEquivalent_of_eq (by
      apply RawCount.ext <;> rfl)
  exact rawEquivalent_trans hleft (rawEquivalent_trans hmid (rawEquivalent_symm hright))

private theorem signedCount_three_add
    (a0 a1 a2 b0 b1 b2 : SignedCount) :
    SignedCount.addCount
        (SignedCount.addCount (SignedCount.addCount a0 b0) (SignedCount.addCount a1 b1))
        (SignedCount.addCount a2 b2) =
      SignedCount.addCount
        (SignedCount.addCount (SignedCount.addCount a0 a1) a2)
        (SignedCount.addCount (SignedCount.addCount b0 b1) b2) := by
  apply signedCount_eq_of_rawEquivalent
  have hleft :
      RawEquivalent
        (SignedCount.toRaw
          (SignedCount.addCount
            (SignedCount.addCount (SignedCount.addCount a0 b0) (SignedCount.addCount a1 b1))
            (SignedCount.addCount a2 b2)))
        (RawCount.add
          (RawCount.add
            (RawCount.add (SignedCount.toRaw a0) (SignedCount.toRaw b0))
            (RawCount.add (SignedCount.toRaw a1) (SignedCount.toRaw b1)))
          (RawCount.add (SignedCount.toRaw a2) (SignedCount.toRaw b2))) := by
    exact rawEquivalent_trans
      (addCount_sound
        (SignedCount.addCount (SignedCount.addCount a0 b0) (SignedCount.addCount a1 b1))
        (SignedCount.addCount a2 b2))
      (rawEquivalent_add
        (rawEquivalent_trans
          (addCount_sound (SignedCount.addCount a0 b0) (SignedCount.addCount a1 b1))
          (rawEquivalent_add (addCount_sound a0 b0) (addCount_sound a1 b1)))
        (addCount_sound a2 b2))
  have hright :
      RawEquivalent
        (SignedCount.toRaw
          (SignedCount.addCount
            (SignedCount.addCount (SignedCount.addCount a0 a1) a2)
            (SignedCount.addCount (SignedCount.addCount b0 b1) b2)))
        (RawCount.add
          (RawCount.add
            (RawCount.add (SignedCount.toRaw a0) (SignedCount.toRaw a1))
            (SignedCount.toRaw a2))
          (RawCount.add
            (RawCount.add (SignedCount.toRaw b0) (SignedCount.toRaw b1))
            (SignedCount.toRaw b2))) := by
    exact rawEquivalent_trans
      (addCount_sound
        (SignedCount.addCount (SignedCount.addCount a0 a1) a2)
        (SignedCount.addCount (SignedCount.addCount b0 b1) b2))
      (rawEquivalent_add
        (rawEquivalent_trans
          (addCount_sound (SignedCount.addCount a0 a1) a2)
          (rawEquivalent_add (addCount_sound a0 a1) (rawEquivalent_refl (SignedCount.toRaw a2))))
        (rawEquivalent_trans
          (addCount_sound (SignedCount.addCount b0 b1) b2)
          (rawEquivalent_add (addCount_sound b0 b1) (rawEquivalent_refl (SignedCount.toRaw b2)))))
  have hmid :
      RawEquivalent
        (RawCount.add
          (RawCount.add
            (RawCount.add (SignedCount.toRaw a0) (SignedCount.toRaw b0))
            (RawCount.add (SignedCount.toRaw a1) (SignedCount.toRaw b1)))
          (RawCount.add (SignedCount.toRaw a2) (SignedCount.toRaw b2)))
        (RawCount.add
          (RawCount.add
            (RawCount.add (SignedCount.toRaw a0) (SignedCount.toRaw a1))
            (SignedCount.toRaw a2))
          (RawCount.add
            (RawCount.add (SignedCount.toRaw b0) (SignedCount.toRaw b1))
            (SignedCount.toRaw b2))) := by
    exact rawEquivalent_of_eq (by
      apply RawCount.ext <;> dsimp [RawCount.add, SignedCount.toRaw] <;> ac_rfl)
  exact rawEquivalent_trans hleft (rawEquivalent_trans hmid (rawEquivalent_symm hright))

/-- Three-coordinate carrier for the balanced hidden sector. The fourth
coordinate is forced by balance, so a balanced state is determined by these
three signed counts. -/
structure BalancedCoordinates where
  c0 : SignedCount
  c1 : SignedCount
  c2 : SignedCount

namespace BalancedCoordinates

/-- Extensionality for reduced balanced coordinates. -/
theorem ext {x y : BalancedCoordinates}
    (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1) (h2 : x.c2 = y.c2) : x = y := by
  cases x
  cases y
  cases h0
  cases h1
  cases h2
  rfl

/-- Read the Part I six-slot reduced-coordinate package as the current-side
balanced hidden coordinates. -/
def ofLocalSlotCoordinates
    (coords : LocalSlotCoordinates) :
    BalancedCoordinates :=
  ⟨coords.c0, coords.c1, coords.c2⟩

/-- The forced fourth coordinate of a balanced three-coordinate state. -/
def forcedFourth (x : BalancedCoordinates) : SignedCount :=
  SignedCount.negate (SignedCount.addCount (SignedCount.addCount x.c0 x.c1) x.c2)

/-- Read the first three coordinates of an arbitrary state. -/
def projectState (x : State) : BalancedCoordinates :=
  ⟨x.c0, x.c1, x.c2⟩

/-- Coordinatewise addition on the reduced balanced carrier. -/
def add (x y : BalancedCoordinates) : BalancedCoordinates :=
  ⟨SignedCount.addCount x.c0 y.c0,
    SignedCount.addCount x.c1 y.c1,
    SignedCount.addCount x.c2 y.c2⟩

/-- Zero reduced balanced coordinate. -/
def zero : BalancedCoordinates :=
  ⟨SignedCount.zero, SignedCount.zero, SignedCount.zero⟩

/-- Forget the reduced balanced coordinates back to a four-coordinate state. -/
def toState (x : BalancedCoordinates) : State :=
  ⟨x.c0, x.c1, x.c2, x.forcedFourth⟩

/-- Reduced transport on balanced coordinates induced from an ambient state
endomap by reconstruction and projection. -/
def transport (F : State → State) (x : BalancedCoordinates) : BalancedCoordinates :=
  projectState (F x.toState)

/-- Every reduced balanced coordinate package determines a balanced four-state. -/
def toBalancedState (x : BalancedCoordinates) : BalancedState := by
  refine ⟨x.toState, ?_⟩
  dsimp [stateTotal, toState, forcedFourth]
  rw [← addCount_assoc]
  exact addCount_negate_right (SignedCount.addCount (SignedCount.addCount x.c0 x.c1) x.c2)

/-- Read the first three coordinates of a balanced state. -/
def ofBalancedState (x : BalancedState) : BalancedCoordinates :=
  ⟨x.toState.c0, x.toState.c1, x.toState.c2⟩

/-- The reduced balanced coordinates reconstruct the balanced state exactly. -/
theorem toBalancedState_ofBalancedState (x : BalancedState) :
    toBalancedState (ofBalancedState x) = x := by
  apply BalancedState.ext
  apply State.ext
  · rfl
  · rfl
  · rfl
  · have hsum :
        SignedCount.addCount
            (SignedCount.addCount
              (SignedCount.addCount x.toState.c0 x.toState.c1)
              x.toState.c2)
            x.toState.c3 =
          SignedCount.zero := by
      simpa [stateTotal, addCount_assoc] using x.balanced
    have hforced :
        SignedCount.addCount
            (SignedCount.addCount x.toState.c0 x.toState.c1)
            x.toState.c2 =
          SignedCount.negate x.toState.c3 :=
      eq_negate_of_addCount_eq_zero hsum
    dsimp [toBalancedState, ofBalancedState, toState, forcedFourth]
    rw [hforced, signedCount_negate_negate]

/-- Reading back the first three coordinates after reconstruction does nothing. -/
theorem ofBalancedState_toBalancedState (x : BalancedCoordinates) :
    ofBalancedState (toBalancedState x) = x := by
  cases x
  rfl

/-- Projecting a reconstructed balanced coordinate package recovers the same
reduced coordinates. -/
theorem projectState_toState (x : BalancedCoordinates) :
    projectState x.toState = x := by
  exact ofBalancedState_toBalancedState x

/-- Projecting a state sum to the reduced balanced carrier is coordinatewise
addition of the projections. -/
theorem projectState_add (x y : State) :
    projectState (State.add x y) = add (projectState x) (projectState y) := by
  rfl

/-- Projecting the zero state gives the reduced balanced zero. -/
theorem projectState_zero :
    projectState State.zero = zero := by
  rfl

/-- Reconstructing the reduced balanced zero gives the zero ambient state. -/
theorem toState_zero :
    zero.toState = State.zero := by
  apply State.ext
  · rfl
  · rfl
  · rfl
  · change SignedCount.negate SignedCount.zero = State.zero.c3
    rw [signedCount_negate_zero]
    rfl

/-- Reconstructing the reduced balanced sum agrees with ambient state
addition. -/
theorem toState_add (x y : BalancedCoordinates) :
    (add x y).toState = State.add x.toState y.toState := by
  let sx : SignedCount := SignedCount.addCount (SignedCount.addCount x.c0 x.c1) x.c2
  let sy : SignedCount := SignedCount.addCount (SignedCount.addCount y.c0 y.c1) y.c2
  apply State.ext
  · rfl
  · rfl
  · rfl
  · dsimp [add, toState, forcedFourth, sx, sy, State.add]
    calc
      SignedCount.negate
          (SignedCount.addCount
            (SignedCount.addCount (SignedCount.addCount x.c0 y.c0)
              (SignedCount.addCount x.c1 y.c1))
            (SignedCount.addCount x.c2 y.c2))
          = SignedCount.negate (SignedCount.addCount sx sy) := by
              rw [signedCount_three_add]
      _ = SignedCount.addCount (SignedCount.negate sx) (SignedCount.negate sy) := by
            rw [signedCount_negate_addCount]
      _ =
            SignedCount.addCount
              (SignedCount.negate (SignedCount.addCount (SignedCount.addCount x.c0 x.c1) x.c2))
              (SignedCount.negate (SignedCount.addCount (SignedCount.addCount y.c0 y.c1) y.c2)) := by
                rfl

/-- Reduced transport by an additive ambient operator is additive on the
balanced hidden carrier. -/
theorem transport_add (A : AddMap) (x y : BalancedCoordinates) :
    transport A.toFun (add x y) =
      add (transport A.toFun x) (transport A.toFun y) := by
  unfold transport
  rw [toState_add, A.map_add, projectState_add]

/-- Reduced transport by an additive ambient operator preserves the reduced
balanced zero. -/
theorem transport_zero (A : AddMap) :
    transport A.toFun zero = zero := by
  unfold transport
  rw [toState_zero, A.map_zero, projectState_zero]

end BalancedCoordinates

/-- Raw soundness for one right-associated three-term signed-count sum. -/
private theorem addCount_sound_right_assoc
    (a b c : SignedCount) :
    RawEquivalent
      (SignedCount.toRaw (SignedCount.addCount a (SignedCount.addCount b c)))
      (RawCount.add (SignedCount.toRaw a)
        (RawCount.add (SignedCount.toRaw b) (SignedCount.toRaw c))) := by
  exact rawEquivalent_trans (addCount_sound a (SignedCount.addCount b c))
    (rawEquivalent_add (rawEquivalent_refl (SignedCount.toRaw a)) (addCount_sound b c))

/-- Raw soundness for one left-associated three-term signed-count sum. -/
private theorem addCount_sound_left_assoc
    (a b c : SignedCount) :
    RawEquivalent
      (SignedCount.toRaw (SignedCount.addCount (SignedCount.addCount a b) c))
      (RawCount.add
        (RawCount.add (SignedCount.toRaw a) (SignedCount.toRaw b))
        (SignedCount.toRaw c)) := by
  exact rawEquivalent_trans (addCount_sound (SignedCount.addCount a b) c)
    (rawEquivalent_add (addCount_sound a b) (rawEquivalent_refl (SignedCount.toRaw c)))

private theorem sixPairFluxTotal_zero
    (a01 a02 a03 a12 a13 a23 : SignedCount) :
    SignedCount.addCount
      (SignedCount.addCount
        (SignedCount.addCount a01 (SignedCount.addCount a02 a03))
        (SignedCount.addCount (SignedCount.negate a01) (SignedCount.addCount a12 a13)))
      (SignedCount.addCount
        (SignedCount.addCount
          (SignedCount.addCount (SignedCount.negate a02) (SignedCount.negate a12))
          a23)
        (SignedCount.addCount
          (SignedCount.addCount (SignedCount.negate a03) (SignedCount.negate a13))
          (SignedCount.negate a23))) =
      SignedCount.zero := by
  let left₁ := SignedCount.addCount a01 (SignedCount.addCount a02 a03)
  let left₂ := SignedCount.addCount (SignedCount.negate a01) (SignedCount.addCount a12 a13)
  let right₁ := SignedCount.addCount
    (SignedCount.addCount (SignedCount.negate a02) (SignedCount.negate a12)) a23
  let right₂ := SignedCount.addCount
    (SignedCount.addCount (SignedCount.negate a03) (SignedCount.negate a13))
    (SignedCount.negate a23)
  apply signedCount_eq_of_rawEquivalent
  have hleft₁ :
      RawEquivalent
        (SignedCount.toRaw left₁)
        (RawCount.add
          (SignedCount.toRaw a01)
          (RawCount.add (SignedCount.toRaw a02) (SignedCount.toRaw a03))) := by
    dsimp [left₁]
    exact addCount_sound_right_assoc a01 a02 a03
  have hleft₂ :
      RawEquivalent
        (SignedCount.toRaw left₂)
        (RawCount.add
          (SignedCount.toRaw (SignedCount.negate a01))
          (RawCount.add (SignedCount.toRaw a12) (SignedCount.toRaw a13))) := by
    dsimp [left₂]
    exact addCount_sound_right_assoc (SignedCount.negate a01) a12 a13
  have hright₁ :
      RawEquivalent
        (SignedCount.toRaw right₁)
        (RawCount.add
          (RawCount.add
            (SignedCount.toRaw (SignedCount.negate a02))
            (SignedCount.toRaw (SignedCount.negate a12)))
          (SignedCount.toRaw a23)) := by
    dsimp [right₁]
    exact addCount_sound_left_assoc (SignedCount.negate a02) (SignedCount.negate a12) a23
  have hright₂ :
      RawEquivalent
        (SignedCount.toRaw right₂)
        (RawCount.add
          (RawCount.add
            (SignedCount.toRaw (SignedCount.negate a03))
            (SignedCount.toRaw (SignedCount.negate a13)))
          (SignedCount.toRaw (SignedCount.negate a23))) := by
    dsimp [right₂]
    exact addCount_sound_left_assoc
      (SignedCount.negate a03) (SignedCount.negate a13) (SignedCount.negate a23)
  have hleft :
      RawEquivalent
        (SignedCount.toRaw (SignedCount.addCount left₁ left₂))
        (RawCount.add
          (RawCount.add
            (SignedCount.toRaw a01)
            (RawCount.add (SignedCount.toRaw a02) (SignedCount.toRaw a03)))
          (RawCount.add
            (SignedCount.toRaw (SignedCount.negate a01))
            (RawCount.add (SignedCount.toRaw a12) (SignedCount.toRaw a13)))) := by
    exact rawEquivalent_trans (addCount_sound left₁ left₂)
      (rawEquivalent_add hleft₁ hleft₂)
  have hright :
      RawEquivalent
        (SignedCount.toRaw (SignedCount.addCount right₁ right₂))
        (RawCount.add
          (RawCount.add
            (RawCount.add
              (SignedCount.toRaw (SignedCount.negate a02))
              (SignedCount.toRaw (SignedCount.negate a12)))
            (SignedCount.toRaw a23))
          (RawCount.add
            (RawCount.add
              (SignedCount.toRaw (SignedCount.negate a03))
              (SignedCount.toRaw (SignedCount.negate a13)))
            (SignedCount.toRaw (SignedCount.negate a23)))) := by
    exact rawEquivalent_trans (addCount_sound right₁ right₂)
      (rawEquivalent_add hright₁ hright₂)
  have htotal :
      RawEquivalent
        (SignedCount.toRaw
          (SignedCount.addCount (SignedCount.addCount left₁ left₂)
            (SignedCount.addCount right₁ right₂)))
        (RawCount.add
          (RawCount.add
            (RawCount.add
              (SignedCount.toRaw a01)
              (RawCount.add (SignedCount.toRaw a02) (SignedCount.toRaw a03)))
            (RawCount.add
              (SignedCount.toRaw (SignedCount.negate a01))
              (RawCount.add (SignedCount.toRaw a12) (SignedCount.toRaw a13))))
          (RawCount.add
            (RawCount.add
              (RawCount.add
                (SignedCount.toRaw (SignedCount.negate a02))
                (SignedCount.toRaw (SignedCount.negate a12)))
              (SignedCount.toRaw a23))
            (RawCount.add
              (RawCount.add
                (SignedCount.toRaw (SignedCount.negate a03))
                (SignedCount.toRaw (SignedCount.negate a13)))
              (SignedCount.toRaw (SignedCount.negate a23))))) := by
    exact rawEquivalent_trans
      (addCount_sound (SignedCount.addCount left₁ left₂) (SignedCount.addCount right₁ right₂))
      (rawEquivalent_add hleft hright)
  have hzero :
      RawEquivalent
        (RawCount.add
          (RawCount.add
            (RawCount.add
              (SignedCount.toRaw a01)
              (RawCount.add (SignedCount.toRaw a02) (SignedCount.toRaw a03)))
            (RawCount.add
              (SignedCount.toRaw (SignedCount.negate a01))
              (RawCount.add (SignedCount.toRaw a12) (SignedCount.toRaw a13))))
          (RawCount.add
            (RawCount.add
              (RawCount.add
                (SignedCount.toRaw (SignedCount.negate a02))
                (SignedCount.toRaw (SignedCount.negate a12)))
              (SignedCount.toRaw a23))
            (RawCount.add
              (RawCount.add
                (SignedCount.toRaw (SignedCount.negate a03))
                (SignedCount.toRaw (SignedCount.negate a13)))
              (SignedCount.toRaw (SignedCount.negate a23)))))
        (SignedCount.toRaw SignedCount.zero) := by
    unfold RawEquivalent
    dsimp [RawCount.add, RawCount.zero, SignedCount.toRaw, SignedCount.negate, SignedCount.zero]
    ac_rfl
  simpa [left₁, left₂, right₁, right₂] using rawEquivalent_trans htotal hzero

/-- The explicit pair-current assembly is automatically balanced. Pairwise
oriented exchanges cancel in the total signed sum across the four framed legs,
so the hidden state already lands in a zero-sum visible sector. -/
theorem assembledState_total_zero
    {carrier : PairExchangeCarrier}
    {Leg : Type}
    (readout : SignedExchangeReadout carrier)
    (frame : FourLegFrame Leg)
    (current : PairExchangeCurrent carrier Leg) :
    stateTotal (assembledState readout frame current) = SignedCount.zero := by
  have h10 :
      readout.toSignedCount (current.value frame.l1 frame.l0) =
        SignedCount.negate (readout.toSignedCount (current.value frame.l0 frame.l1)) := by
    rw [current.swap_reverse frame.l0 frame.l1, readout.map_reverse]
  have h20 :
      readout.toSignedCount (current.value frame.l2 frame.l0) =
        SignedCount.negate (readout.toSignedCount (current.value frame.l0 frame.l2)) := by
    rw [current.swap_reverse frame.l0 frame.l2, readout.map_reverse]
  have h30 :
      readout.toSignedCount (current.value frame.l3 frame.l0) =
        SignedCount.negate (readout.toSignedCount (current.value frame.l0 frame.l3)) := by
    rw [current.swap_reverse frame.l0 frame.l3, readout.map_reverse]
  have h21 :
      readout.toSignedCount (current.value frame.l2 frame.l1) =
        SignedCount.negate (readout.toSignedCount (current.value frame.l1 frame.l2)) := by
    rw [current.swap_reverse frame.l1 frame.l2, readout.map_reverse]
  have h31 :
      readout.toSignedCount (current.value frame.l3 frame.l1) =
        SignedCount.negate (readout.toSignedCount (current.value frame.l1 frame.l3)) := by
    rw [current.swap_reverse frame.l1 frame.l3, readout.map_reverse]
  have h32 :
      readout.toSignedCount (current.value frame.l3 frame.l2) =
        SignedCount.negate (readout.toSignedCount (current.value frame.l2 frame.l3)) := by
    rw [current.swap_reverse frame.l2 frame.l3, readout.map_reverse]
  let a01 := readout.toSignedCount (current.value frame.l0 frame.l1)
  let a02 := readout.toSignedCount (current.value frame.l0 frame.l2)
  let a03 := readout.toSignedCount (current.value frame.l0 frame.l3)
  let a12 := readout.toSignedCount (current.value frame.l1 frame.l2)
  let a13 := readout.toSignedCount (current.value frame.l1 frame.l3)
  let a23 := readout.toSignedCount (current.value frame.l2 frame.l3)
  have hsum := sixPairFluxTotal_zero a01 a02 a03 a12 a13 a23
  simpa [a01, a02, a03, a12, a13, a23,
    stateTotal, assembledState, legFlux,
    current.diagonal_zero frame.l0,
    current.diagonal_zero frame.l1,
    current.diagonal_zero frame.l2,
    current.diagonal_zero frame.l3,
    readout.map_zero,
    h10, h20, h30, h21, h31, h32,
    SignedCount.zero_addCount,
    SignedCount.addCount_zero]
    using hsum

/-- The explicit assembled current state already factors through the balanced
state sector. -/
def assembledBalancedState
    {carrier : PairExchangeCarrier}
    {Leg : Type}
    (readout : SignedExchangeReadout carrier)
    (frame : FourLegFrame Leg)
    (current : PairExchangeCurrent carrier Leg) :
    BalancedState :=
  ⟨assembledState readout frame current,
    assembledState_total_zero readout frame current⟩

/-- The hidden current realization is now explicit: one signed readout on
carrier values and one four-leg frame determine the selected-cut state of the
pair current. The only remaining nontrivial clause is the exactifier/generator
intertwining law on that explicit state assembly. -/
structure CurrentStateAssembly
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentObject Index Time Carrier Law) where
  readout : SignedExchangeReadout data.currentCarrier
  frame : FourLegFrame data.Leg
  exactifier_realized :
    ∀ current : PairExchangeCurrent data.currentCarrier data.Leg,
      assembledState readout frame (data.exactifier.exactify current) =
        data.bridge.generator.toFun (assembledState readout frame current)

/-- The explicit current-state assembly determines the hidden selected-cut
state realization. -/
def CurrentStateAssembly.realize
    {Index Time Carrier Law : Type}
    {data : AnchoredCurrentObject Index Time Carrier Law}
    (assembly : CurrentStateAssembly data) :
    PairExchangeCurrent data.currentCarrier data.Leg → State :=
  assembledState assembly.readout assembly.frame

/-- The explicit current realization already factors through the balanced
zero-sum sector of `State`. -/
def CurrentStateAssembly.realizeBalanced
    {Index Time Carrier Law : Type}
    {data : AnchoredCurrentObject Index Time Carrier Law}
    (assembly : CurrentStateAssembly data) :
    PairExchangeCurrent data.currentCarrier data.Leg → BalancedState :=
  assembledBalancedState assembly.readout assembly.frame

/-- Three-coordinate realization of the balanced hidden current sector. -/
def CurrentStateAssembly.realizeCoordinates
    {Index Time Carrier Law : Type}
    {data : AnchoredCurrentObject Index Time Carrier Law}
    (assembly : CurrentStateAssembly data) :
    PairExchangeCurrent data.currentCarrier data.Leg → BalancedCoordinates :=
  fun current => BalancedCoordinates.ofBalancedState (assembly.realizeBalanced current)

/-- The reduced hidden current coordinates are exactly the first three leg-flux
coordinates of the explicit assembled state. -/
theorem CurrentStateAssembly.coordinateFormula
    {Index Time Carrier Law : Type}
    {data : AnchoredCurrentObject Index Time Carrier Law}
    (assembly : CurrentStateAssembly data) :
    ∀ current : PairExchangeCurrent data.currentCarrier data.Leg,
      assembly.realizeCoordinates current =
        ⟨legFlux assembly.readout assembly.frame current assembly.frame.l0,
          legFlux assembly.readout assembly.frame current assembly.frame.l1,
          legFlux assembly.readout assembly.frame current assembly.frame.l2⟩ := by
  intro current
  rfl

/-- Surface theorem for the explicit current-state assembly. The hidden current
state is no longer arbitrary; it is exactly the legwise signed flux assembled
from the pair current. -/
theorem CurrentStateAssembly.surface
    {Index Time Carrier Law : Type}
    {data : AnchoredCurrentObject Index Time Carrier Law}
    (assembly : CurrentStateAssembly data) :
    (∀ current : PairExchangeCurrent data.currentCarrier data.Leg,
      assembly.realize current =
        assembledState assembly.readout assembly.frame current) ∧
      (∀ current : PairExchangeCurrent data.currentCarrier data.Leg,
        assembly.realize (data.exactifier.exactify current) =
          data.bridge.generator.toFun (assembly.realize current)) := by
  exact
    ⟨by
        intro current
        rfl,
      by
        intro current
        exact assembly.exactifier_realized current⟩

/-- Every realized current state in the explicit assembly is balanced. -/
theorem CurrentStateAssembly.realize_balanced
    {Index Time Carrier Law : Type}
    {data : AnchoredCurrentObject Index Time Carrier Law}
    (assembly : CurrentStateAssembly data) :
    ∀ current : PairExchangeCurrent data.currentCarrier data.Leg,
      stateTotal (assembly.realize current) = SignedCount.zero := by
  intro current
  exact assembledState_total_zero assembly.readout assembly.frame current

/-- The explicit hidden current therefore factors through `BalancedState`,
while still intertwining the local exactifier with the matched selected
generator after forgetting back to `State`. -/
theorem CurrentStateAssembly.balancedSurface
    {Index Time Carrier Law : Type}
    {data : AnchoredCurrentObject Index Time Carrier Law}
    (assembly : CurrentStateAssembly data) :
    (∀ current : PairExchangeCurrent data.currentCarrier data.Leg,
      (assembly.realizeBalanced current).toState = assembly.realize current) ∧
      (∀ current : PairExchangeCurrent data.currentCarrier data.Leg,
        (assembly.realizeBalanced (data.exactifier.exactify current)).toState =
          data.bridge.generator.toFun
            ((assembly.realizeBalanced current).toState)) := by
  exact
    ⟨by
        intro current
        rfl,
      by
        intro current
        exact assembly.exactifier_realized current⟩

/-- The matched selected generator preserves the balanced hidden sector on all
realized current states coming from the explicit current assembly. -/
theorem CurrentStateAssembly.generator_preserves_balance
    {Index Time Carrier Law : Type}
    {data : AnchoredCurrentObject Index Time Carrier Law}
    (assembly : CurrentStateAssembly data) :
    ∀ current : PairExchangeCurrent data.currentCarrier data.Leg,
      stateTotal
          (data.bridge.generator.toFun
            ((assembly.realizeBalanced current).toState)) =
        SignedCount.zero := by
  intro current
  rw [← (assembly.balancedSurface).2 current]
  exact (assembly.realizeBalanced (data.exactifier.exactify current)).balanced

/-- The explicit hidden current therefore also factors through an explicit
three-coordinate reduced carrier for the balanced sector. -/
theorem CurrentStateAssembly.coordinateSurface
    {Index Time Carrier Law : Type}
    {data : AnchoredCurrentObject Index Time Carrier Law}
    (assembly : CurrentStateAssembly data) :
    (∀ current : PairExchangeCurrent data.currentCarrier data.Leg,
      BalancedCoordinates.toBalancedState (assembly.realizeCoordinates current) =
        assembly.realizeBalanced current) ∧
      (∀ current : PairExchangeCurrent data.currentCarrier data.Leg,
        (BalancedCoordinates.toBalancedState
            (assembly.realizeCoordinates (data.exactifier.exactify current))).toState =
          data.bridge.generator.toFun
            ((BalancedCoordinates.toBalancedState
                (assembly.realizeCoordinates current)).toState)) := by
  exact
    ⟨by
        intro current
        exact BalancedCoordinates.toBalancedState_ofBalancedState
          (assembly.realizeBalanced current),
      by
        intro current
        calc
          (BalancedCoordinates.toBalancedState
              (assembly.realizeCoordinates (data.exactifier.exactify current))).toState =
              (assembly.realizeBalanced (data.exactifier.exactify current)).toState := by
                change
                  (BalancedCoordinates.toBalancedState
                      (BalancedCoordinates.ofBalancedState
                        (assembly.realizeBalanced (data.exactifier.exactify current)))).toState =
                    (assembly.realizeBalanced (data.exactifier.exactify current)).toState
                rw [BalancedCoordinates.toBalancedState_ofBalancedState]
          _ =
              data.bridge.generator.toFun
                ((assembly.realizeBalanced current).toState) := by
                  exact (assembly.balancedSurface).2 current
          _ =
              data.bridge.generator.toFun
                ((BalancedCoordinates.toBalancedState
                    (assembly.realizeCoordinates current)).toState) := by
                  change
                    data.bridge.generator.toFun ((assembly.realizeBalanced current).toState) =
                      data.bridge.generator.toFun
                        ((BalancedCoordinates.toBalancedState
                            (BalancedCoordinates.ofBalancedState
                              (assembly.realizeBalanced current))).toState)
                  rw [BalancedCoordinates.toBalancedState_ofBalancedState]⟩

/-- The explicit hidden current law descends to a reduced three-coordinate
transport law by projecting the ambient matched generator. -/
theorem CurrentStateAssembly.coordinateTransport
    {Index Time Carrier Law : Type}
    {data : AnchoredCurrentObject Index Time Carrier Law}
    (assembly : CurrentStateAssembly data) :
    ∀ current : PairExchangeCurrent data.currentCarrier data.Leg,
      assembly.realizeCoordinates (data.exactifier.exactify current) =
        BalancedCoordinates.transport data.bridge.generator.toFun
          (assembly.realizeCoordinates current) := by
  intro current
  have hcoord := (assembly.coordinateSurface).2 current
  apply BalancedCoordinates.ext
  · change
      ((BalancedCoordinates.toBalancedState
          (assembly.realizeCoordinates (data.exactifier.exactify current))).toState).c0 =
        (data.bridge.generator.toFun
          ((BalancedCoordinates.toBalancedState
              (assembly.realizeCoordinates current)).toState)).c0
    exact congrArg State.c0 hcoord
  · change
      ((BalancedCoordinates.toBalancedState
          (assembly.realizeCoordinates (data.exactifier.exactify current))).toState).c1 =
        (data.bridge.generator.toFun
          ((BalancedCoordinates.toBalancedState
              (assembly.realizeCoordinates current)).toState)).c1
    exact congrArg State.c1 hcoord
  · change
      ((BalancedCoordinates.toBalancedState
          (assembly.realizeCoordinates (data.exactifier.exactify current))).toState).c2 =
        (data.bridge.generator.toFun
          ((BalancedCoordinates.toBalancedState
              (assembly.realizeCoordinates current)).toState)).c2
    exact congrArg State.c2 hcoord

/-- Concrete reduced hidden coordinates read directly from a signed readout and
four-leg frame. -/
def assembledCoordinates
    {carrier : PairExchangeCarrier}
    {Leg : Type}
    (readout : SignedExchangeReadout carrier)
    (frame : FourLegFrame Leg)
    (current : PairExchangeCurrent carrier Leg) :
    BalancedCoordinates :=
  ⟨legFlux readout frame current frame.l0,
    legFlux readout frame current frame.l1,
    legFlux readout frame current frame.l2⟩

/-- The reduced hidden coordinates are exactly the canonical six-slot pair
readout assembled onto the first three framed legs. -/
theorem assembledCoordinates_localSlotFormula
    {carrier : PairExchangeCarrier}
    {Leg : Type}
    (readout : SignedExchangeReadout carrier)
    (frame : FourLegFrame Leg)
    (current : PairExchangeCurrent carrier Leg) :
    let slots := localSlotReadout readout frame current
    assembledCoordinates readout frame current =
      ⟨SignedCount.addCount
          (slots LocalSlot.s12)
          (SignedCount.addCount
            (slots LocalSlot.s13)
            (slots LocalSlot.s14)),
        SignedCount.addCount
          (SignedCount.negate (slots LocalSlot.s12))
          (SignedCount.addCount
            (slots LocalSlot.s23)
            (slots LocalSlot.s24)),
        SignedCount.addCount
          (SignedCount.addCount
            (SignedCount.negate (slots LocalSlot.s13))
            (SignedCount.negate (slots LocalSlot.s23)))
          (slots LocalSlot.s34)⟩ := by
  dsimp [assembledCoordinates, legFlux, localSlotReadout]
  rw [current.diagonal_zero frame.l0, readout.map_zero, SignedCount.zero_addCount]
  rw [current.swap_reverse frame.l0 frame.l1, readout.map_reverse]
  rw [current.diagonal_zero frame.l1, readout.map_zero, SignedCount.addCount_zero]
  rw [current.swap_reverse frame.l0 frame.l2, readout.map_reverse]
  rw [current.swap_reverse frame.l1 frame.l2, readout.map_reverse]
  rw [current.diagonal_zero frame.l2, readout.map_zero, SignedCount.zero_addCount]

/-- The reduced hidden coordinates depend only on the six local slot values.
Once two framed current realizations agree slot-by-slot, their assembled
three-coordinate hidden states agree as well. -/
theorem assembledCoordinates_eq_of_localSlotReadout_eq
    {carrier : PairExchangeCarrier}
    {carrier' : PairExchangeCarrier}
    {Leg : Type}
    {Leg' : Type}
    {readout : SignedExchangeReadout carrier}
    {readout' : SignedExchangeReadout carrier'}
    {frame : FourLegFrame Leg}
    {frame' : FourLegFrame Leg'}
    {current : PairExchangeCurrent carrier Leg}
    {current' : PairExchangeCurrent carrier' Leg'}
    (hslots :
      ∀ slot : LocalSlot,
        localSlotReadout readout frame current slot =
          localSlotReadout readout' frame' current' slot) :
    assembledCoordinates readout frame current =
      assembledCoordinates readout' frame' current' := by
  have hleft := assembledCoordinates_localSlotFormula readout frame current
  have hright := assembledCoordinates_localSlotFormula readout' frame' current'
  rw [hleft, hright]
  change
    BalancedCoordinates.ofLocalSlotCoordinates
        (localSlotCoordinates (localSlotReadout readout frame current)) =
      BalancedCoordinates.ofLocalSlotCoordinates
        (localSlotCoordinates (localSlotReadout readout' frame' current'))
  have hcoords :
      localSlotCoordinates (localSlotReadout readout frame current) =
        localSlotCoordinates (localSlotReadout readout' frame' current') :=
    localSlotCoordinates_eq_of_eq hslots
  exact congrArg BalancedCoordinates.ofLocalSlotCoordinates hcoords

/-- Minimal explicit coordinate assembly for the detached hidden current:
only the signed readout, the genuine four-leg frame, and the reduced
three-coordinate transport law are retained. This is the smallest explicit
object that still determines `ρ_3` concretely. -/
structure CurrentCoordinateAssembly
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentObject Index Time Carrier Law) where
  readout : SignedExchangeReadout data.currentCarrier
  frame : FourLegFrame data.Leg
  coordinateTransport :
    ∀ current : PairExchangeCurrent data.currentCarrier data.Leg,
      assembledCoordinates readout frame (data.exactifier.exactify current) =
        BalancedCoordinates.transport data.bridge.generator.toFun
          (assembledCoordinates readout frame current)

/-- Concrete reduced hidden coordinates determined directly by the signed
readout and four-leg frame. -/
def CurrentCoordinateAssembly.currentCoordinates
    {Index Time Carrier Law : Type}
    {data : AnchoredCurrentObject Index Time Carrier Law}
    (assembly : CurrentCoordinateAssembly data) :
    PairExchangeCurrent data.currentCarrier data.Leg → BalancedCoordinates :=
  assembledCoordinates assembly.readout assembly.frame

/-- The coordinate assembly reads exactly the first three leg-flux coordinates
of the framed pair current. -/
theorem CurrentCoordinateAssembly.coordinateFormula
    {Index Time Carrier Law : Type}
    {data : AnchoredCurrentObject Index Time Carrier Law}
    (assembly : CurrentCoordinateAssembly data) :
    ∀ current : PairExchangeCurrent data.currentCarrier data.Leg,
      assembly.currentCoordinates current =
        ⟨legFlux assembly.readout assembly.frame current assembly.frame.l0,
          legFlux assembly.readout assembly.frame current assembly.frame.l1,
          legFlux assembly.readout assembly.frame current assembly.frame.l2⟩ := by
  intro current
  rfl

/-- Every explicit four-state current assembly determines the smaller explicit
coordinate assembly. -/
def CurrentStateAssembly.toCurrentCoordinateAssembly
    {Index Time Carrier Law : Type}
    {data : AnchoredCurrentObject Index Time Carrier Law}
    (assembly : CurrentStateAssembly data) :
    CurrentCoordinateAssembly data where
  readout := assembly.readout
  frame := assembly.frame
  coordinateTransport := by
    intro current
    exact assembly.coordinateTransport current

/-- Minimal detached hidden-state assembly: only the reduced hidden current
coordinates and their exact transport law are retained. All downstream
trajectory statements now depend only on this smaller package, not on the full
readout/frame realization. -/
structure ReducedCurrentAssembly
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentObject Index Time Carrier Law) where
  currentCoordinates :
    PairExchangeCurrent data.currentCarrier data.Leg → BalancedCoordinates
  coordinateTransport :
    ∀ current : PairExchangeCurrent data.currentCarrier data.Leg,
      currentCoordinates (data.exactifier.exactify current) =
        BalancedCoordinates.transport data.bridge.generator.toFun
          (currentCoordinates current)

/-- Every explicit detached current-state assembly determines the smaller
reduced hidden-state assembly. -/
def CurrentStateAssembly.toReducedCurrentAssembly
    {Index Time Carrier Law : Type}
    {data : AnchoredCurrentObject Index Time Carrier Law}
    (assembly : CurrentStateAssembly data) :
    ReducedCurrentAssembly data where
  currentCoordinates := assembly.realizeCoordinates
  coordinateTransport := assembly.coordinateTransport

/-- Every explicit coordinate assembly determines the smaller reduced
hidden-state assembly. -/
def CurrentCoordinateAssembly.toReducedCurrentAssembly
    {Index Time Carrier Law : Type}
    {data : AnchoredCurrentObject Index Time Carrier Law}
    (assembly : CurrentCoordinateAssembly data) :
    ReducedCurrentAssembly data where
  currentCoordinates := assembly.currentCoordinates
  coordinateTransport := assembly.coordinateTransport

/-- Detached anchored current object retaining only the reduced hidden-state
assembly needed for the reduced dynamics. -/
structure ReducedAnchoredCurrentObject (Index Time Carrier Law : Type) where
  object : AnchoredCurrentObject Index Time Carrier Law
  reducedAssembly : ReducedCurrentAssembly object

/-- Detached anchored current object retaining only the explicit coordinate
assembly needed to define `ρ_3` concretely. -/
structure CoordinateAnchoredCurrentObject (Index Time Carrier Law : Type) where
  object : AnchoredCurrentObject Index Time Carrier Law
  coordinateAssembly : CurrentCoordinateAssembly object

/-- The explicit coordinate object determines the smaller reduced anchored
current object. -/
def CoordinateAnchoredCurrentObject.toReducedAnchoredCurrentObject
    {Index Time Carrier Law : Type}
    (data : CoordinateAnchoredCurrentObject Index Time Carrier Law) :
    ReducedAnchoredCurrentObject Index Time Carrier Law where
  object := data.object
  reducedAssembly := data.coordinateAssembly.toReducedCurrentAssembly

/-- Unified detached state field with explicit hidden current assembly. Visible
roles are still realized on the selected cut, but the hidden current-state map
is no longer primitive data. -/
structure AssembledUnifiedStateField
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentObject Index Time Carrier Law) where
  currentAssembly : CurrentStateAssembly data
  visibleRealize :
    (role : VisibleCarrierRole) → data.visible role → State
  visibleRealize_injective :
    ∀ role : VisibleCarrierRole,
      ∀ v w : data.visible role,
        visibleRealize role v = visibleRealize role w → v = w
  visibleRealize_visible :
    ∀ role : VisibleCarrierRole,
      ∀ v : data.visible role,
        selectedProjection data.bridge (visibleRealize role v) =
          visibleRealize role v
  read_realized :
    ∀ role : VisibleCarrierRole,
      ∀ current : PairExchangeCurrent data.currentCarrier data.Leg,
        visibleRealize role ((data.quotient role).read current) =
          selectedProjection data.bridge (currentAssembly.realize current)
  evolve_realized :
    ∀ role : VisibleCarrierRole,
      ∀ v : data.visible role,
        visibleRealize role ((data.quotient role).evolve v) =
          data.bridge.generator.toFun (visibleRealize role v)

/-- The explicit assembly package determines the earlier unified state field. -/
def AssembledUnifiedStateField.toUnifiedStateField
    {Index Time Carrier Law : Type}
    {data : AnchoredCurrentObject Index Time Carrier Law}
    (field : AssembledUnifiedStateField data) :
    UnifiedStateField data where
  currentRealize := field.currentAssembly.realize
  exactifier_realized := field.currentAssembly.exactifier_realized
  visibleRealize := field.visibleRealize
  visibleRealize_injective := field.visibleRealize_injective
  visibleRealize_visible := field.visibleRealize_visible
  read_realized := field.read_realized
  evolve_realized := field.evolve_realized

/-- Anchored detached current object equipped with an explicit assembled hidden
state field. This is the first point where the hidden current has a concrete
formula on the selected cut rather than a black-box state map. -/
structure AssembledUnifiedAnchoredCurrentObject (Index Time Carrier Law : Type) where
  object : AnchoredCurrentObject Index Time Carrier Law
  stateField : AssembledUnifiedStateField object

/-- The explicit assembled state-field package determines the earlier unified
anchored detached current object. -/
def AssembledUnifiedAnchoredCurrentObject.toUnifiedAnchoredCurrentObject
    {Index Time Carrier Law : Type}
    (data : AssembledUnifiedAnchoredCurrentObject Index Time Carrier Law) :
    UnifiedAnchoredCurrentObject Index Time Carrier Law where
  object := data.object
  stateField := data.stateField.toUnifiedStateField

/-- Balanced hidden current state on the selected cut, obtained from the
explicit assembled current realization. -/
def AssembledUnifiedAnchoredCurrentObject.currentBalancedState
    {Index Time Carrier Law : Type}
    (data : AssembledUnifiedAnchoredCurrentObject Index Time Carrier Law) :
    PairExchangeCurrent data.object.currentCarrier data.object.Leg →
      BalancedState :=
  data.stateField.currentAssembly.realizeBalanced

/-- Three-coordinate reduced realization of the balanced hidden current
sector on the selected cut. -/
def AssembledUnifiedAnchoredCurrentObject.currentCoordinates
    {Index Time Carrier Law : Type}
    (data : AssembledUnifiedAnchoredCurrentObject Index Time Carrier Law) :
    PairExchangeCurrent data.object.currentCarrier data.object.Leg →
      BalancedCoordinates :=
  data.stateField.currentAssembly.realizeCoordinates

/-- Packaged reduced hidden-state assembly determined by the explicit detached
current realization. -/
def AssembledUnifiedAnchoredCurrentObject.toReducedCurrentAssembly
    {Index Time Carrier Law : Type}
    (data : AssembledUnifiedAnchoredCurrentObject Index Time Carrier Law) :
    ReducedCurrentAssembly data.object :=
  data.stateField.currentAssembly.toReducedCurrentAssembly

/-- The explicit assembled anchored current object determines the smaller
reduced anchored current object. -/
def AssembledUnifiedAnchoredCurrentObject.toReducedAnchoredCurrentObject
    {Index Time Carrier Law : Type}
    (data : AssembledUnifiedAnchoredCurrentObject Index Time Carrier Law) :
    ReducedAnchoredCurrentObject Index Time Carrier Law where
  object := data.object
  reducedAssembly := data.toReducedCurrentAssembly

/-- The packaged reduced hidden current is already given by the concrete
leg-flux coordinate formula on the first three framed legs. -/
theorem AssembledUnifiedAnchoredCurrentObject.currentCoordinateFormula
    {Index Time Carrier Law : Type}
    (data : AssembledUnifiedAnchoredCurrentObject Index Time Carrier Law) :
    ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
      data.currentCoordinates current =
        ⟨legFlux data.stateField.currentAssembly.readout
            data.stateField.currentAssembly.frame
            current
            data.stateField.currentAssembly.frame.l0,
          legFlux data.stateField.currentAssembly.readout
            data.stateField.currentAssembly.frame
            current
            data.stateField.currentAssembly.frame.l1,
          legFlux data.stateField.currentAssembly.readout
            data.stateField.currentAssembly.frame
            current
            data.stateField.currentAssembly.frame.l2⟩ := by
  intro current
  exact data.stateField.currentAssembly.coordinateFormula current

/-- Surface theorem for the explicit assembled unified state field. The same
selected-cut flagship surface now follows with an explicit hidden current-state
formula. -/
theorem AssembledUnifiedAnchoredCurrentObject.surface
    {Index Time Carrier Law : Type}
    (data : AssembledUnifiedAnchoredCurrentObject Index Time Carrier Law) :
    Nonempty (PairExchangeCurrent data.object.currentCarrier data.object.Leg) ∧
      data.object.toCurrentAnchor.currentDirectReturnCompatible ∧
      data.object.toCurrentAnchor.visiblePrimitiveReadoutAutonomous ∧
      data.object.toCurrentAnchor.minimalVisibleQuotients ∧
      exactVisibleOnCut
        (data.object.bridge.selectedBridge.observer.selection.realization.tower.π
          data.object.bridge.selectedBridge.observer.selection.horizon)
        (selected_observed_law
          data.object.bridge.selectedBridge.observer.selection).op ∧
      ForcedContinuumLaw
        data.object.bridge.selectedBridge.observer.continuumClass
        data.object.physicalPrinciple.selectedLaw.selectedClosureLaw ∧
      (∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
        observer.selection = data.object.bridge.selectedBridge.observer.selection →
          data.object.physicalPrinciple.selectedLaw.endpointClosureClass =
            observer.continuumClass) ∧
      (∀ role : VisibleCarrierRole,
        ∀ current :
          PairExchangeCurrent data.object.currentCarrier data.object.Leg,
          (data.object.quotient role).read
              (data.object.exactifier.exactify current) =
            (data.object.quotient role).evolve
              ((data.object.quotient role).read current)) ∧
      (∀ role : VisibleCarrierRole,
        ∀ current :
          PairExchangeCurrent data.object.currentCarrier data.object.Leg,
          data.toUnifiedAnchoredCurrentObject.toAutonomousAnchoredCurrentObject.toAnchoredAutonomyObject.toAnchoredLawForm.channelResidual role current =
            data.toUnifiedAnchoredCurrentObject.toAutonomousAnchoredCurrentObject.toAnchoredAutonomyObject.toAnchoredLawForm.channelRead role
              (data.toUnifiedAnchoredCurrentObject.toAutonomousAnchoredCurrentObject.toAnchoredAutonomyObject.toAnchoredLawForm.returnedDefect current)) ∧
      (∀ role : VisibleCarrierRole,
        ∀ v : data.object.visible role,
          data.object.bridge.generator.toFun
            (data.stateField.visibleRealize role v) =
              data.stateField.visibleRealize role
                ((data.object.quotient role).evolve v)) := by
  simpa
    [AssembledUnifiedAnchoredCurrentObject.toUnifiedAnchoredCurrentObject,
      AssembledUnifiedStateField.toUnifiedStateField,
      CurrentStateAssembly.realize]
    using data.toUnifiedAnchoredCurrentObject.surface

/-- On the explicit assembled anchored object, every hidden current state lies
in the balanced zero-sum sector of `State`. -/
theorem AssembledUnifiedAnchoredCurrentObject.currentBalance
    {Index Time Carrier Law : Type}
    (data : AssembledUnifiedAnchoredCurrentObject Index Time Carrier Law) :
    ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
      stateTotal (data.stateField.currentAssembly.realize current) =
        SignedCount.zero := by
  intro current
  exact data.stateField.currentAssembly.realize_balanced current

/-- On the explicit assembled anchored object, the hidden current really is a
balanced-state-valued field, and the exactifier/generator law still holds after
forgetting back to `State`. -/
theorem AssembledUnifiedAnchoredCurrentObject.currentBalancedSurface
    {Index Time Carrier Law : Type}
    (data : AssembledUnifiedAnchoredCurrentObject Index Time Carrier Law) :
    (∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
      (data.currentBalancedState current).toState =
        data.stateField.currentAssembly.realize current) ∧
      (∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
        (data.currentBalancedState (data.object.exactifier.exactify current)).toState =
          data.object.bridge.generator.toFun
            ((data.currentBalancedState current).toState)) := by
  exact data.stateField.currentAssembly.balancedSurface

/-- The matched selected generator therefore closes on the balanced hidden
sector traced by the explicit current assembly. -/
theorem AssembledUnifiedAnchoredCurrentObject.currentBalancedClosure
    {Index Time Carrier Law : Type}
    (data : AssembledUnifiedAnchoredCurrentObject Index Time Carrier Law) :
    ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
      stateTotal
          (data.object.bridge.generator.toFun
            ((data.currentBalancedState current).toState)) =
        SignedCount.zero := by
  intro current
  exact data.stateField.currentAssembly.generator_preserves_balance current

/-- On the explicit assembled anchored object, the hidden current is also a
three-coordinate reduced carrier whose reconstruction recovers the balanced
hidden current law. -/
theorem AssembledUnifiedAnchoredCurrentObject.currentCoordinateSurface
    {Index Time Carrier Law : Type}
    (data : AssembledUnifiedAnchoredCurrentObject Index Time Carrier Law) :
    (∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
      BalancedCoordinates.toBalancedState (data.currentCoordinates current) =
        data.currentBalancedState current) ∧
      (∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
        (BalancedCoordinates.toBalancedState
            (data.currentCoordinates (data.object.exactifier.exactify current))).toState =
          data.object.bridge.generator.toFun
            ((BalancedCoordinates.toBalancedState
                (data.currentCoordinates current)).toState)) := by
  exact data.stateField.currentAssembly.coordinateSurface

/-- Packaged selected-cut three-coordinate transport law for the reduced hidden
current carrier. -/
theorem AssembledUnifiedAnchoredCurrentObject.currentCoordinateTransport
    {Index Time Carrier Law : Type}
    (data : AssembledUnifiedAnchoredCurrentObject Index Time Carrier Law) :
    ∀ current : PairExchangeCurrent data.object.currentCarrier data.object.Leg,
      data.currentCoordinates (data.object.exactifier.exactify current) =
        BalancedCoordinates.transport data.object.bridge.generator.toFun
          (data.currentCoordinates current) := by
  intro current
  exact data.stateField.currentAssembly.coordinateTransport current

end ClosureCurrent

end CoherenceCalculus
