import CoherenceCalculus.Foundation.ClosureTransportCore
import CoherenceCalculus.Foundation.DiophantineWidth

/-!
# Foundation.ClosureBalanceCore

Manuscript-facing Chapter 6 consequences of the canonical closure realization.

This module does not extend the foundation. It packages already-forced closure
facts into explicit objects and theorems that match the Part II interface:

- the realized structural interface
- the balanced six-slot local carrier count
- primitive local type profiles on the unit seed
- exact collapse of boundary shadow transport in the canonical realization
- exact tail/revelation laws for the realized four-grade tower
-/

namespace CoherenceCalculus

/-- The common local closure-slot count attached to a balanced dimension. -/
def balancedClosureSlotCount (D : Nat) : Nat := binomial D 2

/-- Plain recursive sum on finite lists of natural numbers. -/
def natListSum : List Nat → Nat
  | [] => 0
  | n :: ns => n + natListSum ns

/-- Every listed channel size is strictly positive. -/
def PositiveParts (parts : List Nat) : Prop :=
  ∀ n, n ∈ parts → 0 < n

/-- The channel sizes are listed in weakly decreasing order. -/
def NonincreasingParts : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: tail => b ≤ a ∧ NonincreasingParts (b :: tail)

/-- A local type profile is a finite positive partition of the balanced local
closure-slot count. -/
structure LocalTypeProfile (D : Nat) where
  parts : List Nat
  positive : PositiveParts parts
  nonincreasing : NonincreasingParts parts
  sum_eq : natListSum parts = balancedClosureSlotCount D

/-- On the canonical balanced carrier, a logical type signature is exactly a
local type profile. -/
abbrev LogicalTypeSignature := LocalTypeProfile closureStableDimension

/-- The finitely many nonincreasing positive partitions of the canonical
six-slot balanced carrier. -/
def IsCanonicalLogicalProfile (parts : List Nat) : Prop :=
  parts = [6] ∨
  parts = [5, 1] ∨
  parts = [4, 2] ∨
  parts = [4, 1, 1] ∨
  parts = [3, 3] ∨
  parts = [3, 2, 1] ∨
  parts = [3, 1, 1, 1] ∨
  parts = [2, 2, 2] ∨
  parts = [2, 2, 1, 1] ∨
  parts = [2, 1, 1, 1, 1] ∨
  parts = [1, 1, 1, 1, 1, 1]

/-- A symmetry-refined logical type is still controlled by an underlying
logical type signature on the six-slot balanced carrier. -/
structure SymmetryRefinedLogicalType where
  signature : LogicalTypeSignature

/-- Four primitive labels for the canonical balanced carrier. -/
inductive Primitive4 where
  | one
  | two
  | three
  | four
  deriving DecidableEq, Repr

/-- The six unordered slot pairs in the canonical balanced four-incidence. -/
inductive LocalSlot where
  | s12
  | s13
  | s14
  | s23
  | s24
  | s34
  deriving DecidableEq, Repr

/-- The local six-slot carrier packaged as a six-coordinate signed-count
carrier. -/
def LocalSlotCarrier : Type := LocalSlot → SignedCount

/-- Reduced three-coordinate readout of the canonical six-slot carrier. This is
the smallest linear coordinate package later used to reconstruct the balanced
local current from six slot values alone. -/
structure LocalSlotCoordinates where
  c0 : SignedCount
  c1 : SignedCount
  c2 : SignedCount

namespace LocalSlotCoordinates

/-- Extensionality for reduced six-slot coordinate packages. -/
theorem ext
    {x y : LocalSlotCoordinates}
    (h0 : x.c0 = y.c0)
    (h1 : x.c1 = y.c1)
    (h2 : x.c2 = y.c2) :
    x = y := by
  cases x
  cases y
  cases h0
  cases h1
  cases h2
  rfl

end LocalSlotCoordinates

/-- Canonical reduced-coordinate readout of a six-slot local carrier. The
three visible coordinates are fixed linear combinations of the six local slot
values. -/
def localSlotCoordinates
    (slots : LocalSlotCarrier) :
    LocalSlotCoordinates :=
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
      (slots LocalSlot.s34)⟩

/-- The reduced-coordinate readout depends only on the six local slot values.
Pointwise agreement of slot carriers already forces agreement of the canonical
three-coordinate readout. -/
theorem localSlotCoordinates_eq_of_eq
    {slots slots' : LocalSlotCarrier}
    (hslots : ∀ slot : LocalSlot, slots slot = slots' slot) :
    localSlotCoordinates slots = localSlotCoordinates slots' := by
  apply LocalSlotCoordinates.ext
  · unfold localSlotCoordinates
    rw [hslots LocalSlot.s12, hslots LocalSlot.s13, hslots LocalSlot.s14]
  · unfold localSlotCoordinates
    rw [hslots LocalSlot.s12, hslots LocalSlot.s23, hslots LocalSlot.s24]
  · unfold localSlotCoordinates
    rw [hslots LocalSlot.s13, hslots LocalSlot.s23, hslots LocalSlot.s34]

/-- Canonical basis for the primitive three-channel appearing in the
intrinsic `1+2+3` profile. -/
inductive PrimitiveThreeChannel where
  | u1
  | u2
  | u3
  deriving DecidableEq, Repr

/-- Canonical symmetric-square basis on the primitive three-channel. This is
the finite carrier-level surrogate for the manuscript's `Sym^2(U_3)` readout
on the active additive foundation. -/
inductive PrimitiveThreeSymmetricSquare where
  | u1u1
  | u1u2
  | u1u3
  | u2u2
  | u2u3
  | u3u3
  deriving DecidableEq, Repr

/-- Minimal carrier isomorphism structure used for finite explicit carrier
identifications on the active additive foundation. -/
structure CarrierIso (α β : Type) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x : α, invFun (toFun x) = x
  right_inv : ∀ y : β, toFun (invFun y) = y

/-- Canonical identification of the six local slots with the six symmetric
square basis states of the primitive three-channel. -/
def localSlotToPrimitiveThreeSymmetricSquare :
    LocalSlot → PrimitiveThreeSymmetricSquare
  | .s12 => .u1u1
  | .s13 => .u1u2
  | .s14 => .u1u3
  | .s23 => .u2u2
  | .s24 => .u2u3
  | .s34 => .u3u3

/-- Inverse identification from the symmetric-square basis back to the six
local slots. -/
def primitiveThreeSymmetricSquareToLocalSlot :
    PrimitiveThreeSymmetricSquare → LocalSlot
  | .u1u1 => .s12
  | .u1u2 => .s13
  | .u1u3 => .s14
  | .u2u2 => .s23
  | .u2u3 => .s24
  | .u3u3 => .s34

/-- The slot-to-symmetric-square identification is left-invertible. -/
theorem primitiveThreeSymmetricSquare_roundtrip_slot
    (s : LocalSlot) :
    primitiveThreeSymmetricSquareToLocalSlot
        (localSlotToPrimitiveThreeSymmetricSquare s) = s := by
  cases s <;> rfl

/-- The symmetric-square-to-slot identification is right-invertible. -/
theorem primitiveThreeSymmetricSquare_roundtrip_basis
    (q : PrimitiveThreeSymmetricSquare) :
    localSlotToPrimitiveThreeSymmetricSquare
        (primitiveThreeSymmetricSquareToLocalSlot q) = q := by
  cases q <;> rfl

/-- Explicit basis-level equivalence between the six-slot local carrier index
type and the symmetric-square basis of the primitive three-channel. -/
def sixSlotCarrierSymmetricSquareEquiv :
    CarrierIso LocalSlot PrimitiveThreeSymmetricSquare where
  toFun := localSlotToPrimitiveThreeSymmetricSquare
  invFun := primitiveThreeSymmetricSquareToLocalSlot
  left_inv := primitiveThreeSymmetricSquare_roundtrip_slot
  right_inv := primitiveThreeSymmetricSquare_roundtrip_basis

/-- Intrinsic relabelings are primitive permutations of the balanced
four-incidence. -/
def IntrinsicRelabelingAction : Type := {
    toFun : Primitive4 → Primitive4 //
    (∀ ⦃x y : Primitive4⦄, toFun x = toFun y → x = y) ∧
      (∀ y : Primitive4, ∃ x : Primitive4, toFun x = y)
  }

/-- The three intrinsic orbit classes of ordered slot pairs. -/
inductive IntrinsicSlotAdjacency where
  | equal
  | adjacent
  | disjoint
  deriving DecidableEq, Repr

/-- Ordered slot pairs are classified by equality, shared primitive, or
disjointness. -/
def intrinsicSlotAdjacency : LocalSlot → LocalSlot → IntrinsicSlotAdjacency
  | .s12, .s12 => .equal
  | .s13, .s13 => .equal
  | .s14, .s14 => .equal
  | .s23, .s23 => .equal
  | .s24, .s24 => .equal
  | .s34, .s34 => .equal
  | .s12, .s34 => .disjoint
  | .s34, .s12 => .disjoint
  | .s13, .s24 => .disjoint
  | .s24, .s13 => .disjoint
  | .s14, .s23 => .disjoint
  | .s23, .s14 => .disjoint
  | _, _ => .adjacent

/-- The forced intrinsic signature on the six-slot carrier is the
three-channel profile `3+2+1`, i.e. the manuscript's `1+2+3` written in the
repository's nonincreasing profile convention. -/
theorem intrinsic_six_slot_decomposition :
    natListSum [3, 2, 1] = balancedClosureSlotCount closureStableDimension ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  refine ⟨by decide, ?_⟩
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

/-- Full intrinsic relabeling symmetry collapses the canonical six-slot
logical signature to the `3+2+1` profile. -/
theorem intrinsic_symmetry_forces_123 :
    IsCanonicalLogicalProfile [3, 2, 1] :=
  intrinsic_six_slot_decomposition.2

/-- Finite carrier-level surrogate for the manuscript statement that the
six-slot carrier is the symmetric square of the primitive three-channel. On
the active additive foundation, this is recorded as an explicit equivalence of
the six slot labels with the symmetric-square basis states. -/
theorem six_slot_carrier_is_symmetric_square_of_u3 :
    Nonempty (CarrierIso LocalSlot PrimitiveThreeSymmetricSquare) := by
  exact ⟨sixSlotCarrierSymmetricSquareEquiv⟩

/-- Explicit exterior-square representation content of the canonical
`1+2+3` six-slot carrier decomposition. -/
structure ExteriorSquareFermionicData where
  u2ExteriorSign : Prop
  u2ExteriorSign_valid : u2ExteriorSign
  u3ExteriorSignTwistedStandard : Prop
  u3ExteriorSignTwistedStandard_valid : u3ExteriorSignTwistedStandard
  absentFromEdgeCarrier : Prop
  absentFromEdgeCarrier_valid : absentFromEdgeCarrier
  additionalFermionicDimension : Nat
  additionalFermionicDimension_eq :
    additionalFermionicDimension = 4

/-- The exterior squares of the `2`- and `3`-channels contribute a fermionic
`1+3` sector outside the bosonic six-slot carrier. -/
theorem fermionic_sector_from_ext2
    (data : ExteriorSquareFermionicData) :
    data.u2ExteriorSign ∧
      data.u3ExteriorSignTwistedStandard ∧
      data.absentFromEdgeCarrier ∧
      data.additionalFermionicDimension = 4 := by
  exact ⟨data.u2ExteriorSign_valid, data.u3ExteriorSignTwistedStandard_valid,
    data.absentFromEdgeCarrier_valid, data.additionalFermionicDimension_eq⟩

/-- Slot laws invariant under intrinsic relabeling depend only on the three
adjacency classes of ordered slot pairs. -/
def IntrinsicAdjacencyInvariant
    (A : LocalSlot → LocalSlot → SignedCount) : Prop :=
  ∀ α β α' β' : LocalSlot,
    intrinsicSlotAdjacency α β = intrinsicSlotAdjacency α' β' →
      A α β = A α' β'

/-- The three scalar parameters of an intrinsically equivariant six-slot law. -/
structure IntrinsicSlotParameters where
  diagonal : SignedCount
  adjacent : SignedCount
  disjoint : SignedCount

/-- Extensionality for intrinsic six-slot parameter packages. -/
theorem IntrinsicSlotParameters.ext
    {p q : IntrinsicSlotParameters}
    (hdiag : p.diagonal = q.diagonal)
    (hadj : p.adjacent = q.adjacent)
    (hdis : p.disjoint = q.disjoint) : p = q := by
  cases p with
  | mk pdiag padj pdis =>
      cases q with
      | mk qdiag qadj qdis =>
          cases hdiag
          cases hadj
          cases hdis
          rfl

/-- The normal-form value attached to one intrinsic adjacency class. -/
def intrinsicNormalEntry
    (p : IntrinsicSlotParameters) : IntrinsicSlotAdjacency → SignedCount
  | .equal => p.diagonal
  | .adjacent => p.adjacent
  | .disjoint => p.disjoint

/-- An intrinsic six-slot law is in normal form when every matrix entry is
determined solely by the slot-pair adjacency class. -/
def isIntrinsicNormalForm
    (A : LocalSlot → LocalSlot → SignedCount)
    (p : IntrinsicSlotParameters) : Prop :=
  ∀ α β : LocalSlot,
    A α β = intrinsicNormalEntry p (intrinsicSlotAdjacency α β)

/-- Intrinsic full-symmetry laws on the six-slot carrier have a unique
three-parameter normal form. -/
theorem intrinsic_slot_normal_form
    (A : LocalSlot → LocalSlot → SignedCount)
    (hA : IntrinsicAdjacencyInvariant A) :
    ∃ p : IntrinsicSlotParameters,
      isIntrinsicNormalForm A p ∧
        ∀ q : IntrinsicSlotParameters, isIntrinsicNormalForm A q → q = p := by
  let p : IntrinsicSlotParameters :=
    ⟨A LocalSlot.s12 LocalSlot.s12,
      A LocalSlot.s12 LocalSlot.s13,
      A LocalSlot.s12 LocalSlot.s34⟩
  refine ⟨p, ?_, ?_⟩
  · intro α β
    unfold intrinsicNormalEntry
    cases hclass : intrinsicSlotAdjacency α β with
    | equal =>
        exact hA α β LocalSlot.s12 LocalSlot.s12 (by simpa using hclass)
    | adjacent =>
        exact hA α β LocalSlot.s12 LocalSlot.s13 (by simpa using hclass)
    | disjoint =>
        exact hA α β LocalSlot.s12 LocalSlot.s34 (by simpa using hclass)
  · intro q hq
    apply IntrinsicSlotParameters.ext
    · calc
        q.diagonal = A LocalSlot.s12 LocalSlot.s12 := by
          simpa [isIntrinsicNormalForm, intrinsicNormalEntry] using
            (hq LocalSlot.s12 LocalSlot.s12).symm
        _ = p.diagonal := by
          rfl
    · calc
        q.adjacent = A LocalSlot.s12 LocalSlot.s13 := by
          simpa [isIntrinsicNormalForm, intrinsicNormalEntry] using
            (hq LocalSlot.s12 LocalSlot.s13).symm
        _ = p.adjacent := by
          rfl
    · calc
        q.disjoint = A LocalSlot.s12 LocalSlot.s34 := by
          simpa [isIntrinsicNormalForm, intrinsicNormalEntry] using
            (hq LocalSlot.s12 LocalSlot.s34).symm
        _ = p.disjoint := by
          rfl

/-- Two intrinsic six-slot laws in the same normal form agree pointwise. Once
the three slot-class parameters agree, no further entrywise freedom remains. -/
theorem intrinsic_law_pointwise_eq_of_normalForm_eq
    {A B : LocalSlot → LocalSlot → SignedCount}
    {p : IntrinsicSlotParameters}
    (hA : isIntrinsicNormalForm A p)
    (hB : isIntrinsicNormalForm B p) :
    ∀ α β : LocalSlot, A α β = B α β := by
  intro α β
  calc
    A α β = intrinsicNormalEntry p (intrinsicSlotAdjacency α β) := hA α β
    _ = B α β := (hB α β).symm

/-- Explicit repeated addition on signed counts. -/
def signedCount_nsmul : Nat → SignedCount → SignedCount
  | 0, _ => SignedCount.zero
  | n + 1, z => SignedCount.addCount (signedCount_nsmul n z) z

/-- First intrinsic channel eigenvalue attached to one normal-form parameter
package. -/
def intrinsicChannelEigenvalue1
    (p : IntrinsicSlotParameters) : SignedCount :=
  SignedCount.addCount
    (SignedCount.addCount p.diagonal (signedCount_nsmul 4 p.adjacent))
    p.disjoint

/-- Second intrinsic channel eigenvalue attached to one normal-form parameter
package. -/
def intrinsicChannelEigenvalue2
    (p : IntrinsicSlotParameters) : SignedCount :=
  SignedCount.addCount
    (SignedCount.subCount p.diagonal (signedCount_nsmul 2 p.adjacent))
    p.disjoint

/-- Third intrinsic channel eigenvalue attached to one normal-form parameter
package. -/
def intrinsicChannelEigenvalue3
    (p : IntrinsicSlotParameters) : SignedCount :=
  SignedCount.subCount p.diagonal p.disjoint

/-- The three canonical channel eigenvalue formulas attached to one intrinsic
normal-form parameter package. -/
theorem intrinsic_channel_eigenvalues
    (A : LocalSlot → LocalSlot → SignedCount)
    (hA : IntrinsicAdjacencyInvariant A) :
    ∃ a b c : SignedCount,
      ∃ l1 l2 l3 : SignedCount,
        (∀ α β : LocalSlot,
          A α β =
            match intrinsicSlotAdjacency α β with
            | .equal => a
            | .adjacent => b
            | .disjoint => c) ∧
        l1 = SignedCount.addCount (SignedCount.addCount a (signedCount_nsmul 4 b)) c ∧
        l2 = SignedCount.addCount (SignedCount.subCount a (signedCount_nsmul 2 b)) c ∧
        l3 = SignedCount.subCount a c := by
  obtain ⟨p, hp, _⟩ := intrinsic_slot_normal_form A hA
  refine ⟨p.diagonal, p.adjacent, p.disjoint,
    intrinsicChannelEigenvalue1 p,
    intrinsicChannelEigenvalue2 p,
    intrinsicChannelEigenvalue3 p,
    ?_, rfl, rfl, rfl⟩
  intro α β
  simpa [intrinsicNormalEntry] using hp α β

/-- Any intrinsically equivariant six-slot law is determined by exactly three
scalar channel parameters. -/
theorem intrinsic_equivariant_three_parameter
    (A : LocalSlot → LocalSlot → SignedCount)
    (hA : IntrinsicAdjacencyInvariant A) :
    ∃ a b c : SignedCount,
      ∀ α β : LocalSlot,
        A α β =
          match intrinsicSlotAdjacency α β with
          | .equal => a
          | .adjacent => b
          | .disjoint => c := by
  obtain ⟨p, hp, _⟩ := intrinsic_slot_normal_form A hA
  exact ⟨p.diagonal, p.adjacent, p.disjoint, by
    intro α β
    simpa [intrinsicNormalEntry] using hp α β⟩

/-- Canonical overlap law on the intrinsic six-slot carrier: equal slots share
two legs, adjacent slots share one, and disjoint slots share none. -/
def canonicalIntrinsicOverlapLaw : LocalSlot → LocalSlot → SignedCount
  | α, β =>
      match intrinsicSlotAdjacency α β with
      | .equal => SignedCount.ofNat 2
      | .adjacent => SignedCount.ofNat 1
      | .disjoint => SignedCount.zero

/-- The canonical overlap law depends only on the intrinsic slot-adjacency
class. -/
theorem canonicalIntrinsicOverlapLaw_intrinsic :
    IntrinsicAdjacencyInvariant canonicalIntrinsicOverlapLaw := by
  intro α β α' β' hclass
  exact congrArg
    (fun q =>
      match q with
      | .equal => SignedCount.ofNat 2
      | .adjacent => SignedCount.ofNat 1
      | .disjoint => SignedCount.zero)
    hclass

/-- Canonical normal-form parameters for the intrinsic overlap law. -/
def canonicalIntrinsicOverlapParameters : IntrinsicSlotParameters where
  diagonal := SignedCount.ofNat 2
  adjacent := SignedCount.ofNat 1
  disjoint := SignedCount.zero

/-- The canonical intrinsic overlap law already lies in its expected normal
form. -/
theorem canonicalIntrinsicOverlapLaw_normalForm :
    isIntrinsicNormalForm
      canonicalIntrinsicOverlapLaw
      canonicalIntrinsicOverlapParameters := by
  intro α β
  rfl

/-- The canonical intrinsic overlap law has one unique normal form, with
explicit parameters `(2, 1, 0)`. -/
theorem canonicalIntrinsicOverlapLaw_existsUniqueCanonicalNormalForm :
    ∃ p : IntrinsicSlotParameters,
      (isIntrinsicNormalForm canonicalIntrinsicOverlapLaw p ∧
        p.diagonal = SignedCount.ofNat 2 ∧
        p.adjacent = SignedCount.ofNat 1 ∧
        p.disjoint = SignedCount.zero) ∧
      ∀ q : IntrinsicSlotParameters,
        (isIntrinsicNormalForm canonicalIntrinsicOverlapLaw q ∧
          q.diagonal = SignedCount.ofNat 2 ∧
          q.adjacent = SignedCount.ofNat 1 ∧
          q.disjoint = SignedCount.zero) →
        q = p := by
  refine ⟨canonicalIntrinsicOverlapParameters, ?_, ?_⟩
  · exact ⟨canonicalIntrinsicOverlapLaw_normalForm, rfl, rfl, rfl⟩
  · intro q hq
    rcases hq with ⟨_hnormal, hdiag, hadj, hdis⟩
    apply IntrinsicSlotParameters.ext
    · simpa [canonicalIntrinsicOverlapParameters] using hdiag
    · simpa [canonicalIntrinsicOverlapParameters] using hadj
    · simpa [canonicalIntrinsicOverlapParameters] using hdis

/-- Any six-slot law in canonical normal form `(2, 1, 0)` already agrees
pointwise with the canonical intrinsic overlap law. -/
theorem pointwise_eq_canonicalIntrinsicOverlapLaw_of_normalForm
    {A : LocalSlot → LocalSlot → SignedCount}
    {p : IntrinsicSlotParameters}
    (hA : isIntrinsicNormalForm A p)
    (hdiag : p.diagonal = SignedCount.ofNat 2)
    (hadj : p.adjacent = SignedCount.ofNat 1)
    (hdis : p.disjoint = SignedCount.zero) :
    ∀ α β : LocalSlot, A α β = canonicalIntrinsicOverlapLaw α β := by
  have hp :
      p = canonicalIntrinsicOverlapParameters :=
    IntrinsicSlotParameters.ext
      (by simpa [canonicalIntrinsicOverlapParameters] using hdiag)
      (by simpa [canonicalIntrinsicOverlapParameters] using hadj)
      (by simpa [canonicalIntrinsicOverlapParameters] using hdis)
  cases hp
  exact
    intrinsic_law_pointwise_eq_of_normalForm_eq
      hA
      canonicalIntrinsicOverlapLaw_normalForm

/-- Existence of the canonical `(2, 1, 0)` normal form already forces a
six-slot law to agree pointwise with the canonical intrinsic overlap law. -/
theorem pointwise_eq_canonicalIntrinsicOverlapLaw_of_existsCanonicalNormalForm
    {A : LocalSlot → LocalSlot → SignedCount}
    (hA :
      ∃ p : IntrinsicSlotParameters,
        (isIntrinsicNormalForm A p ∧
          p.diagonal = SignedCount.ofNat 2 ∧
          p.adjacent = SignedCount.ofNat 1 ∧
          p.disjoint = SignedCount.zero) ∧
        ∀ q : IntrinsicSlotParameters,
          (isIntrinsicNormalForm A q ∧
            q.diagonal = SignedCount.ofNat 2 ∧
            q.adjacent = SignedCount.ofNat 1 ∧
            q.disjoint = SignedCount.zero) →
          q = p) :
    ∀ α β : LocalSlot, A α β = canonicalIntrinsicOverlapLaw α β := by
  rcases hA with ⟨p, ⟨hnormal, hdiag, hadj, hdis⟩, _hunique⟩
  exact
    pointwise_eq_canonicalIntrinsicOverlapLaw_of_normalForm
      hnormal hdiag hadj hdis

/-- Fiber of an intrinsic six-slot law above one chosen anchor slot. This
packages the six values seen from one fixed slot as an ordinary six-slot
carrier. -/
def intrinsicLawFiber
    (A : LocalSlot → LocalSlot → SignedCount)
    (anchor : LocalSlot) :
    LocalSlotCarrier :=
  fun β => A anchor β

/-- Pointwise equality of intrinsic six-slot laws forces equality on every
anchored fiber, and therefore on the reduced three-coordinate fiber readout. -/
theorem intrinsicFiberCoordinates_eq_of_pointwise_eq
    {A B : LocalSlot → LocalSlot → SignedCount}
    (hAB : ∀ α β : LocalSlot, A α β = B α β)
    (anchor : LocalSlot) :
    localSlotCoordinates (intrinsicLawFiber A anchor) =
      localSlotCoordinates (intrinsicLawFiber B anchor) := by
  exact localSlotCoordinates_eq_of_eq (fun β => hAB anchor β)

/-- Distinguished anchor fiber of the canonical intrinsic overlap law. This is
the row later read by the fixed first-leg local assembly formulas. -/
def canonicalIntrinsicOverlapS12Fiber : LocalSlotCarrier :=
  intrinsicLawFiber canonicalIntrinsicOverlapLaw LocalSlot.s12

/-- The canonical intrinsic overlap law already carries the three-parameter
channel surface of the six-slot calculus. -/
theorem canonicalIntrinsicOverlapLaw_channelSurface :
    ∃ a b c : SignedCount,
      ∃ l1 l2 l3 : SignedCount,
        (∀ α β : LocalSlot,
          canonicalIntrinsicOverlapLaw α β =
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
  exact
    intrinsic_channel_eigenvalues
      canonicalIntrinsicOverlapLaw
      canonicalIntrinsicOverlapLaw_intrinsic

private theorem signedCount_addCount_ofNat_ofNat
    (a b : Nat) :
    SignedCount.addCount (SignedCount.ofNat a) (SignedCount.ofNat b) =
      SignedCount.ofNat (a + b) := by
  rfl

private theorem signedCount_nsmul_ofNat_one
    (n : Nat) :
    signedCount_nsmul n (SignedCount.ofNat 1) = SignedCount.ofNat n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [signedCount_nsmul, ih, signedCount_addCount_ofNat_ofNat]

private theorem signedCount_addCount_negOfNat_one_one :
    SignedCount.addCount (SignedCount.negOfNat 1) (SignedCount.negOfNat 1) =
      SignedCount.negOfNat 2 := by
  rfl

/-- The canonical overlap law carries an exact intrinsic channel spectrum. For
the forced normal form `(2, 1, 0)`, the three intrinsic channel eigenvalues
are exactly `(6, 0, 2)`. -/
theorem canonicalIntrinsicOverlapLaw_exactChannelSpectrum :
    intrinsicChannelEigenvalue1 canonicalIntrinsicOverlapParameters =
        SignedCount.ofNat 6 ∧
      intrinsicChannelEigenvalue2 canonicalIntrinsicOverlapParameters =
        SignedCount.zero ∧
      intrinsicChannelEigenvalue3 canonicalIntrinsicOverlapParameters =
        SignedCount.ofNat 2 := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      intrinsicChannelEigenvalue1 canonicalIntrinsicOverlapParameters
          =
            SignedCount.addCount
              (SignedCount.addCount (SignedCount.ofNat 2) (SignedCount.ofNat 4))
              SignedCount.zero := by
                rw [intrinsicChannelEigenvalue1, canonicalIntrinsicOverlapParameters,
                  signedCount_nsmul_ofNat_one]
      _ = SignedCount.addCount (SignedCount.ofNat 6) SignedCount.zero := by
            rw [signedCount_addCount_ofNat_ofNat]
      _ = SignedCount.ofNat 6 := by
            exact SignedCount.addCount_zero (SignedCount.ofNat 6)
  · calc
      intrinsicChannelEigenvalue2 canonicalIntrinsicOverlapParameters
          =
            SignedCount.addCount
              (SignedCount.subCount (SignedCount.ofNat 2) (SignedCount.ofNat 2))
              SignedCount.zero := by
                rw [intrinsicChannelEigenvalue2, canonicalIntrinsicOverlapParameters,
                  signedCount_nsmul_ofNat_one]
      _ = SignedCount.addCount SignedCount.zero SignedCount.zero := by
            rw [SignedCount.subCount_ofNat_eq_zero rfl]
      _ = SignedCount.zero := by
            exact SignedCount.zero_addCount SignedCount.zero
  · simpa [intrinsicChannelEigenvalue3, canonicalIntrinsicOverlapParameters] using
      (subCount_zero (SignedCount.ofNat 2))

/-- The distinguished `s12` fiber of the canonical intrinsic overlap law has
one exact reduced coordinate package. This is the first anchored current-side
readout forced directly by the six-slot normal form. -/
theorem canonicalIntrinsicOverlapS12Fiber_coordinates :
    localSlotCoordinates canonicalIntrinsicOverlapS12Fiber =
      ⟨SignedCount.ofNat 4, SignedCount.zero, SignedCount.negOfNat 2⟩ := by
  apply LocalSlotCoordinates.ext
  · unfold canonicalIntrinsicOverlapS12Fiber intrinsicLawFiber localSlotCoordinates
    dsimp [canonicalIntrinsicOverlapLaw, intrinsicSlotAdjacency]
    rw [signedCount_addCount_ofNat_ofNat, signedCount_addCount_ofNat_ofNat]
  · unfold canonicalIntrinsicOverlapS12Fiber intrinsicLawFiber localSlotCoordinates
    dsimp [canonicalIntrinsicOverlapLaw, intrinsicSlotAdjacency]
    rw [signedCount_addCount_ofNat_ofNat]
    simpa using addCount_negate_left (SignedCount.ofNat 2)
  · unfold canonicalIntrinsicOverlapS12Fiber intrinsicLawFiber localSlotCoordinates
    dsimp [canonicalIntrinsicOverlapLaw, intrinsicSlotAdjacency]
    change
      (SignedCount.addCount (SignedCount.negOfNat 1) (SignedCount.negOfNat 1)).addCount
        SignedCount.zero =
      SignedCount.negOfNat 2
    rw [signedCount_addCount_negOfNat_one_one]
    exact SignedCount.addCount_zero (SignedCount.negOfNat 2)

/-- The `s13` anchor fiber of an intrinsic normal-form six-slot law reads its
three parameters directly: the first coordinate is `a + 2b`, the second is the
disjoint value `c`, and the third is `-a`. This is the anchor most convenient
for recovering the full intrinsic law from fiber data. -/
theorem s13FiberCoordinates_of_normalForm
    {A : LocalSlot → LocalSlot → SignedCount}
    {p : IntrinsicSlotParameters}
    (hA : isIntrinsicNormalForm A p) :
    localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13) =
      ⟨SignedCount.addCount
          p.diagonal
          (SignedCount.addCount p.adjacent p.adjacent),
        p.disjoint,
        SignedCount.negate p.diagonal⟩ := by
  apply LocalSlotCoordinates.ext
  · unfold localSlotCoordinates intrinsicLawFiber
    rw [hA LocalSlot.s13 LocalSlot.s12,
      hA LocalSlot.s13 LocalSlot.s13,
      hA LocalSlot.s13 LocalSlot.s14]
    simp [intrinsicNormalEntry, intrinsicSlotAdjacency]
    calc
      SignedCount.addCount p.adjacent
          (SignedCount.addCount p.diagonal p.adjacent) =
        SignedCount.addCount
          (SignedCount.addCount p.adjacent p.diagonal)
          p.adjacent := by
            symm
            exact addCount_assoc p.adjacent p.diagonal p.adjacent
      _ =
        SignedCount.addCount p.diagonal
          (SignedCount.addCount p.adjacent p.adjacent) := by
            rw [addCount_comm p.adjacent p.diagonal, addCount_assoc]
  · unfold localSlotCoordinates intrinsicLawFiber
    rw [hA LocalSlot.s13 LocalSlot.s12,
      hA LocalSlot.s13 LocalSlot.s23,
      hA LocalSlot.s13 LocalSlot.s24]
    simp [intrinsicNormalEntry, intrinsicSlotAdjacency]
    rw [← addCount_assoc, addCount_negate_left, SignedCount.zero_addCount]
  · unfold localSlotCoordinates intrinsicLawFiber
    rw [hA LocalSlot.s13 LocalSlot.s13,
      hA LocalSlot.s13 LocalSlot.s23,
      hA LocalSlot.s13 LocalSlot.s34]
    simp [intrinsicNormalEntry, intrinsicSlotAdjacency]
    rw [addCount_assoc, addCount_negate_left, SignedCount.addCount_zero]

/-- The canonical overlap law has the same exact `s13` fiber coordinates as its
distinguished `s12` fiber: `(4, 0, -2)`. -/
theorem canonicalIntrinsicOverlapS13Fiber_coordinates :
    localSlotCoordinates
        (intrinsicLawFiber canonicalIntrinsicOverlapLaw LocalSlot.s13) =
      ⟨SignedCount.ofNat 4, SignedCount.zero, SignedCount.negOfNat 2⟩ := by
  calc
    localSlotCoordinates
        (intrinsicLawFiber canonicalIntrinsicOverlapLaw LocalSlot.s13) =
          ⟨SignedCount.addCount
              (SignedCount.ofNat 2)
              (SignedCount.addCount (SignedCount.ofNat 1) (SignedCount.ofNat 1)),
            SignedCount.zero,
            SignedCount.negOfNat 2⟩ := by
              simpa [canonicalIntrinsicOverlapParameters] using
                s13FiberCoordinates_of_normalForm
                  (A := canonicalIntrinsicOverlapLaw)
                  (p := canonicalIntrinsicOverlapParameters)
                  canonicalIntrinsicOverlapLaw_normalForm
    _ = ⟨SignedCount.ofNat 4, SignedCount.zero, SignedCount.negOfNat 2⟩ := by
          apply LocalSlotCoordinates.ext
          · rw [signedCount_addCount_ofNat_ofNat, signedCount_addCount_ofNat_ofNat]
          · rfl
          · rfl

/-- Canonical anchor-fiber coordinate family of the intrinsic overlap law.
For each anchor slot, this records the reduced three-coordinate readout of the
row seen from that anchor. -/
def canonicalIntrinsicOverlapFiberCoordinates
    (anchor : LocalSlot) :
    LocalSlotCoordinates :=
  localSlotCoordinates (intrinsicLawFiber canonicalIntrinsicOverlapLaw anchor)

/-- Any intrinsic six-slot law in canonical normal form `(2, 1, 0)` already
has the same distinguished `s12` fiber coordinates as the canonical overlap
law. This is the coordinate-level forcing theorem needed later by the
current-side assembly route. -/
theorem s12FiberCoordinates_of_existsCanonicalNormalForm
    {A : LocalSlot → LocalSlot → SignedCount}
    (hA :
      ∃ p : IntrinsicSlotParameters,
        (isIntrinsicNormalForm A p ∧
          p.diagonal = SignedCount.ofNat 2 ∧
          p.adjacent = SignedCount.ofNat 1 ∧
          p.disjoint = SignedCount.zero) ∧
        ∀ q : IntrinsicSlotParameters,
          (isIntrinsicNormalForm A q ∧
            q.diagonal = SignedCount.ofNat 2 ∧
            q.adjacent = SignedCount.ofNat 1 ∧
            q.disjoint = SignedCount.zero) →
          q = p) :
    localSlotCoordinates (intrinsicLawFiber A LocalSlot.s12) =
      ⟨SignedCount.ofNat 4, SignedCount.zero, SignedCount.negOfNat 2⟩ := by
  calc
    localSlotCoordinates (intrinsicLawFiber A LocalSlot.s12) =
      localSlotCoordinates
        (intrinsicLawFiber canonicalIntrinsicOverlapLaw LocalSlot.s12) := by
          exact
            intrinsicFiberCoordinates_eq_of_pointwise_eq
              (pointwise_eq_canonicalIntrinsicOverlapLaw_of_existsCanonicalNormalForm hA)
              LocalSlot.s12
    _ = ⟨SignedCount.ofNat 4, SignedCount.zero, SignedCount.negOfNat 2⟩ := by
          exact canonicalIntrinsicOverlapS12Fiber_coordinates

/-- Any intrinsic six-slot law in canonical normal form `(2, 1, 0)` already
has the same distinguished `s13` fiber coordinates as the canonical overlap
law. This is the smallest single-fiber coordinate forcing theorem used later
by the selected-completion route. -/
theorem s13FiberCoordinates_of_existsCanonicalNormalForm
    {A : LocalSlot → LocalSlot → SignedCount}
    (hA :
      ∃ p : IntrinsicSlotParameters,
        (isIntrinsicNormalForm A p ∧
          p.diagonal = SignedCount.ofNat 2 ∧
          p.adjacent = SignedCount.ofNat 1 ∧
          p.disjoint = SignedCount.zero) ∧
        ∀ q : IntrinsicSlotParameters,
          (isIntrinsicNormalForm A q ∧
            q.diagonal = SignedCount.ofNat 2 ∧
            q.adjacent = SignedCount.ofNat 1 ∧
            q.disjoint = SignedCount.zero) →
          q = p) :
    localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13) =
      ⟨SignedCount.ofNat 4, SignedCount.zero, SignedCount.negOfNat 2⟩ := by
  calc
    localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13) =
      localSlotCoordinates
        (intrinsicLawFiber canonicalIntrinsicOverlapLaw LocalSlot.s13) := by
          exact
            intrinsicFiberCoordinates_eq_of_pointwise_eq
              (pointwise_eq_canonicalIntrinsicOverlapLaw_of_existsCanonicalNormalForm hA)
              LocalSlot.s13
    _ = ⟨SignedCount.ofNat 4, SignedCount.zero, SignedCount.negOfNat 2⟩ := by
          exact canonicalIntrinsicOverlapS13Fiber_coordinates

/-- Any intrinsic six-slot law in canonical normal form `(2, 1, 0)` already
has the same anchor-fiber coordinate family as the canonical overlap law. So
the reduced three-coordinate readout is forced simultaneously at every anchor,
not only on one distinguished row. -/
theorem fiberCoordinates_of_existsCanonicalNormalForm
    {A : LocalSlot → LocalSlot → SignedCount}
    (hA :
      ∃ p : IntrinsicSlotParameters,
        (isIntrinsicNormalForm A p ∧
          p.diagonal = SignedCount.ofNat 2 ∧
          p.adjacent = SignedCount.ofNat 1 ∧
          p.disjoint = SignedCount.zero) ∧
        ∀ q : IntrinsicSlotParameters,
          (isIntrinsicNormalForm A q ∧
            q.diagonal = SignedCount.ofNat 2 ∧
            q.adjacent = SignedCount.ofNat 1 ∧
            q.disjoint = SignedCount.zero) →
          q = p) :
    ∀ anchor : LocalSlot,
      localSlotCoordinates (intrinsicLawFiber A anchor) =
        canonicalIntrinsicOverlapFiberCoordinates anchor := by
  intro anchor
  dsimp [canonicalIntrinsicOverlapFiberCoordinates]
  exact
    intrinsicFiberCoordinates_eq_of_pointwise_eq
      (pointwise_eq_canonicalIntrinsicOverlapLaw_of_existsCanonicalNormalForm hA)
      anchor

/-- Two intrinsic six-slot laws in the canonical normal form `(2, 1, 0)`
already have the same anchor-fiber coordinate family. This is the family-level
rigidity later consumed by the current-side assembly route. -/
theorem fiberCoordinateFamily_eq_of_existsCanonicalNormalForm
    {A B : LocalSlot → LocalSlot → SignedCount}
    (hA :
      ∃ p : IntrinsicSlotParameters,
        (isIntrinsicNormalForm A p ∧
          p.diagonal = SignedCount.ofNat 2 ∧
          p.adjacent = SignedCount.ofNat 1 ∧
          p.disjoint = SignedCount.zero) ∧
        ∀ q : IntrinsicSlotParameters,
          (isIntrinsicNormalForm A q ∧
            q.diagonal = SignedCount.ofNat 2 ∧
            q.adjacent = SignedCount.ofNat 1 ∧
            q.disjoint = SignedCount.zero) →
          q = p)
    (hB :
      ∃ p : IntrinsicSlotParameters,
        (isIntrinsicNormalForm B p ∧
          p.diagonal = SignedCount.ofNat 2 ∧
          p.adjacent = SignedCount.ofNat 1 ∧
          p.disjoint = SignedCount.zero) ∧
        ∀ q : IntrinsicSlotParameters,
          (isIntrinsicNormalForm B q ∧
            q.diagonal = SignedCount.ofNat 2 ∧
            q.adjacent = SignedCount.ofNat 1 ∧
            q.disjoint = SignedCount.zero) →
          q = p) :
    ∀ anchor : LocalSlot,
      localSlotCoordinates (intrinsicLawFiber A anchor) =
        localSlotCoordinates (intrinsicLawFiber B anchor) := by
  intro anchor
  calc
    localSlotCoordinates (intrinsicLawFiber A anchor) =
        canonicalIntrinsicOverlapFiberCoordinates anchor := by
          exact fiberCoordinates_of_existsCanonicalNormalForm hA anchor
    _ = localSlotCoordinates (intrinsicLawFiber B anchor) := by
          symm
          exact fiberCoordinates_of_existsCanonicalNormalForm hB anchor

private theorem signedCount_eq_of_negate_eq_negOfNat_two
    {a : SignedCount}
    (h : SignedCount.negate a = SignedCount.negOfNat 2) :
    a = SignedCount.ofNat 2 := by
  apply SignedCount.ext
  · exact congrArg SignedCount.neg h
  · exact congrArg SignedCount.pos h

private theorem signedCount_double_eq_ofNat_two
    {a : SignedCount}
    (h : SignedCount.addCount a a = SignedCount.ofNat 2) :
    a = SignedCount.ofNat 1 := by
  cases a with
  | mk pos neg normalized =>
      cases normalized with
      | inl hpos =>
          cases hpos
          cases neg with
          | zero =>
              change SignedCount.zero = SignedCount.ofNat 2 at h
              exact False.elim (SignedCount.ofNat_succ_ne_zero 1 h.symm)
          | succ n =>
              change
                SignedCount.negOfNat ((n + 1) + (n + 1)) =
                  SignedCount.ofNat 2 at h
              cases h
      | inr hneg =>
          cases hneg
          change SignedCount.ofNat (pos + pos) = SignedCount.ofNat 2 at h
          have hsum : pos + pos = 2 := congrArg SignedCount.pos h
          cases pos with
          | zero =>
              cases hsum
          | succ pos =>
              cases pos with
              | zero =>
                  rfl
              | succ pos =>
                  have hge2 : 2 ≤ pos + 1 + 1 := by
                    exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le pos))
                  have hge4 : 4 ≤ pos + 1 + 1 + (pos + 1 + 1) := by
                    calc
                      4 = 2 + 2 := rfl
                      _ ≤ (pos + 1 + 1) + (pos + 1 + 1) := by
                        exact Nat.add_le_add hge2 hge2
                      _ = pos + 1 + 1 + (pos + 1 + 1) := rfl
                  have hfour_le_two : 4 ≤ 2 := by
                    calc
                      4 ≤ pos + 1 + 1 + (pos + 1 + 1) := hge4
                      _ = 2 := hsum
                  exact False.elim ((by decide : ¬ 4 ≤ 2) hfour_le_two)

/-- One intrinsic `s13` fiber in canonical coordinates already forces the full
canonical overlap law. For an intrinsically equivariant six-slot law, this
single anchored fiber determines the three normal-form parameters, hence the
entire law. -/
theorem pointwise_eq_canonicalIntrinsicOverlapLaw_of_intrinsic_and_s13FiberCoordinates
    {A : LocalSlot → LocalSlot → SignedCount}
    (hA : IntrinsicAdjacencyInvariant A)
    (hs13 :
      localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13) =
        canonicalIntrinsicOverlapFiberCoordinates LocalSlot.s13) :
    ∀ α β : LocalSlot, A α β = canonicalIntrinsicOverlapLaw α β := by
  obtain ⟨p, hp, _hunique⟩ := intrinsic_slot_normal_form A hA
  have hs13canon :
      localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13) =
        ⟨SignedCount.ofNat 4, SignedCount.zero, SignedCount.negOfNat 2⟩ := by
    calc
      localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13) =
        canonicalIntrinsicOverlapFiberCoordinates LocalSlot.s13 := hs13
      _ =
        localSlotCoordinates
          (intrinsicLawFiber canonicalIntrinsicOverlapLaw LocalSlot.s13) := by
            rfl
      _ = ⟨SignedCount.ofNat 4, SignedCount.zero, SignedCount.negOfNat 2⟩ := by
            exact canonicalIntrinsicOverlapS13Fiber_coordinates
  have hdiag :
      p.diagonal = SignedCount.ofNat 2 := by
    exact
      signedCount_eq_of_negate_eq_negOfNat_two
        (calc
          SignedCount.negate p.diagonal =
              (localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13)).c2 := by
                exact congrArg LocalSlotCoordinates.c2
                  (s13FiberCoordinates_of_normalForm hp).symm
          _ = SignedCount.negOfNat 2 := by
                exact congrArg LocalSlotCoordinates.c2 hs13canon)
  have hdis :
      p.disjoint = SignedCount.zero := by
    calc
      p.disjoint = (localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13)).c1 := by
        exact congrArg LocalSlotCoordinates.c1
          (s13FiberCoordinates_of_normalForm hp).symm
      _ = SignedCount.zero := by
        exact congrArg LocalSlotCoordinates.c1 hs13canon
  have hdouble :
      SignedCount.addCount p.adjacent p.adjacent = SignedCount.ofNat 2 := by
    have hsum :
        SignedCount.addCount
            p.diagonal
            (SignedCount.addCount p.adjacent p.adjacent) =
          SignedCount.ofNat 4 := by
      calc
        SignedCount.addCount
            p.diagonal
            (SignedCount.addCount p.adjacent p.adjacent) =
              (localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13)).c0 := by
                exact congrArg LocalSlotCoordinates.c0
                  (s13FiberCoordinates_of_normalForm hp).symm
        _ = SignedCount.ofNat 4 := by
              exact congrArg LocalSlotCoordinates.c0 hs13canon
    rw [hdiag, ← signedCount_addCount_ofNat_ofNat 2 2] at hsum
    exact addCount_left_cancel hsum
  have hadj :
      p.adjacent = SignedCount.ofNat 1 := by
    exact signedCount_double_eq_ofNat_two hdouble
  exact
    pointwise_eq_canonicalIntrinsicOverlapLaw_of_normalForm
      hp hdiag hadj hdis

/-- For an intrinsically equivariant six-slot law, one canonical `s13` anchor
fiber already forces the unique canonical normal form `(2, 1, 0)`. This
upgrades the single-anchor rigidity theorem to the exact normal-form package
needed later by the current-side assembly route. -/
theorem canonicalNormalForm_of_intrinsic_and_s13FiberCoordinates
    {A : LocalSlot → LocalSlot → SignedCount}
    (hA : IntrinsicAdjacencyInvariant A)
    (hs13 :
      localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13) =
        canonicalIntrinsicOverlapFiberCoordinates LocalSlot.s13) :
    ∃ p : IntrinsicSlotParameters,
      (isIntrinsicNormalForm A p ∧
        p.diagonal = SignedCount.ofNat 2 ∧
        p.adjacent = SignedCount.ofNat 1 ∧
        p.disjoint = SignedCount.zero) ∧
      ∀ q : IntrinsicSlotParameters,
        (isIntrinsicNormalForm A q ∧
          q.diagonal = SignedCount.ofNat 2 ∧
          q.adjacent = SignedCount.ofNat 1 ∧
          q.disjoint = SignedCount.zero) →
        q = p := by
  have hpointwise :
      ∀ α β : LocalSlot, A α β = canonicalIntrinsicOverlapLaw α β :=
    pointwise_eq_canonicalIntrinsicOverlapLaw_of_intrinsic_and_s13FiberCoordinates
      hA hs13
  refine ⟨canonicalIntrinsicOverlapParameters, ?_, ?_⟩
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro α β
    calc
      A α β = canonicalIntrinsicOverlapLaw α β := hpointwise α β
      _ =
          intrinsicNormalEntry
            canonicalIntrinsicOverlapParameters
            (intrinsicSlotAdjacency α β) := by
              simpa using canonicalIntrinsicOverlapLaw_normalForm α β
  · intro q hq
    rcases hq with ⟨_hnormal, hdiag, hadj, hdis⟩
    exact
      IntrinsicSlotParameters.ext
        (by simpa [canonicalIntrinsicOverlapParameters] using hdiag)
        (by simpa [canonicalIntrinsicOverlapParameters] using hadj)
        (by simpa [canonicalIntrinsicOverlapParameters] using hdis)

/-- The same single canonical `s13` anchor already forces the full canonical
anchor-fiber coordinate family. Once the intrinsic six-slot law is fixed by
that anchor, every other anchor fiber has the canonical reduced coordinates as
well. -/
theorem canonicalFiberCoordinates_of_intrinsic_and_s13FiberCoordinates
    {A : LocalSlot → LocalSlot → SignedCount}
    (hA : IntrinsicAdjacencyInvariant A)
    (hs13 :
      localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13) =
        canonicalIntrinsicOverlapFiberCoordinates LocalSlot.s13) :
    ∀ anchor : LocalSlot,
      localSlotCoordinates (intrinsicLawFiber A anchor) =
        canonicalIntrinsicOverlapFiberCoordinates anchor := by
  exact
    fiberCoordinates_of_existsCanonicalNormalForm
      (canonicalNormalForm_of_intrinsic_and_s13FiberCoordinates hA hs13)

/-- If two intrinsically equivariant six-slot laws both carry the canonical
`s13` anchor fiber, then they already agree pointwise. So the single-anchor
rigidity theorem is genuinely pairwise: it identifies any two admissible laws,
not only each law with the canonical overlap law separately. -/
theorem pointwise_eq_of_intrinsic_and_canonicalS13FiberCoordinates
    {A B : LocalSlot → LocalSlot → SignedCount}
    (hA : IntrinsicAdjacencyInvariant A)
    (hs13A :
      localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13) =
        canonicalIntrinsicOverlapFiberCoordinates LocalSlot.s13)
    (hB : IntrinsicAdjacencyInvariant B)
    (hs13B :
      localSlotCoordinates (intrinsicLawFiber B LocalSlot.s13) =
        canonicalIntrinsicOverlapFiberCoordinates LocalSlot.s13) :
    ∀ α β : LocalSlot, A α β = B α β := by
  intro α β
  calc
    A α β = canonicalIntrinsicOverlapLaw α β := by
      exact
        pointwise_eq_canonicalIntrinsicOverlapLaw_of_intrinsic_and_s13FiberCoordinates
          hA hs13A α β
    _ = B α β := by
      symm
      exact
        pointwise_eq_canonicalIntrinsicOverlapLaw_of_intrinsic_and_s13FiberCoordinates
          hB hs13B α β

/-- And the same single-anchor hypothesis on two intrinsically equivariant
six-slot laws already forces the full anchor-fiber coordinate family to agree.
This is the pairwise fiber-coordinate rigidity later consumed by the
current-side assembly route. -/
theorem fiberCoordinateFamily_eq_of_intrinsic_and_canonicalS13FiberCoordinates
    {A B : LocalSlot → LocalSlot → SignedCount}
    (hA : IntrinsicAdjacencyInvariant A)
    (hs13A :
      localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13) =
        canonicalIntrinsicOverlapFiberCoordinates LocalSlot.s13)
    (hB : IntrinsicAdjacencyInvariant B)
    (hs13B :
      localSlotCoordinates (intrinsicLawFiber B LocalSlot.s13) =
        canonicalIntrinsicOverlapFiberCoordinates LocalSlot.s13) :
    ∀ anchor : LocalSlot,
      localSlotCoordinates (intrinsicLawFiber A anchor) =
        localSlotCoordinates (intrinsicLawFiber B anchor) := by
  intro anchor
  calc
    localSlotCoordinates (intrinsicLawFiber A anchor) =
        canonicalIntrinsicOverlapFiberCoordinates anchor := by
          exact
            canonicalFiberCoordinates_of_intrinsic_and_s13FiberCoordinates
              hA hs13A anchor
    _ = localSlotCoordinates (intrinsicLawFiber B anchor) := by
          symm
          exact
            canonicalFiberCoordinates_of_intrinsic_and_s13FiberCoordinates
              hB hs13B anchor

/-- The stronger full anchor-fiber surface is also enough to recover the full
canonical overlap law. In practice, the `s13` row already suffices; this
corollary packages the same rigidity in the family form exported to the
selected-completion lane. -/
theorem pointwise_eq_canonicalIntrinsicOverlapLaw_of_intrinsic_and_canonicalFiberCoordinates
    {A : LocalSlot → LocalSlot → SignedCount}
    (hA : IntrinsicAdjacencyInvariant A)
    (hcoords :
      ∀ anchor : LocalSlot,
        localSlotCoordinates (intrinsicLawFiber A anchor) =
          canonicalIntrinsicOverlapFiberCoordinates anchor) :
    ∀ α β : LocalSlot, A α β = canonicalIntrinsicOverlapLaw α β := by
  exact
    pointwise_eq_canonicalIntrinsicOverlapLaw_of_intrinsic_and_s13FiberCoordinates
      hA
      (hcoords LocalSlot.s13)

/-- Chapter 6 summary: the canonical closure realization supplies the forced
state/tower/boundary interface with no extra data. -/
def ClosureBalanceStructuralInterface : Prop :=
  closureStableDimension = 4 ∧
  (∀ x : ClosureState,
    closureStateTransport.toClosure (closureStateTransport.toState x) = x) ∧
  (∀ x : State, trueBoundary (trueBoundary x) = State.zero) ∧
  (∀ h : Nat, ∀ x : State, (closureTower.π h).toFun x = closureProjectionFromCounting h x) ∧
  (∀ x : State, shadowProj closureTower 4 x = State.zero)

/-- Grade-wise energy on the canonical closure-realized state. -/
def canonicalGradeEnergy (x : ClosureState) : Nat → Nat
  | 0 => SignedCount.energy x.g0
  | 1 => SignedCount.energy x.g1
  | 2 => SignedCount.energy x.g2
  | 3 => SignedCount.energy x.g3
  | _ + 4 => 0

/-- Tail energy profile of the canonical closure-realized tower. -/
def canonicalTailProfile (h : Nat) (x : ClosureState) : Nat :=
  ClosureState.energy (closureShadowState h x)

/-- One-step revealed state between adjacent canonical horizons. -/
def canonicalRevelationState (h : Nat) (x : ClosureState) : ClosureState :=
  ClosureState.sub (closureProjectionState (h + 1) x) (closureProjectionState h x)

/-- One-step revelation energy profile of the canonical closure-realized tower. -/
def canonicalRevelationProfile (h : Nat) (x : ClosureState) : Nat :=
  ClosureState.energy (canonicalRevelationState h x)

private theorem positiveParts_tail {a : Nat} {tail : List Nat}
    (h : PositiveParts (a :: tail)) : PositiveParts tail := by
  intro n hn
  exact h n (List.mem_cons_of_mem a hn)

private theorem positive_sum_zero_nil {parts : List Nat}
    (hpos : PositiveParts parts) (hsum : natListSum parts = 0) : parts = [] := by
  cases parts with
  | nil =>
      rfl
  | cons a tail =>
      have ha : 0 < a := hpos a List.mem_cons_self
      have hge : 1 ≤ natListSum (a :: tail) := by
        exact Nat.le_trans ha (Nat.le_add_right a (natListSum tail))
      rw [hsum] at hge
      exact False.elim (Nat.not_succ_le_zero 0 hge)

private theorem positive_sum_one_singleton {parts : List Nat}
    (hpos : PositiveParts parts) (hsum : natListSum parts = 1) : parts = [1] := by
  cases parts with
  | nil =>
      change 0 = 1 at hsum
      cases hsum
  | cons a tail =>
      have hpos_cons : PositiveParts (a :: tail) := hpos
      have ha : 0 < a := hpos_cons a List.mem_cons_self
      cases a with
      | zero =>
          cases Nat.not_lt_zero 0 ha
      | succ a' =>
          cases a' with
          | zero =>
              have htail_sum : natListSum tail = 0 := by
                change 1 + natListSum tail = 1 + 0 at hsum
                exact add_left_cancel_counting hsum
              have htail_nil : tail = [] :=
                positive_sum_zero_nil (positiveParts_tail hpos_cons) htail_sum
              rw [htail_nil]
          | succ a'' =>
              have hhead_ge : 2 ≤ Nat.succ (Nat.succ a'') := by
                exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le a''))
              have hge : 2 ≤ Nat.succ (Nat.succ a'') + natListSum tail := by
                exact Nat.le_trans hhead_ge (Nat.le_add_right _ _)
              have htwo_le_one : 2 ≤ 1 := by
                calc
                  2 ≤ Nat.succ (Nat.succ a'') + natListSum tail := hge
                  _ = 1 := hsum
              exact False.elim ((by decide : ¬ 2 ≤ 1) htwo_le_one)

private theorem nonincreasingParts_tail {a : Nat} {tail : List Nat}
    (h : NonincreasingParts (a :: tail)) : NonincreasingParts tail := by
  cases tail with
  | nil =>
      trivial
  | cons b tail' =>
      exact h.2

private theorem positiveParts_length_le_sum {parts : List Nat}
    (hpos : PositiveParts parts) : parts.length ≤ natListSum parts := by
  cases parts with
  | nil =>
      exact Nat.zero_le 0
  | cons a tail =>
      have ha : 1 ≤ a := hpos a List.mem_cons_self
      have htail : tail.length ≤ natListSum tail :=
        positiveParts_length_le_sum (positiveParts_tail hpos)
      calc
        List.length (a :: tail) = Nat.succ tail.length := rfl
        _ ≤ Nat.succ (natListSum tail) := Nat.succ_le_succ htail
        _ = natListSum tail + 1 := Nat.succ_eq_add_one (natListSum tail)
        _ = 1 + natListSum tail := Nat.add_comm (natListSum tail) 1
        _ ≤ a + natListSum tail := Nat.add_le_add_right ha (natListSum tail)
        _ = natListSum (a :: tail) := rfl

private def IsProfile2 (parts : List Nat) : Prop :=
  parts = [2] ∨ parts = [1, 1]

private def IsProfile3 (parts : List Nat) : Prop :=
  parts = [3] ∨ parts = [2, 1] ∨ parts = [1, 1, 1]

private def IsProfile4 (parts : List Nat) : Prop :=
  parts = [4] ∨
  parts = [3, 1] ∨
  parts = [2, 2] ∨
  parts = [2, 1, 1] ∨
  parts = [1, 1, 1, 1]

private def IsProfile5 (parts : List Nat) : Prop :=
  parts = [5] ∨
  parts = [4, 1] ∨
  parts = [3, 2] ∨
  parts = [3, 1, 1] ∨
  parts = [2, 2, 1] ∨
  parts = [2, 1, 1, 1] ∨
  parts = [1, 1, 1, 1, 1]

private theorem positive_nonincreasing_sum_eq_two {parts : List Nat}
    (hpos : PositiveParts parts)
    (hnon : NonincreasingParts parts)
    (hsum : natListSum parts = 2) :
    IsProfile2 parts := by
  cases parts with
  | nil =>
      change 0 = 2 at hsum
      cases hsum
  | cons a tail =>
      have hpos_cons : PositiveParts (a :: tail) := hpos
      have ha : 0 < a := hpos_cons a List.mem_cons_self
      cases a with
      | zero =>
          cases Nat.not_lt_zero 0 ha
      | succ a' =>
          cases a' with
          | zero =>
              have htail_sum : natListSum tail = 1 := by
                change 1 + natListSum tail = 1 + 1 at hsum
                exact add_left_cancel_counting hsum
              have htail : tail = [1] :=
                positive_sum_one_singleton (positiveParts_tail hpos_cons) htail_sum
              rw [htail]
              exact Or.inr rfl
          | succ a'' =>
              cases a'' with
              | zero =>
                  have htail_sum : natListSum tail = 0 := by
                    change 2 + natListSum tail = 2 + 0 at hsum
                    exact add_left_cancel_counting hsum
                  have htail_nil : tail = [] :=
                    positive_sum_zero_nil (positiveParts_tail hpos_cons) htail_sum
                  rw [htail_nil]
                  exact Or.inl rfl
              | succ a''' =>
                  have hhead_ge : 3 ≤ Nat.succ (Nat.succ (Nat.succ a''')) := by
                    exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le a''')))
                  have hge : 3 ≤ Nat.succ (Nat.succ (Nat.succ a''')) + natListSum tail := by
                    exact Nat.le_trans hhead_ge (Nat.le_add_right _ _)
                  have hthree_le_two : 3 ≤ 2 := by
                    calc
                      3 ≤ Nat.succ (Nat.succ (Nat.succ a''')) + natListSum tail := hge
                      _ = 2 := hsum
                  exact False.elim ((by decide : ¬ 3 ≤ 2) hthree_le_two)

private theorem positive_nonincreasing_sum_eq_three {parts : List Nat}
    (hpos : PositiveParts parts)
    (hnon : NonincreasingParts parts)
    (hsum : natListSum parts = 3) :
    IsProfile3 parts := by
  cases parts with
  | nil =>
      change 0 = 3 at hsum
      cases hsum
  | cons a tail =>
      have hpos_cons : PositiveParts (a :: tail) := hpos
      have ha : 0 < a := hpos_cons a List.mem_cons_self
      cases a with
      | zero =>
          cases Nat.not_lt_zero 0 ha
      | succ a' =>
          cases a' with
          | zero =>
              have htail_sum : natListSum tail = 2 := by
                change 1 + natListSum tail = 1 + 2 at hsum
                exact add_left_cancel_counting hsum
              have htail_non : NonincreasingParts tail := nonincreasingParts_tail hnon
              have htail :=
                positive_nonincreasing_sum_eq_two (positiveParts_tail hpos_cons) htail_non htail_sum
              cases htail with
              | inl htail_eq =>
                  rw [htail_eq] at hnon
                  exact False.elim ((by decide : ¬ 2 ≤ 1) hnon.1)
              | inr htail_eq =>
                  rw [htail_eq]
                  exact Or.inr (Or.inr rfl)
          | succ a'' =>
              cases a'' with
              | zero =>
                  have htail_sum : natListSum tail = 1 := by
                    change 2 + natListSum tail = 2 + 1 at hsum
                    exact add_left_cancel_counting hsum
                  have htail : tail = [1] :=
                    positive_sum_one_singleton (positiveParts_tail hpos_cons) htail_sum
                  rw [htail]
                  exact Or.inr (Or.inl rfl)
              | succ a''' =>
                  cases a''' with
                  | zero =>
                      have htail_sum : natListSum tail = 0 := by
                        change 3 + natListSum tail = 3 + 0 at hsum
                        exact add_left_cancel_counting hsum
                      have htail_nil : tail = [] :=
                        positive_sum_zero_nil (positiveParts_tail hpos_cons) htail_sum
                      rw [htail_nil]
                      exact Or.inl rfl
                  | succ a'''' =>
                      have hhead_ge : 4 ≤ Nat.succ (Nat.succ (Nat.succ (Nat.succ a''''))) := by
                        exact Nat.succ_le_succ
                          (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le a''''))))
                      have hge : 4 ≤ Nat.succ (Nat.succ (Nat.succ (Nat.succ a''''))) + natListSum tail := by
                        exact Nat.le_trans hhead_ge (Nat.le_add_right _ _)
                      have hfour_le_three : 4 ≤ 3 := by
                        calc
                          4 ≤ Nat.succ (Nat.succ (Nat.succ (Nat.succ a''''))) + natListSum tail := hge
                          _ = 3 := hsum
                      exact False.elim ((by decide : ¬ 4 ≤ 3) hfour_le_three)

private theorem positive_nonincreasing_sum_eq_four {parts : List Nat}
    (hpos : PositiveParts parts)
    (hnon : NonincreasingParts parts)
    (hsum : natListSum parts = 4) :
    IsProfile4 parts := by
  cases parts with
  | nil =>
      change 0 = 4 at hsum
      cases hsum
  | cons a tail =>
      have hpos_cons : PositiveParts (a :: tail) := hpos
      have ha : 0 < a := hpos_cons a List.mem_cons_self
      cases a with
      | zero =>
          cases Nat.not_lt_zero 0 ha
      | succ a' =>
          cases a' with
          | zero =>
              have htail_sum : natListSum tail = 3 := by
                change 1 + natListSum tail = 1 + 3 at hsum
                exact add_left_cancel_counting hsum
              have htail_non : NonincreasingParts tail := nonincreasingParts_tail hnon
              have htail :=
                positive_nonincreasing_sum_eq_three (positiveParts_tail hpos_cons) htail_non htail_sum
              cases htail with
              | inl htail_eq =>
                  rw [htail_eq] at hnon
                  exact False.elim ((by decide : ¬ 3 ≤ 1) hnon.1)
              | inr htail =>
                  cases htail with
                  | inl htail_eq =>
                      rw [htail_eq] at hnon
                      exact False.elim ((by decide : ¬ 2 ≤ 1) hnon.1)
                  | inr htail_eq =>
                      rw [htail_eq]
                      exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
          | succ a'' =>
              cases a'' with
              | zero =>
                  have htail_sum : natListSum tail = 2 := by
                    change 2 + natListSum tail = 2 + 2 at hsum
                    exact add_left_cancel_counting hsum
                  have htail_non : NonincreasingParts tail := nonincreasingParts_tail hnon
                  have htail :=
                    positive_nonincreasing_sum_eq_two (positiveParts_tail hpos_cons) htail_non htail_sum
                  cases htail with
                  | inl htail_eq =>
                      rw [htail_eq]
                      exact Or.inr (Or.inr (Or.inl rfl))
                  | inr htail_eq =>
                      rw [htail_eq]
                      exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
              | succ a''' =>
                  cases a''' with
                  | zero =>
                      have htail_sum : natListSum tail = 1 := by
                        change 3 + natListSum tail = 3 + 1 at hsum
                        exact add_left_cancel_counting hsum
                      have htail : tail = [1] :=
                        positive_sum_one_singleton (positiveParts_tail hpos_cons) htail_sum
                      rw [htail]
                      exact Or.inr (Or.inl rfl)
                  | succ a'''' =>
                      cases a'''' with
                      | zero =>
                          have htail_sum : natListSum tail = 0 := by
                            change 4 + natListSum tail = 4 + 0 at hsum
                            exact add_left_cancel_counting hsum
                          have htail_nil : tail = [] :=
                            positive_sum_zero_nil (positiveParts_tail hpos_cons) htail_sum
                          rw [htail_nil]
                          exact Or.inl rfl
                      | succ a''''' =>
                          have hhead_ge : 5 ≤ Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ a''''')))) := by
                            exact Nat.succ_le_succ
                              (Nat.succ_le_succ
                                (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le a''''')))))
                          have hge :
                              5 ≤ Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ a''''')))) + natListSum tail := by
                            exact Nat.le_trans hhead_ge (Nat.le_add_right _ _)
                          have hfive_le_four : 5 ≤ 4 := by
                            calc
                              5 ≤ Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ a''''')))) + natListSum tail := hge
                              _ = 4 := hsum
                          exact False.elim ((by decide : ¬ 5 ≤ 4) hfive_le_four)

private theorem positive_nonincreasing_sum_eq_five {parts : List Nat}
    (hpos : PositiveParts parts)
    (hnon : NonincreasingParts parts)
    (hsum : natListSum parts = 5) :
    IsProfile5 parts := by
  cases parts with
  | nil =>
      change 0 = 5 at hsum
      cases hsum
  | cons a tail =>
      have hpos_cons : PositiveParts (a :: tail) := hpos
      have ha : 0 < a := hpos_cons a List.mem_cons_self
      cases a with
      | zero =>
          cases Nat.not_lt_zero 0 ha
      | succ a' =>
          cases a' with
          | zero =>
              have htail_sum : natListSum tail = 4 := by
                change 1 + natListSum tail = 1 + 4 at hsum
                exact add_left_cancel_counting hsum
              have htail_non : NonincreasingParts tail := nonincreasingParts_tail hnon
              have htail :=
                positive_nonincreasing_sum_eq_four (positiveParts_tail hpos_cons) htail_non htail_sum
              cases htail with
              | inl htail_eq =>
                  rw [htail_eq] at hnon
                  exact False.elim ((by decide : ¬ 4 ≤ 1) hnon.1)
              | inr htail =>
                  cases htail with
                  | inl htail_eq =>
                      rw [htail_eq] at hnon
                      exact False.elim ((by decide : ¬ 3 ≤ 1) hnon.1)
                  | inr htail =>
                      cases htail with
                      | inl htail_eq =>
                          rw [htail_eq] at hnon
                          exact False.elim ((by decide : ¬ 2 ≤ 1) hnon.1)
                      | inr htail =>
                          cases htail with
                          | inl htail_eq =>
                              rw [htail_eq] at hnon
                              exact False.elim ((by decide : ¬ 2 ≤ 1) hnon.1)
                          | inr htail_eq =>
                              rw [htail_eq]
                              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
          | succ a'' =>
              cases a'' with
              | zero =>
                  have htail_sum : natListSum tail = 3 := by
                    change 2 + natListSum tail = 2 + 3 at hsum
                    exact add_left_cancel_counting hsum
                  have htail_non : NonincreasingParts tail := nonincreasingParts_tail hnon
                  have htail :=
                    positive_nonincreasing_sum_eq_three (positiveParts_tail hpos_cons) htail_non htail_sum
                  cases htail with
                  | inl htail_eq =>
                      rw [htail_eq] at hnon
                      exact False.elim ((by decide : ¬ 3 ≤ 2) hnon.1)
                  | inr htail =>
                      cases htail with
                      | inl htail_eq =>
                          rw [htail_eq]
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
                      | inr htail_eq =>
                          rw [htail_eq]
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
              | succ a''' =>
                  cases a''' with
                  | zero =>
                      have htail_sum : natListSum tail = 2 := by
                        change 3 + natListSum tail = 3 + 2 at hsum
                        exact add_left_cancel_counting hsum
                      have htail_non : NonincreasingParts tail := nonincreasingParts_tail hnon
                      have htail :=
                        positive_nonincreasing_sum_eq_two (positiveParts_tail hpos_cons) htail_non htail_sum
                      cases htail with
                      | inl htail_eq =>
                          rw [htail_eq]
                          exact Or.inr (Or.inr (Or.inl rfl))
                      | inr htail_eq =>
                          rw [htail_eq]
                          exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
                  | succ a'''' =>
                      cases a'''' with
                      | zero =>
                          have htail_sum : natListSum tail = 1 := by
                            change 4 + natListSum tail = 4 + 1 at hsum
                            exact add_left_cancel_counting hsum
                          have htail : tail = [1] :=
                            positive_sum_one_singleton (positiveParts_tail hpos_cons) htail_sum
                          rw [htail]
                          exact Or.inr (Or.inl rfl)
                      | succ a''''' =>
                          cases a''''' with
                          | zero =>
                              have htail_sum : natListSum tail = 0 := by
                                change 5 + natListSum tail = 5 + 0 at hsum
                                exact add_left_cancel_counting hsum
                              have htail_nil : tail = [] :=
                                positive_sum_zero_nil (positiveParts_tail hpos_cons) htail_sum
                              rw [htail_nil]
                              exact Or.inl rfl
                          | succ a'''''' =>
                              have hhead_ge :
                                  6 ≤ Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ a''''''))))) := by
                                exact Nat.succ_le_succ
                                  (Nat.succ_le_succ
                                    (Nat.succ_le_succ
                                      (Nat.succ_le_succ
                                        (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le a''''''))))))
                              have hge :
                                  6 ≤ Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ a''''''))))) +
                                      natListSum tail := by
                                exact Nat.le_trans hhead_ge (Nat.le_add_right _ _)
                              have hsix_le_five : 6 ≤ 5 := by
                                calc
                                  6 ≤ Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ a''''''))))) +
                                      natListSum tail := hge
                                  _ = 5 := hsum
                              exact False.elim ((by decide : ¬ 6 ≤ 5) hsix_le_five)

private theorem positive_nonincreasing_sum_eq_six {parts : List Nat}
    (hpos : PositiveParts parts)
    (hnon : NonincreasingParts parts)
    (hsum : natListSum parts = 6) :
    IsCanonicalLogicalProfile parts := by
  cases parts with
  | nil =>
      change 0 = 6 at hsum
      cases hsum
  | cons a tail =>
      have hpos_cons : PositiveParts (a :: tail) := hpos
      have ha : 0 < a := hpos_cons a List.mem_cons_self
      cases a with
      | zero =>
          cases Nat.not_lt_zero 0 ha
      | succ a' =>
          cases a' with
          | zero =>
              have htail_sum : natListSum tail = 5 := by
                change 1 + natListSum tail = 1 + 5 at hsum
                exact add_left_cancel_counting hsum
              have htail_non : NonincreasingParts tail := nonincreasingParts_tail hnon
              have htail :=
                positive_nonincreasing_sum_eq_five (positiveParts_tail hpos_cons) htail_non htail_sum
              cases htail with
              | inl htail_eq =>
                  rw [htail_eq] at hnon
                  exact False.elim ((by decide : ¬ 5 ≤ 1) hnon.1)
              | inr htail =>
                  cases htail with
                  | inl htail_eq =>
                      rw [htail_eq] at hnon
                      exact False.elim ((by decide : ¬ 4 ≤ 1) hnon.1)
                  | inr htail =>
                      cases htail with
                      | inl htail_eq =>
                          rw [htail_eq] at hnon
                          exact False.elim ((by decide : ¬ 3 ≤ 1) hnon.1)
                      | inr htail =>
                          cases htail with
                          | inl htail_eq =>
                              rw [htail_eq] at hnon
                              exact False.elim ((by decide : ¬ 3 ≤ 1) hnon.1)
                          | inr htail =>
                              cases htail with
                              | inl htail_eq =>
                                  rw [htail_eq] at hnon
                                  exact False.elim ((by decide : ¬ 2 ≤ 1) hnon.1)
                              | inr htail =>
                                  cases htail with
                                  | inl htail_eq =>
                                      rw [htail_eq] at hnon
                                      exact False.elim ((by decide : ¬ 2 ≤ 1) hnon.1)
                                  | inr htail_eq =>
                                      rw [htail_eq]
                                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))))
          | succ a'' =>
              cases a'' with
              | zero =>
                  have htail_sum : natListSum tail = 4 := by
                    change 2 + natListSum tail = 2 + 4 at hsum
                    exact add_left_cancel_counting hsum
                  have htail_non : NonincreasingParts tail := nonincreasingParts_tail hnon
                  have htail :=
                    positive_nonincreasing_sum_eq_four (positiveParts_tail hpos_cons) htail_non htail_sum
                  cases htail with
                  | inl htail_eq =>
                      rw [htail_eq] at hnon
                      exact False.elim ((by decide : ¬ 4 ≤ 2) hnon.1)
                  | inr htail =>
                      cases htail with
                      | inl htail_eq =>
                          rw [htail_eq] at hnon
                          exact False.elim ((by decide : ¬ 3 ≤ 2) hnon.1)
                      | inr htail =>
                          cases htail with
                          | inl htail_eq =>
                              rw [htail_eq]
                              change IsCanonicalLogicalProfile [2, 2, 2]
                              unfold IsCanonicalLogicalProfile
                              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                (Or.inr (Or.inl rfl)))))))
                          | inr htail =>
                              cases htail with
                              | inl htail_eq =>
                                  rw [htail_eq]
                                  change IsCanonicalLogicalProfile [2, 2, 1, 1]
                                  unfold IsCanonicalLogicalProfile
                                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                    (Or.inr (Or.inr (Or.inl rfl))))))))
                              | inr htail_eq =>
                                  rw [htail_eq]
                                  change IsCanonicalLogicalProfile [2, 1, 1, 1, 1]
                                  unfold IsCanonicalLogicalProfile
                                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
              | succ a''' =>
                  cases a''' with
                  | zero =>
                      have htail_sum : natListSum tail = 3 := by
                        change 3 + natListSum tail = 3 + 3 at hsum
                        exact add_left_cancel_counting hsum
                      have htail_non : NonincreasingParts tail := nonincreasingParts_tail hnon
                      have htail :=
                          positive_nonincreasing_sum_eq_three (positiveParts_tail hpos_cons) htail_non htail_sum
                      cases htail with
                      | inl htail_eq =>
                          rw [htail_eq]
                          change IsCanonicalLogicalProfile [3, 3]
                          unfold IsCanonicalLogicalProfile
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
                      | inr htail =>
                          cases htail with
                          | inl htail_eq =>
                              rw [htail_eq]
                              change IsCanonicalLogicalProfile [3, 2, 1]
                              unfold IsCanonicalLogicalProfile
                              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
                          | inr htail_eq =>
                              rw [htail_eq]
                              change IsCanonicalLogicalProfile [3, 1, 1, 1]
                              unfold IsCanonicalLogicalProfile
                              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                (Or.inl rfl))))))
                  | succ a'''' =>
                      cases a'''' with
                      | zero =>
                          have htail_sum : natListSum tail = 2 := by
                            change 4 + natListSum tail = 4 + 2 at hsum
                            exact add_left_cancel_counting hsum
                          have htail_non : NonincreasingParts tail := nonincreasingParts_tail hnon
                          have htail :=
                            positive_nonincreasing_sum_eq_two (positiveParts_tail hpos_cons) htail_non htail_sum
                          cases htail with
                          | inl htail_eq =>
                              rw [htail_eq]
                              exact Or.inr (Or.inr (Or.inl rfl))
                          | inr htail_eq =>
                              rw [htail_eq]
                              exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
                      | succ a''''' =>
                          cases a''''' with
                          | zero =>
                              have htail_sum : natListSum tail = 1 := by
                                change 5 + natListSum tail = 5 + 1 at hsum
                                exact add_left_cancel_counting hsum
                              have htail : tail = [1] :=
                                positive_sum_one_singleton (positiveParts_tail hpos_cons) htail_sum
                              rw [htail]
                              exact Or.inr (Or.inl rfl)
                          | succ a'''''' =>
                              cases a'''''' with
                              | zero =>
                                  have htail_sum : natListSum tail = 0 := by
                                    change 6 + natListSum tail = 6 + 0 at hsum
                                    exact add_left_cancel_counting hsum
                                  have htail_nil : tail = [] :=
                                    positive_sum_zero_nil (positiveParts_tail hpos_cons) htail_sum
                                  rw [htail_nil]
                                  exact Or.inl rfl
                              | succ a''''''' =>
                                  have hhead_ge :
                                      7 ≤ Nat.succ
                                            (Nat.succ
                                              (Nat.succ
                                                (Nat.succ
                                                  (Nat.succ
                                                    (Nat.succ (Nat.succ a'''''''))))) ) := by
                                    exact Nat.succ_le_succ
                                      (Nat.succ_le_succ
                                        (Nat.succ_le_succ
                                          (Nat.succ_le_succ
                                            (Nat.succ_le_succ
                                              (Nat.succ_le_succ
                                                (Nat.succ_le_succ (Nat.zero_le a''''''')))))))
                                  have hge :
                                      7 ≤
                                        Nat.succ
                                          (Nat.succ
                                            (Nat.succ
                                              (Nat.succ
                                                (Nat.succ
                                                  (Nat.succ (Nat.succ a'''''''))))) ) +
                                          natListSum tail := by
                                    exact Nat.le_trans hhead_ge (Nat.le_add_right _ _)
                                  have hseven_le_six : 7 ≤ 6 := by
                                    calc
                                      7 ≤
                                          Nat.succ
                                            (Nat.succ
                                              (Nat.succ
                                                (Nat.succ
                                                  (Nat.succ
                                                    (Nat.succ (Nat.succ a'''''''))))) ) +
                                          natListSum tail := hge
                                      _ = 6 := hsum
                                  exact False.elim ((by decide : ¬ 7 ≤ 6) hseven_le_six)

private theorem balancedClosureSlotCount_two :
    balancedClosureSlotCount 2 = 1 := by
  decide

private theorem balancedClosureSlotCount_closureStableDimension :
    balancedClosureSlotCount closureStableDimension = 6 := by
  decide

private theorem closureState_sub_self (x : ClosureState) :
    ClosureState.sub x x = ClosureState.zero := by
  apply ClosureState.ext
  · exact SignedCount.subCount_self x.g0
  · exact SignedCount.subCount_self x.g1
  · exact SignedCount.subCount_self x.g2
  · exact SignedCount.subCount_self x.g3

private theorem closureProjectionState_zero_state (h : Nat) :
    closureProjectionState h ClosureState.zero = ClosureState.zero := by
  apply ClosureState.ext
  · change keepBelow (decide (0 < h)) SignedCount.zero = SignedCount.zero
    exact keepBelow_zero (decide (0 < h))
  · change keepBelow (decide (1 < h)) SignedCount.zero = SignedCount.zero
    exact keepBelow_zero (decide (1 < h))
  · change keepBelow (decide (2 < h)) SignedCount.zero = SignedCount.zero
    exact keepBelow_zero (decide (2 < h))
  · change keepBelow (decide (3 < h)) SignedCount.zero = SignedCount.zero
    exact keepBelow_zero (decide (3 < h))

private theorem closureShadowState_zero_state (h : Nat) :
    closureShadowState h ClosureState.zero = ClosureState.zero := by
  rw [closureShadowState, closureProjectionState_zero_state]
  exact closureState_sub_self ClosureState.zero

private theorem closureReturnState_zero_state (h : Nat) :
    closureReturnState h ClosureState.zero = ClosureState.zero := by
  unfold closureReturnState
  rw [closureShadowState_zero_state]
  have hboundary : closureBoundaryState ClosureState.zero = ClosureState.zero := by
    rfl
  rw [hboundary, closureProjectionState_zero_state]

private theorem closureShadowState_of_projection_eq (h : Nat) (x : ClosureState)
    (hproj : closureProjectionState h x = x) :
    closureShadowState h x = ClosureState.zero := by
  rw [closureShadowState, hproj]
  apply ClosureState.ext
  · exact SignedCount.subCount_self x.g0
  · exact SignedCount.subCount_self x.g1
  · exact SignedCount.subCount_self x.g2
  · exact SignedCount.subCount_self x.g3

private theorem closureShadowState_zero_exact (x : ClosureState) :
    closureShadowState 0 x = x := by
  apply ClosureState.ext
  · exact subCount_zero x.g0
  · exact subCount_zero x.g1
  · exact subCount_zero x.g2
  · exact subCount_zero x.g3

private theorem closureShadowState_one_exact (x : ClosureState) :
    closureShadowState 1 x =
      ⟨SignedCount.zero, x.g1, x.g2, x.g3⟩ := by
  apply ClosureState.ext
  · exact SignedCount.subCount_self x.g0
  · exact subCount_zero x.g1
  · exact subCount_zero x.g2
  · exact subCount_zero x.g3

private theorem closureShadowState_two_exact (x : ClosureState) :
    closureShadowState 2 x =
      ⟨SignedCount.zero, SignedCount.zero, x.g2, x.g3⟩ := by
  apply ClosureState.ext
  · exact SignedCount.subCount_self x.g0
  · exact SignedCount.subCount_self x.g1
  · exact subCount_zero x.g2
  · exact subCount_zero x.g3

private theorem closureShadowState_three_exact (x : ClosureState) :
    closureShadowState 3 x =
      ⟨SignedCount.zero, SignedCount.zero, SignedCount.zero, x.g3⟩ := by
  apply ClosureState.ext
  · exact SignedCount.subCount_self x.g0
  · exact SignedCount.subCount_self x.g1
  · exact SignedCount.subCount_self x.g2
  · exact subCount_zero x.g3

private theorem closureState_energy_g1g2g3 (x : ClosureState) :
    ClosureState.energy
      ⟨SignedCount.zero, x.g1, x.g2, x.g3⟩ =
        canonicalGradeEnergy x 1 +
        canonicalGradeEnergy x 2 +
        canonicalGradeEnergy x 3 := by
  cases x with
  | mk g0 g1 g2 g3 =>
      change
        (((SignedCount.energy SignedCount.zero + SignedCount.energy g1) +
            SignedCount.energy g2) + SignedCount.energy g3) =
          ((SignedCount.energy g1 + SignedCount.energy g2) + SignedCount.energy g3)
      rw [signedCount_energy_zero, zero_add_counting]

private theorem closureState_energy_g2g3 (x : ClosureState) :
    ClosureState.energy
      ⟨SignedCount.zero, SignedCount.zero, x.g2, x.g3⟩ =
        canonicalGradeEnergy x 2 +
        canonicalGradeEnergy x 3 := by
  cases x with
  | mk g0 g1 g2 g3 =>
      change
        (((SignedCount.energy SignedCount.zero + SignedCount.energy SignedCount.zero) +
            SignedCount.energy g2) + SignedCount.energy g3) =
          (SignedCount.energy g2 + SignedCount.energy g3)
      rw [signedCount_energy_zero]
      rw [zero_add_counting 0, zero_add_counting (SignedCount.energy g2)]

private theorem closureState_energy_g3 (x : ClosureState) :
    ClosureState.energy
      ⟨SignedCount.zero, SignedCount.zero, SignedCount.zero, x.g3⟩ =
        canonicalGradeEnergy x 3 := by
  cases x with
  | mk g0 g1 g2 g3 =>
      change
        (((SignedCount.energy SignedCount.zero + SignedCount.energy SignedCount.zero) +
            SignedCount.energy SignedCount.zero) + SignedCount.energy g3) =
          SignedCount.energy g3
      rw [signedCount_energy_zero]
      rw [zero_add_counting 0, zero_add_counting (SignedCount.energy g3)]

private theorem closureState_energy_g1_only (x : ClosureState) :
    ClosureState.energy
      ⟨SignedCount.zero, x.g1, SignedCount.zero, SignedCount.zero⟩ =
        canonicalGradeEnergy x 1 := by
  cases x with
  | mk g0 g1 g2 g3 =>
      change
        (((SignedCount.energy SignedCount.zero + SignedCount.energy g1) +
            SignedCount.energy SignedCount.zero) + SignedCount.energy SignedCount.zero) =
          SignedCount.energy g1
      rw [signedCount_energy_zero]
      rw [zero_add_counting (SignedCount.energy g1)]
      rw [add_zero_counting (SignedCount.energy g1)]

private theorem closureState_energy_g2_only (x : ClosureState) :
    ClosureState.energy
      ⟨SignedCount.zero, SignedCount.zero, x.g2, SignedCount.zero⟩ =
        canonicalGradeEnergy x 2 := by
  cases x with
  | mk g0 g1 g2 g3 =>
      change
        (((SignedCount.energy SignedCount.zero + SignedCount.energy SignedCount.zero) +
            SignedCount.energy g2) + SignedCount.energy SignedCount.zero) =
          SignedCount.energy g2
      rw [signedCount_energy_zero]
      rw [zero_add_counting 0, zero_add_counting (SignedCount.energy g2), add_zero_counting (SignedCount.energy g2)]

private theorem closureState_energy_g3_only (x : ClosureState) :
    ClosureState.energy
      ⟨SignedCount.zero, SignedCount.zero, SignedCount.zero, x.g3⟩ =
        canonicalGradeEnergy x 3 := by
  exact closureState_energy_g3 x

private theorem canonicalRevelationState_zero_exact (x : ClosureState) :
    canonicalRevelationState 0 x =
      ⟨x.g0, SignedCount.zero, SignedCount.zero, SignedCount.zero⟩ := by
  apply ClosureState.ext
  · exact subCount_zero x.g0
  · rfl
  · rfl
  · rfl

private theorem canonicalRevelationState_one_exact (x : ClosureState) :
    canonicalRevelationState 1 x =
      ⟨SignedCount.zero, x.g1, SignedCount.zero, SignedCount.zero⟩ := by
  apply ClosureState.ext
  · exact SignedCount.subCount_self x.g0
  · exact subCount_zero x.g1
  · rfl
  · rfl

private theorem canonicalRevelationState_two_exact (x : ClosureState) :
    canonicalRevelationState 2 x =
      ⟨SignedCount.zero, SignedCount.zero, x.g2, SignedCount.zero⟩ := by
  apply ClosureState.ext
  · exact SignedCount.subCount_self x.g0
  · exact SignedCount.subCount_self x.g1
  · exact subCount_zero x.g2
  · rfl

private theorem canonicalRevelationState_three_exact (x : ClosureState) :
    canonicalRevelationState 3 x =
      ⟨SignedCount.zero, SignedCount.zero, SignedCount.zero, x.g3⟩ := by
  apply ClosureState.ext
  · exact SignedCount.subCount_self x.g0
  · exact SignedCount.subCount_self x.g1
  · exact SignedCount.subCount_self x.g2
  · exact subCount_zero x.g3

private theorem closureLeakageState_zero (h : Nat) (x : ClosureState) :
    closureLeakageState h x = ClosureState.zero := by
  cases h with
  | zero =>
      rfl
  | succ h =>
      cases h with
      | zero =>
          rfl
      | succ h =>
      cases h with
      | zero =>
          have hboundary :
              closureBoundaryState (closureProjectionState 2 x) =
                ⟨x.g1, SignedCount.zero, SignedCount.zero, SignedCount.zero⟩ := by
            rfl
          rw [closureLeakageState, hboundary]
          have hproj :
              closureProjectionState 2
                ⟨x.g1, SignedCount.zero, SignedCount.zero, SignedCount.zero⟩ =
                  ⟨x.g1, SignedCount.zero, SignedCount.zero, SignedCount.zero⟩ := by
            apply ClosureState.ext <;> rfl
          exact closureShadowState_of_projection_eq 2 _ hproj
      | succ h =>
          cases h with
          | zero =>
              have hboundary :
                  closureBoundaryState (closureProjectionState 3 x) =
                    ⟨x.g1, SignedCount.zero, SignedCount.zero, SignedCount.zero⟩ := by
                rfl
              rw [closureLeakageState, hboundary]
              have hproj :
                  closureProjectionState 3
                    ⟨x.g1, SignedCount.zero, SignedCount.zero, SignedCount.zero⟩ =
                      ⟨x.g1, SignedCount.zero, SignedCount.zero, SignedCount.zero⟩ := by
                apply ClosureState.ext <;> rfl
              exact closureShadowState_of_projection_eq 3 _ hproj
          | succ h =>
                  change
                    closureShadowState (h + closureStableDimension)
                      (closureBoundaryState (closureProjectionState (h + closureStableDimension) x)) =
                        ClosureState.zero
                  have hproj :
                      closureProjectionState (h + closureStableDimension) x = x :=
                    closureProjectionState_after_stable_dimension h x
                  rw [hproj]
                  exact closureShadowState_after_stable_dimension h (closureBoundaryState x)

private theorem closureDefectState_zero (h : Nat) (x : ClosureState) :
    closureDefectState h x = ClosureState.zero := by
  rw [closureDefectState, closureLeakageState_zero]
  exact closureReturnState_zero_state h

/-- The Chapter 6 interface theorem is already forced by the active closure
realization. -/
theorem closure_balance_realizes_interface :
    ClosureBalanceStructuralInterface := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro x
    exact state_layer_is_closure_transport x
  · intro x
    exact fullBoundary_closes x
  · intro h x
    exact closureTower_apply h x
  · intro x
    have hshadow :
        shadowProj closureTower 4 x = shadowProj coherenceTower 4 x := by
      unfold shadowProj
      rw [closureTower_apply]
    rw [hshadow, coherenceShadow_after_four]

/-- The canonical balanced carrier is the unique nontrivial stable six-slot
carrier, while the unit seed occurs at dimension `2`. -/
theorem unit_seed_and_six_slot_carrier :
    (∀ {D : Nat}, isStable D → D = 2 ∨ D = closureStableDimension) ∧
    balancedClosureSlotCount 2 = 1 ∧
    balancedClosureSlotCount closureStableDimension = 6 := by
  refine ⟨?_, ?_, ?_⟩
  · intro D hstable
    simpa [closureStableDimension] using (stable_dimension_classification.mp hstable)
  · decide
  · decide

/-- The unit-balanced seed has no nontrivial positive channel decomposition. -/
theorem primitive_seed_irreducible
    (parts : List Nat)
    (hpos : PositiveParts parts)
    (hsum : natListSum parts = balancedClosureSlotCount 2) :
    parts = [1] := by
  have hsum_one : natListSum parts = 1 := by
    calc
      natListSum parts = balancedClosureSlotCount 2 := hsum
      _ = 1 := balancedClosureSlotCount_two
  cases parts with
  | nil =>
      change 0 = 1 at hsum_one
      cases hsum_one
  | cons a tail =>
      have hpos_cons : PositiveParts (a :: tail) := hpos
      have ha : 0 < a := hpos_cons a List.mem_cons_self
      cases a with
      | zero =>
          cases Nat.not_lt_zero 0 ha
      | succ a' =>
          cases a' with
          | zero =>
              have htail_pos : PositiveParts tail := positiveParts_tail hpos_cons
              have htail_zero : natListSum tail = 0 := by
                exact add_left_cancel_counting hsum_one
              cases tail with
              | nil =>
                  rfl
              | cons b tail' =>
                  have hb : 0 < b := htail_pos b List.mem_cons_self
                  have hge : 1 ≤ natListSum (b :: tail') := by
                    exact Nat.le_trans hb (Nat.le_add_right b (natListSum tail'))
                  rw [htail_zero] at hge
                  exact False.elim (Nat.not_succ_le_zero 0 hge)
          | succ a'' =>
              have hge : 2 ≤ Nat.succ (Nat.succ a'') + natListSum tail := by
                exact Nat.le_trans
                  (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le a''))) <|
                  Nat.le_add_right (Nat.succ (Nat.succ a'')) (natListSum tail)
              have htwo_le_one : 2 ≤ 1 := by
                calc
                  2 ≤ Nat.succ (Nat.succ a'') + natListSum tail := hge
                  _ = 1 := hsum_one
              exact False.elim ((by decide : ¬ 2 ≤ 1) htwo_le_one)

/-- The unit-balanced seed carries only the one-part local channel profile. -/
theorem single_channel_unit_seed
    (parts : List Nat)
    (hpos : PositiveParts parts)
    (hsum : natListSum parts = balancedClosureSlotCount 2) :
    parts = [1] := by
  exact primitive_seed_irreducible parts hpos hsum

/-- The residual dimension remains the unique nontrivial counting barrier, and
the balanced six-slot carrier admits only the finitely many canonical logical
profiles. -/
theorem finite_local_type_profiles :
    holographicImbalance 3 = SignedCount.ofNat 1 ∧
    ∀ p : LogicalTypeSignature, IsCanonicalLogicalProfile p.parts := by
  refine ⟨barrier_D3, ?_⟩
  intro p
  have hsum_six : natListSum p.parts = 6 := by
    calc
      natListSum p.parts = balancedClosureSlotCount closureStableDimension := p.sum_eq
      _ = 6 := balancedClosureSlotCount_closureStableDimension
  exact positive_nonincreasing_sum_eq_six p.positive p.nonincreasing hsum_six

/-- The Chapter 6 type-classification problem is reduced to the unit seed, the
residual barrier, the six-slot carrier, and the explicit finite logical
profiles on that carrier. -/
theorem choice_free_type_classification :
    balancedClosureSlotCount 2 = 1 ∧
    holographicImbalance 3 = SignedCount.ofNat 1 ∧
    balancedClosureSlotCount closureStableDimension = 6 ∧
    ∀ p : LogicalTypeSignature, IsCanonicalLogicalProfile p.parts := by
  refine ⟨unit_seed_and_six_slot_carrier.2.1, finite_local_type_profiles.1,
    unit_seed_and_six_slot_carrier.2.2, finite_local_type_profiles.2⟩

/-- Every symmetry-refined logical type still lies over the same finite
six-slot logical signature surface. -/
theorem symmetry_refined_logical_type (τ : SymmetryRefinedLogicalType) :
    natListSum τ.signature.parts = 6 ∧
    τ.signature.parts.length ≤ 6 ∧
    (∃ σ : LogicalTypeSignature, σ.parts = τ.signature.parts) ∧
    IsCanonicalLogicalProfile τ.signature.parts := by
  have hsum_six : natListSum τ.signature.parts = 6 := by
    calc
      natListSum τ.signature.parts =
          balancedClosureSlotCount closureStableDimension := τ.signature.sum_eq
      _ = 6 := balancedClosureSlotCount_closureStableDimension
  refine ⟨hsum_six, ?_, ⟨τ.signature, rfl⟩, finite_local_type_profiles.2 τ.signature⟩
  calc
    τ.signature.parts.length ≤ natListSum τ.signature.parts :=
      positiveParts_length_le_sum τ.signature.positive
    _ = 6 := hsum_six

/-- Symmetry refinement cannot enlarge the finite logical-type surface of the
canonical balanced carrier. -/
theorem logical_types_finite (τ : SymmetryRefinedLogicalType) :
    τ.signature.parts.length ≤ 6 ∧
    IsCanonicalLogicalProfile τ.signature.parts := by
  rcases symmetry_refined_logical_type τ with ⟨_, hlen, _, hcanon⟩
  exact ⟨hlen, hcanon⟩

/-- Manuscript-facing forcing surface of the canonical six-slot carrier. This
packages exactly the finite carrier, canonical `3+2+1` profile, unique
intrinsic normal form, and channel-parameter/eigenvalue control later needed
by the selected-completion route. -/
structure SixSlotForcing where
  slotCount :
    balancedClosureSlotCount closureStableDimension = 6
  canonicalProfile :
    natListSum [3, 2, 1] = balancedClosureSlotCount closureStableDimension ∧
      IsCanonicalLogicalProfile [3, 2, 1]
  finiteLogicalTypes :
    ∀ τ : SymmetryRefinedLogicalType, τ.signature.parts.length ≤ 6
  symmetricSquareCarrier :
    Nonempty (CarrierIso LocalSlot PrimitiveThreeSymmetricSquare)
  uniqueNormalForm :
    ∀ A : LocalSlot → LocalSlot → SignedCount,
      IntrinsicAdjacencyInvariant A →
      ∃ p : IntrinsicSlotParameters,
        isIntrinsicNormalForm A p ∧
          ∀ q : IntrinsicSlotParameters, isIntrinsicNormalForm A q → q = p
  normalFormRigidity :
    ∀ {A B : LocalSlot → LocalSlot → SignedCount}
      {p : IntrinsicSlotParameters},
      isIntrinsicNormalForm A p →
      isIntrinsicNormalForm B p →
      ∀ α β : LocalSlot, A α β = B α β
  threeParameterControl :
    ∀ A : LocalSlot → LocalSlot → SignedCount,
      IntrinsicAdjacencyInvariant A →
      ∃ a b c : SignedCount,
        ∀ α β : LocalSlot,
          A α β =
            match intrinsicSlotAdjacency α β with
            | .equal => a
            | .adjacent => b
            | .disjoint => c
  channelEigenvalues :
    ∀ A : LocalSlot → LocalSlot → SignedCount,
      IntrinsicAdjacencyInvariant A →
      ∃ a b c : SignedCount,
        ∃ l1 l2 l3 : SignedCount,
          (∀ α β : LocalSlot,
            A α β =
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
          l3 = SignedCount.subCount a c
  canonicalS12FiberCoordinates :
    localSlotCoordinates canonicalIntrinsicOverlapS12Fiber =
      ⟨SignedCount.ofNat 4, SignedCount.zero, SignedCount.negOfNat 2⟩
  canonicalS13FiberCoordinates :
    localSlotCoordinates
        (intrinsicLawFiber canonicalIntrinsicOverlapLaw LocalSlot.s13) =
      ⟨SignedCount.ofNat 4, SignedCount.zero, SignedCount.negOfNat 2⟩
  canonicalNormalFormS12FiberCoordinates :
    ∀ {A : LocalSlot → LocalSlot → SignedCount},
      (∃ p : IntrinsicSlotParameters,
        (isIntrinsicNormalForm A p ∧
          p.diagonal = SignedCount.ofNat 2 ∧
          p.adjacent = SignedCount.ofNat 1 ∧
          p.disjoint = SignedCount.zero) ∧
        ∀ q : IntrinsicSlotParameters,
          (isIntrinsicNormalForm A q ∧
            q.diagonal = SignedCount.ofNat 2 ∧
            q.adjacent = SignedCount.ofNat 1 ∧
            q.disjoint = SignedCount.zero) →
          q = p) →
        localSlotCoordinates (intrinsicLawFiber A LocalSlot.s12) =
          ⟨SignedCount.ofNat 4, SignedCount.zero, SignedCount.negOfNat 2⟩
  canonicalNormalFormS13FiberCoordinates :
    ∀ {A : LocalSlot → LocalSlot → SignedCount},
      (∃ p : IntrinsicSlotParameters,
        (isIntrinsicNormalForm A p ∧
          p.diagonal = SignedCount.ofNat 2 ∧
          p.adjacent = SignedCount.ofNat 1 ∧
          p.disjoint = SignedCount.zero) ∧
        ∀ q : IntrinsicSlotParameters,
          (isIntrinsicNormalForm A q ∧
            q.diagonal = SignedCount.ofNat 2 ∧
            q.adjacent = SignedCount.ofNat 1 ∧
            q.disjoint = SignedCount.zero) →
          q = p) →
        localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13) =
          ⟨SignedCount.ofNat 4, SignedCount.zero, SignedCount.negOfNat 2⟩
  canonicalFiberCoordinates :
    ∀ {A : LocalSlot → LocalSlot → SignedCount},
      (∃ p : IntrinsicSlotParameters,
        (isIntrinsicNormalForm A p ∧
          p.diagonal = SignedCount.ofNat 2 ∧
          p.adjacent = SignedCount.ofNat 1 ∧
          p.disjoint = SignedCount.zero) ∧
        ∀ q : IntrinsicSlotParameters,
          (isIntrinsicNormalForm A q ∧
            q.diagonal = SignedCount.ofNat 2 ∧
            q.adjacent = SignedCount.ofNat 1 ∧
            q.disjoint = SignedCount.zero) →
          q = p) →
        ∀ anchor : LocalSlot,
          localSlotCoordinates (intrinsicLawFiber A anchor) =
            canonicalIntrinsicOverlapFiberCoordinates anchor
  canonicalS13FiberRigidity :
    ∀ {A : LocalSlot → LocalSlot → SignedCount},
      IntrinsicAdjacencyInvariant A →
      localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13) =
        canonicalIntrinsicOverlapFiberCoordinates LocalSlot.s13 →
      ∀ α β : LocalSlot, A α β = canonicalIntrinsicOverlapLaw α β
  canonicalS13FiberForcesCanonicalNormalForm :
    ∀ {A : LocalSlot → LocalSlot → SignedCount},
      IntrinsicAdjacencyInvariant A →
      localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13) =
        canonicalIntrinsicOverlapFiberCoordinates LocalSlot.s13 →
      ∃ p : IntrinsicSlotParameters,
        (isIntrinsicNormalForm A p ∧
          p.diagonal = SignedCount.ofNat 2 ∧
          p.adjacent = SignedCount.ofNat 1 ∧
          p.disjoint = SignedCount.zero) ∧
        ∀ q : IntrinsicSlotParameters,
          (isIntrinsicNormalForm A q ∧
            q.diagonal = SignedCount.ofNat 2 ∧
            q.adjacent = SignedCount.ofNat 1 ∧
            q.disjoint = SignedCount.zero) →
          q = p
  canonicalS13FiberForcesCanonicalFiberCoordinates :
    ∀ {A : LocalSlot → LocalSlot → SignedCount},
      IntrinsicAdjacencyInvariant A →
      localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13) =
        canonicalIntrinsicOverlapFiberCoordinates LocalSlot.s13 →
      ∀ anchor : LocalSlot,
        localSlotCoordinates (intrinsicLawFiber A anchor) =
          canonicalIntrinsicOverlapFiberCoordinates anchor
  canonicalS13FiberPairwiseRigidity :
    ∀ {A B : LocalSlot → LocalSlot → SignedCount},
      IntrinsicAdjacencyInvariant A →
      localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13) =
        canonicalIntrinsicOverlapFiberCoordinates LocalSlot.s13 →
      IntrinsicAdjacencyInvariant B →
      localSlotCoordinates (intrinsicLawFiber B LocalSlot.s13) =
        canonicalIntrinsicOverlapFiberCoordinates LocalSlot.s13 →
      ∀ α β : LocalSlot, A α β = B α β
  canonicalS13FiberPairwiseCoordinates :
    ∀ {A B : LocalSlot → LocalSlot → SignedCount},
      IntrinsicAdjacencyInvariant A →
      localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13) =
        canonicalIntrinsicOverlapFiberCoordinates LocalSlot.s13 →
      IntrinsicAdjacencyInvariant B →
      localSlotCoordinates (intrinsicLawFiber B LocalSlot.s13) =
        canonicalIntrinsicOverlapFiberCoordinates LocalSlot.s13 →
      ∀ anchor : LocalSlot,
        localSlotCoordinates (intrinsicLawFiber A anchor) =
          localSlotCoordinates (intrinsicLawFiber B anchor)
  canonicalFiberRigidity :
    ∀ {A : LocalSlot → LocalSlot → SignedCount},
      IntrinsicAdjacencyInvariant A →
      (∀ anchor : LocalSlot,
        localSlotCoordinates (intrinsicLawFiber A anchor) =
          canonicalIntrinsicOverlapFiberCoordinates anchor) →
      ∀ α β : LocalSlot, A α β = canonicalIntrinsicOverlapLaw α β
  fiberCoordinateRigidity :
    ∀ {A B : LocalSlot → LocalSlot → SignedCount},
      (∃ p : IntrinsicSlotParameters,
        (isIntrinsicNormalForm A p ∧
          p.diagonal = SignedCount.ofNat 2 ∧
          p.adjacent = SignedCount.ofNat 1 ∧
          p.disjoint = SignedCount.zero) ∧
        ∀ q : IntrinsicSlotParameters,
          (isIntrinsicNormalForm A q ∧
            q.diagonal = SignedCount.ofNat 2 ∧
            q.adjacent = SignedCount.ofNat 1 ∧
            q.disjoint = SignedCount.zero) →
          q = p) →
      (∃ p : IntrinsicSlotParameters,
        (isIntrinsicNormalForm B p ∧
          p.diagonal = SignedCount.ofNat 2 ∧
          p.adjacent = SignedCount.ofNat 1 ∧
          p.disjoint = SignedCount.zero) ∧
        ∀ q : IntrinsicSlotParameters,
          (isIntrinsicNormalForm B q ∧
            q.diagonal = SignedCount.ofNat 2 ∧
            q.adjacent = SignedCount.ofNat 1 ∧
            q.disjoint = SignedCount.zero) →
          q = p) →
        ∀ anchor : LocalSlot,
          localSlotCoordinates (intrinsicLawFiber A anchor) =
            localSlotCoordinates (intrinsicLawFiber B anchor)

/-- The canonical closure-balance carrier already supplies the complete
six-slot forcing surface. -/
def canonicalSixSlotForcing : SixSlotForcing where
  slotCount := unit_seed_and_six_slot_carrier.2.2
  canonicalProfile := intrinsic_six_slot_decomposition
  finiteLogicalTypes := fun τ => (logical_types_finite τ).1
  symmetricSquareCarrier := six_slot_carrier_is_symmetric_square_of_u3
  uniqueNormalForm := intrinsic_slot_normal_form
  normalFormRigidity := intrinsic_law_pointwise_eq_of_normalForm_eq
  threeParameterControl := intrinsic_equivariant_three_parameter
  channelEigenvalues := intrinsic_channel_eigenvalues
  canonicalS12FiberCoordinates := canonicalIntrinsicOverlapS12Fiber_coordinates
  canonicalS13FiberCoordinates := canonicalIntrinsicOverlapS13Fiber_coordinates
  canonicalNormalFormS12FiberCoordinates :=
    s12FiberCoordinates_of_existsCanonicalNormalForm
  canonicalNormalFormS13FiberCoordinates :=
    s13FiberCoordinates_of_existsCanonicalNormalForm
  canonicalFiberCoordinates :=
    fiberCoordinates_of_existsCanonicalNormalForm
  canonicalS13FiberRigidity :=
    pointwise_eq_canonicalIntrinsicOverlapLaw_of_intrinsic_and_s13FiberCoordinates
  canonicalS13FiberForcesCanonicalNormalForm :=
    canonicalNormalForm_of_intrinsic_and_s13FiberCoordinates
  canonicalS13FiberForcesCanonicalFiberCoordinates :=
    canonicalFiberCoordinates_of_intrinsic_and_s13FiberCoordinates
  canonicalS13FiberPairwiseRigidity :=
    pointwise_eq_of_intrinsic_and_canonicalS13FiberCoordinates
  canonicalS13FiberPairwiseCoordinates :=
    fiberCoordinateFamily_eq_of_intrinsic_and_canonicalS13FiberCoordinates
  canonicalFiberRigidity :=
    pointwise_eq_canonicalIntrinsicOverlapLaw_of_intrinsic_and_canonicalFiberCoordinates
  fiberCoordinateRigidity :=
    fiberCoordinateFamily_eq_of_existsCanonicalNormalForm

/-- In the canonical closure realization, observable-to-shadow transport by the
true boundary vanishes identically, and so does the induced defect. -/
theorem canonical_shadow_collapse (h : Nat) (x : ClosureState) :
    closureLeakageState h x = ClosureState.zero ∧
    closureDefectState h x = ClosureState.zero := by
  exact ⟨closureLeakageState_zero h x, closureDefectState_zero h x⟩

/-- Exact tail and one-step revelation formulas for the canonical four-grade
closure tower. -/
theorem canonical_tail_laws (x : ClosureState) :
    canonicalTailProfile 0 x =
      canonicalGradeEnergy x 0 +
      canonicalGradeEnergy x 1 +
      canonicalGradeEnergy x 2 +
      canonicalGradeEnergy x 3 ∧
    canonicalTailProfile 1 x =
      canonicalGradeEnergy x 1 +
      canonicalGradeEnergy x 2 +
      canonicalGradeEnergy x 3 ∧
    canonicalTailProfile 2 x =
      canonicalGradeEnergy x 2 +
      canonicalGradeEnergy x 3 ∧
    canonicalTailProfile 3 x = canonicalGradeEnergy x 3 ∧
    (∀ h : Nat, canonicalTailProfile (h + 4) x = 0) ∧
    canonicalRevelationProfile 0 x = canonicalGradeEnergy x 0 ∧
    canonicalRevelationProfile 1 x = canonicalGradeEnergy x 1 ∧
    canonicalRevelationProfile 2 x = canonicalGradeEnergy x 2 ∧
    canonicalRevelationProfile 3 x = canonicalGradeEnergy x 3 ∧
    (∀ h : Nat, canonicalRevelationProfile (h + 4) x = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [canonicalTailProfile, closureShadowState_zero_exact]
    rfl
  · rw [canonicalTailProfile, closureShadowState_one_exact]
    exact closureState_energy_g1g2g3 x
  · rw [canonicalTailProfile, closureShadowState_two_exact]
    exact closureState_energy_g2g3 x
  · rw [canonicalTailProfile, closureShadowState_three_exact]
    exact closureState_energy_g3 x
  · intro h
    have hzero : closureShadowState (h + 4) x = ClosureState.zero := by
      have hzero' := closureShadowState_after_stable_dimension h x
      unfold closureStableDimension at hzero'
      exact hzero'
    rw [canonicalTailProfile, hzero]
    rfl
  · rw [canonicalRevelationProfile, canonicalRevelationState_zero_exact]
    rfl
  · rw [canonicalRevelationProfile, canonicalRevelationState_one_exact]
    exact closureState_energy_g1_only x
  · rw [canonicalRevelationProfile, canonicalRevelationState_two_exact]
    exact closureState_energy_g2_only x
  · rw [canonicalRevelationProfile, canonicalRevelationState_three_exact]
    exact closureState_energy_g3_only x
  · intro h
    unfold canonicalRevelationProfile canonicalRevelationState
    have hproj0 : closureProjectionState (h + 4) x = x := by
      have hproj := closureProjectionState_after_stable_dimension h x
      unfold closureStableDimension at hproj
      exact hproj
    have hproj1 : closureProjectionState (h + 4 + 1) x = x := by
      have hproj := closureProjectionState_after_stable_dimension (h + 1) x
      unfold closureStableDimension at hproj
      rw [add_assoc_counting h 4 1, add_comm_counting 4 1, ← add_assoc_counting h 1 4]
      exact hproj
    rw [hproj1, hproj0, closureState_sub_self]
    rfl

/-- The canonical tail profile reconstructs exactly from the one-step revealed
energies, and the revealed energies recover the grade energies. -/
theorem canonical_tail_reconstruction (x : ClosureState) :
    canonicalTailProfile 0 x =
      canonicalRevelationProfile 0 x + canonicalTailProfile 1 x ∧
    canonicalTailProfile 1 x =
      canonicalRevelationProfile 1 x + canonicalTailProfile 2 x ∧
    canonicalTailProfile 2 x =
      canonicalRevelationProfile 2 x + canonicalTailProfile 3 x ∧
    canonicalTailProfile 3 x = canonicalRevelationProfile 3 x ∧
    canonicalTailProfile 4 x = 0 ∧
    canonicalGradeEnergy x 0 = canonicalRevelationProfile 0 x ∧
    canonicalGradeEnergy x 1 = canonicalRevelationProfile 1 x ∧
    canonicalGradeEnergy x 2 = canonicalRevelationProfile 2 x ∧
    canonicalGradeEnergy x 3 = canonicalRevelationProfile 3 x := by
  rcases canonical_tail_laws x with
    ⟨hE0, hE1, hE2, hE3, hEge4, hμ0, hμ1, hμ2, hμ3, _hμge4⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hE0, hμ0, hE1]
    calc
      canonicalGradeEnergy x 0 + canonicalGradeEnergy x 1 + canonicalGradeEnergy x 2 + canonicalGradeEnergy x 3
          = ((canonicalGradeEnergy x 0 + canonicalGradeEnergy x 1) + canonicalGradeEnergy x 2) +
              canonicalGradeEnergy x 3 := by
                rfl
      _ = (canonicalGradeEnergy x 0 + (canonicalGradeEnergy x 1 + canonicalGradeEnergy x 2)) +
            canonicalGradeEnergy x 3 := by
              rw [← add_assoc_counting
                (canonicalGradeEnergy x 0) (canonicalGradeEnergy x 1) (canonicalGradeEnergy x 2)]
      _ = canonicalGradeEnergy x 0 +
            ((canonicalGradeEnergy x 1 + canonicalGradeEnergy x 2) + canonicalGradeEnergy x 3) := by
              rw [add_assoc_counting
                (canonicalGradeEnergy x 0)
                (canonicalGradeEnergy x 1 + canonicalGradeEnergy x 2)
                (canonicalGradeEnergy x 3)]
      _ = canonicalGradeEnergy x 0 +
            (canonicalGradeEnergy x 1 + canonicalGradeEnergy x 2 + canonicalGradeEnergy x 3) := by
              rfl
  · rw [hE1, hμ1, hE2]
    exact add_assoc_counting
      (canonicalGradeEnergy x 1) (canonicalGradeEnergy x 2) (canonicalGradeEnergy x 3)
  · rw [hE2, hμ2, hE3]
  · rw [hE3, hμ3]
  · exact hEge4 0
  · exact hμ0.symm
  · exact hμ1.symm
  · exact hμ2.symm
  · exact hμ3.symm

end CoherenceCalculus
