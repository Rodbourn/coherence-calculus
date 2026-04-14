import CoherenceCalculus.PartIV.ClosureCurrentTrajectoryCore
import CoherenceCalculus.PartIV.ClosureCurrentCompletionTargetCore
import CoherenceCalculus.PartIV.ClosureCurrentConstructiveLawCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentCompletionBridgeCore

Constructive bridge from the smaller detached law layers to no-stage
completion.

`ClosureCurrentCompletionTargetCore` isolates the next target in the detached
closure program: one microscopic law should already carry a no-stage local
event four-state completion law on the same selected datum. The target itself
is honest, but taken alone it still hides one architectural seam. The present
file splits that seam into three visibly different ingredients:

* one constructive sector law on the detached current side;
* one concrete four-state assembly on that same local event;
* one Step 4 rigidity/canonical-representative package above the same
  law-native intrinsic sector generation, with carrier classification recovered
  from the canonical representatives.

From those split data, the no-stage completion law is recovered directly.
Nothing here proves that the smaller proposition-level microscopic closure law
always carries such a bridge. The point is narrower: the completion target is
now matched to a smaller constructive bridge layer rather than only to the
already-assembled completion law itself.
-/

namespace ClosureCurrent

/-- Signed readout and genuine four-leg frame above one fixed constructive
sector law. This is the current-side datum below the full four-state assembly:
it chooses how the hidden current is read as a visible four-state, but it does
not yet assert that the exactifier intertwines with the selected generator on
that assembled state. -/
structure FourStateReadout
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law) where
  readout : SignedExchangeReadout sectorLaw.currentCarrier
  frame : FourLegFrame sectorLaw.Leg

/-- Exact current-side readout target above one fixed constructive sector law.
-/
def FourStateReadoutTarget
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law) : Prop :=
  Nonempty (FourStateReadout sectorLaw)

/-- Exactifier/generator realization target above one fixed current-side
readout package. This is the remaining current-side identity needed to upgrade
that readout to a full four-state assembly. -/
def ExactifierRealizationTarget
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : FourStateReadout sectorLaw) : Prop :=
  ∀ current : PairExchangeCurrent sectorLaw.currentCarrier sectorLaw.Leg,
    assembledState data.readout data.frame (sectorLaw.exactifier.exactify current) =
      sectorLaw.bridge.generator.toFun
        (assembledState data.readout data.frame current)

/-- Explicit four-state assembly above one fixed constructive sector law. This
keeps only the signed readout, the genuine four-leg frame, and the
exactifier/generator intertwining identity on the assembled hidden state. -/
structure FourStateAssembly
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law)
    extends FourStateReadout sectorLaw where
  exactifier_realized :
    ∀ current : PairExchangeCurrent sectorLaw.currentCarrier sectorLaw.Leg,
      assembledState readout frame (sectorLaw.exactifier.exactify current) =
        sectorLaw.bridge.generator.toFun
          (assembledState readout frame current)

/-- Exact Step 4 carrier-classification target above one fixed constructive
sector law. -/
def CompletionClassificationTarget
    {Index Time Carrier Law : Type}
    (_sectorLaw : ConstructiveSectorLaw Index Time Carrier Law) : Prop :=
  Nonempty (SelectedBundle.CarrierClassification)

/-- Law-native Step 4 rigidity package above one fixed constructive sector law.
This is smaller than the full aligned completion datum: it keeps only the
endpoint-rigidity principle on the law's own intrinsic sector generation and
the common endpoint reduction. -/
structure CompletionRigidity
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law) where
  rigidityPrinciple : EndpointRigidity.Principle Time Carrier Law
  usesSectorGeneration :
    rigidityPrinciple.sectorGeneration = sectorLaw.toIntrinsicSectorGeneration
  endpointRigidity : EndpointRigidity.Reduction Time Carrier Law

/-- Exact law-native Step 4 rigidity target above one fixed constructive
sector law. -/
def CompletionRigidityTarget
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law) : Prop :=
  Nonempty (CompletionRigidity sectorLaw)

/-- Reduced Step 4 representative package above one fixed constructive sector
law. The endpoint-sensitive carriers keep canonical representative identities,
while the kinetic face is already kept only at the weaker classification level,
matching its stock-side role on the active surface. -/
structure CanonicalRepresentatives where
  phaseCanonicalRepresentative : Prop
  waveCanonicalRepresentative : Prop
  kineticRepresentativeClassified : Prop
  gaugeCanonicalRepresentative : Prop
  geometricCanonicalRepresentative : Prop
  phaseCanonicalRepresentative_valid : phaseCanonicalRepresentative
  waveCanonicalRepresentative_valid : waveCanonicalRepresentative
  kineticRepresentativeClassified_valid : kineticRepresentativeClassified
  gaugeCanonicalRepresentative_valid : gaugeCanonicalRepresentative
  geometricCanonicalRepresentative_valid : geometricCanonicalRepresentative

/-- Exact canonical-representative target above one fixed constructive sector
law. -/
def CanonicalRepresentativeTarget
    {Index Time Carrier Law : Type}
    (_sectorLaw : ConstructiveSectorLaw Index Time Carrier Law) : Prop :=
  Nonempty CanonicalRepresentatives

/-- Active Step 4 completion datum above one fixed constructive sector law. It
keeps only the endpoint-rigidity clauses, common endpoint reduction, and
the reduced representative package needed to rebuild the active completion
package over the law-native intrinsic sector generation. Carrier
classification is recovered from that same reduced package. -/
structure CompletionAlignment
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law) where
  localLawsReduceToFiniteJetOrder : Prop
  generatedSymmetryActsOnJetLevel : Prop
  compatibilityIdentitiesCutJetOperatorSpace : Prop
  admissibleEndpointEquivalenceRelation : Prop
  minimalTruncationProducesFiniteClosureQuotient : Prop
  singletonQuotientForcesUniqueCanonicalRepresentative : Prop
  nonsingletonQuotientForcesCanonicalNormalFormFamily : Prop
  endpointRigidity : EndpointRigidity.Reduction Time Carrier Law
  phaseCanonicalRepresentative : Prop
  waveCanonicalRepresentative : Prop
  kineticRepresentativeClassified : Prop
  gaugeCanonicalRepresentative : Prop
  geometricCanonicalRepresentative : Prop
  localLawsReduceToFiniteJetOrder_valid :
    localLawsReduceToFiniteJetOrder
  generatedSymmetryActsOnJetLevel_valid :
    generatedSymmetryActsOnJetLevel
  compatibilityIdentitiesCutJetOperatorSpace_valid :
    compatibilityIdentitiesCutJetOperatorSpace
  admissibleEndpointEquivalenceRelation_valid :
    admissibleEndpointEquivalenceRelation
  minimalTruncationProducesFiniteClosureQuotient_valid :
    minimalTruncationProducesFiniteClosureQuotient
  singletonQuotientForcesUniqueCanonicalRepresentative_valid :
    singletonQuotientForcesUniqueCanonicalRepresentative
  nonsingletonQuotientForcesCanonicalNormalFormFamily_valid :
    nonsingletonQuotientForcesCanonicalNormalFormFamily
  phaseCanonicalRepresentative_valid : phaseCanonicalRepresentative
  waveCanonicalRepresentative_valid : waveCanonicalRepresentative
  kineticRepresentativeClassified_valid : kineticRepresentativeClassified
  gaugeCanonicalRepresentative_valid : gaugeCanonicalRepresentative
  geometricCanonicalRepresentative_valid : geometricCanonicalRepresentative

/-- Split bridge from the constructive detached current lane to the no-stage
completion package. It keeps the four-state law and the active completion datum
separate, requiring only that the completion datum lives on the same selected
datum and physical selected law. -/
structure NoStageCompletionBridge
    (Index Time Carrier Law : Type) where
  sectorLaw : ConstructiveSectorLaw Index Time Carrier Law
  readout : SignedExchangeReadout sectorLaw.currentCarrier
  frame : FourLegFrame sectorLaw.Leg
  exactifier_realized :
    ∀ current : PairExchangeCurrent sectorLaw.currentCarrier sectorLaw.Leg,
      assembledState readout frame (sectorLaw.exactifier.exactify current) =
        sectorLaw.bridge.generator.toFun
          (assembledState readout frame current)
  completion : NaturalOperatorCompletion Time Carrier Law
  sameSelectedSelection :
    completion.sectorGeneration.selectedBundle.selectedSchurBridge.observer.selection =
      sectorLaw.bridge.selectedBridge.observer.selection
  samePhysicalPrinciple :
    completion.sectorGeneration.selectedBundle.physicalPrinciple =
      sectorLaw.physicalPrinciple

/-- The exact split completion-bridge target above one microscopic closure law:
the law is realized by one constructive sector law carrying a signed
four-state assembly and one aligned active completion datum. -/
def NoStageCompletionBridgeTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) : Prop :=
  ∃ data : NoStageCompletionBridge Index Time Carrier Law,
    data.sectorLaw.toMicroscopicClosureLaw = law

/-- Exact four-state assembly target above one fixed constructive sector law.
This records only the current-side signed readout/frame assembly needed for the
completion bridge. -/
def FourStateAssemblyTarget
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law) : Prop :=
  Nonempty (FourStateAssembly sectorLaw)

/-- Exact aligned-completion target above one fixed constructive sector law.
This records only the active Step 4 rigidity/canonical-representative datum
above that law-native intrinsic sector generation. Carrier classification is
recovered from that same datum. -/
def CompletionAlignmentTarget
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law) : Prop :=
  Nonempty (CompletionAlignment sectorLaw)

/-- Existence-level split completion witness above one smaller microscopic
closure law. It records one constructive sector law over that microscopic law,
one current-side readout with exactifier realization, and the two smaller
Step 4 existence targets that remain once carrier classification is read from
canonical representatives. This is the law-level split form of the completion
seam below the assembled completion bridge. -/
structure CompletionSplitWitness
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) where
  sectorLaw : ConstructiveSectorLaw Index Time Carrier Law
  sameLaw : sectorLaw.toMicroscopicClosureLaw = law
  readout : FourStateReadout sectorLaw
  exactifierRealized : ExactifierRealizationTarget readout
  rigidity : CompletionRigidityTarget sectorLaw
  representatives : CanonicalRepresentativeTarget sectorLaw

/-- Existence-level split completion target above one smaller microscopic
closure law. -/
def CompletionSplitTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) : Prop :=
  Nonempty (CompletionSplitWitness law)

namespace FourStateReadout

/-- Any actual current-side readout package realizes the corresponding exact
readout target. -/
theorem readoutTarget
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : FourStateReadout sectorLaw) :
    FourStateReadoutTarget sectorLaw := by
  exact ⟨data⟩

/-- One exactifier realization above a fixed current-side readout package
upgrades it to a full four-state assembly. -/
def toFourStateAssembly
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : FourStateReadout sectorLaw)
    (hexact : ExactifierRealizationTarget data) :
    FourStateAssembly sectorLaw where
  toFourStateReadout := data
  exactifier_realized := hexact

/-- A fixed current-side readout package plus its exactifier realization
already realize the full four-state assembly target. -/
theorem assemblyTargetOfExactifierTarget
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : FourStateReadout sectorLaw)
    (hexact : ExactifierRealizationTarget data) :
    FourStateAssemblyTarget sectorLaw := by
  exact ⟨data.toFourStateAssembly hexact⟩

end FourStateReadout

namespace CompletionRigidity

/-- Reassemble the smaller law-native Step 4 rigidity package from the
endpoint-rigidity principle on the fixed intrinsic sector generation together
with the reduced endpoint-rigidity surface. -/
def ofParts
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (rigidityPrinciple : EndpointRigidity.Principle Time Carrier Law)
    (usesSectorGeneration :
      rigidityPrinciple.sectorGeneration = sectorLaw.toIntrinsicSectorGeneration)
    (endpointRigidity : EndpointRigidity.Reduction Time Carrier Law) :
    CompletionRigidity sectorLaw where
  rigidityPrinciple := rigidityPrinciple
  usesSectorGeneration := usesSectorGeneration
  endpointRigidity := endpointRigidity

/-- Reassembling a law-native rigidity package from its own smaller parts
recovers the original package exactly. -/
theorem ofParts_eq
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : CompletionRigidity sectorLaw) :
    CompletionRigidity.ofParts
        data.rigidityPrinciple
        data.usesSectorGeneration
        data.endpointRigidity =
      data := by
  cases data
  rfl

/-- The reconstructed rigidity package remembers exactly the endpoint-rigidity
principle used to build it. -/
theorem ofParts_toRigidityPrinciple
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (rigidityPrinciple : EndpointRigidity.Principle Time Carrier Law)
    (usesSectorGeneration :
      rigidityPrinciple.sectorGeneration = sectorLaw.toIntrinsicSectorGeneration)
    (endpointRigidity : EndpointRigidity.Reduction Time Carrier Law) :
    (CompletionRigidity.ofParts
      rigidityPrinciple
      usesSectorGeneration
      endpointRigidity).rigidityPrinciple =
      rigidityPrinciple := rfl

/-- The reconstructed rigidity package remembers exactly the reduced
endpoint-rigidity surface used to build it. -/
theorem ofParts_toEndpointRigidity
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (rigidityPrinciple : EndpointRigidity.Principle Time Carrier Law)
    (usesSectorGeneration :
      rigidityPrinciple.sectorGeneration = sectorLaw.toIntrinsicSectorGeneration)
    (endpointRigidity : EndpointRigidity.Reduction Time Carrier Law) :
    (CompletionRigidity.ofParts
      rigidityPrinciple
      usesSectorGeneration
      endpointRigidity).endpointRigidity =
      endpointRigidity := rfl

/-- The smaller law-native rigidity package is determined by its actual
mathematical parts: the endpoint-rigidity principle on the fixed sector
generation and the reduced endpoint-rigidity surface. -/
theorem eq_of_parts_eq
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    {data other : CompletionRigidity sectorLaw}
    (hprinciple : data.rigidityPrinciple = other.rigidityPrinciple)
    (hendpoint : data.endpointRigidity = other.endpointRigidity) :
    data = other := by
  cases data
  cases other
  cases hprinciple
  cases hendpoint
  simp

/-- Any actual law-native Step 4 rigidity package realizes the corresponding
exact rigidity target. -/
theorem rigidityTarget
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : CompletionRigidity sectorLaw) :
    CompletionRigidityTarget sectorLaw := by
  exact ⟨data⟩

/-- Surface theorem for the smaller law-native Step 4 rigidity package. -/
theorem surface
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : CompletionRigidity sectorLaw) :
    data.rigidityPrinciple.sectorGeneration =
        sectorLaw.toIntrinsicSectorGeneration ∧
      data.rigidityPrinciple.localLawsReduceToFiniteJetOrder ∧
      data.rigidityPrinciple.generatedSymmetryActsOnJetLevel ∧
      data.rigidityPrinciple.compatibilityIdentitiesCutJetOperatorSpace ∧
      data.rigidityPrinciple.admissibleEndpointEquivalenceRelation ∧
      data.rigidityPrinciple.minimalTruncationProducesFiniteClosureQuotient ∧
      data.rigidityPrinciple.singletonQuotientForcesUniqueCanonicalRepresentative ∧
      data.rigidityPrinciple.nonsingletonQuotientForcesCanonicalNormalFormFamily ∧
      data.endpointRigidity.symmetryChannelScalarization ∧
      data.endpointRigidity.inheritedMinimalOrderClassSingleton ∧
      data.endpointRigidity.endpointClosureUniqueModuloContinuumEquivalence := by
  have hprinciple := EndpointRigidity.Principle.surface data.rigidityPrinciple
  have hreduction := EndpointRigidity.Reduction.surface data.endpointRigidity
  rcases hprinciple with
    ⟨hjet, hsymm, hcompat, hequiv, htrunc, hsingle, hfamily⟩
  rcases hreduction with ⟨hscalar, hsingleton, huniq⟩
  exact
    ⟨data.usesSectorGeneration,
      hjet,
      hsymm,
      hcompat,
      hequiv,
      htrunc,
      hsingle,
      hfamily,
      hscalar,
      hsingleton,
      huniq⟩

end CompletionRigidity

namespace CanonicalRepresentatives

/-- Canonical representative identities already classify the same carrier-level
representatives. So classification is not an additional Step 4 input once the
canonical representatives themselves are in hand. -/
def toClassification
    (data : CanonicalRepresentatives) :
  SelectedBundle.CarrierClassification where
  phaseRepresentativeClassified := data.phaseCanonicalRepresentative
  waveRepresentativeClassified := data.waveCanonicalRepresentative
  kineticRepresentativeClassified := data.kineticRepresentativeClassified
  gaugeRepresentativeClassified := data.gaugeCanonicalRepresentative
  geometricRepresentativeClassified := data.geometricCanonicalRepresentative
  phaseRepresentativeClassified_valid :=
    data.phaseCanonicalRepresentative_valid
  waveRepresentativeClassified_valid :=
    data.waveCanonicalRepresentative_valid
  kineticRepresentativeClassified_valid :=
    data.kineticRepresentativeClassified_valid
  gaugeRepresentativeClassified_valid :=
    data.gaugeCanonicalRepresentative_valid
  geometricRepresentativeClassified_valid :=
    data.geometricCanonicalRepresentative_valid

/-- Surface theorem for the reduced Step 4 representative package. -/
theorem surface
    (data : CanonicalRepresentatives) :
    data.phaseCanonicalRepresentative ∧
      data.waveCanonicalRepresentative ∧
      data.kineticRepresentativeClassified ∧
      data.gaugeCanonicalRepresentative ∧
      data.geometricCanonicalRepresentative := by
  exact
    ⟨data.phaseCanonicalRepresentative_valid,
      data.waveCanonicalRepresentative_valid,
      data.kineticRepresentativeClassified_valid,
      data.gaugeCanonicalRepresentative_valid,
      data.geometricCanonicalRepresentative_valid⟩

/-- Hence the reduced representative package already realizes the weaker
carrier-classification target above any fixed constructive sector law. -/
theorem classificationTarget
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : CanonicalRepresentatives) :
    CompletionClassificationTarget sectorLaw := by
  exact ⟨data.toClassification⟩

end CanonicalRepresentatives

namespace FourStateAssembly

/-- Any actual four-state assembly realizes the corresponding current-side
assembly target. -/
theorem assemblyTarget
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : FourStateAssembly sectorLaw) :
    FourStateAssemblyTarget sectorLaw := by
  exact ⟨data⟩

/-- Any actual four-state assembly still realizes the corresponding smaller
current-side readout target. -/
theorem readoutTarget
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : FourStateAssembly sectorLaw) :
    FourStateReadoutTarget sectorLaw := by
  exact data.toFourStateReadout.readoutTarget

/-- Any actual four-state assembly still realizes the corresponding exactifier
realization target above its own readout/frame data. -/
theorem exactifierRealizationTarget
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : FourStateAssembly sectorLaw) :
    ExactifierRealizationTarget data.toFourStateReadout := by
  exact data.exactifier_realized

/-- The current-side local-event object under one fixed four-state assembly. -/
def toLocalEventObject
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (_data : FourStateAssembly sectorLaw) :
    LocalEventObject Index Time Carrier Law :=
  sectorLaw.toConstructiveMicroscopicLaw.toLocalEventObject

/-- The framed local-event object carried by one explicit four-state assembly.
-/
def toFramedLocalEventObject
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : FourStateAssembly sectorLaw) :
    FramedLocalEventObject Index Time Carrier Law where
  object := data.toLocalEventObject
  readout := data.readout
  frame := data.frame

/-- The no-stage local-event four-state law carried by one explicit four-state
assembly above the fixed constructive sector law. -/
def toLocalEventFourStateLaw
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : FourStateAssembly sectorLaw) :
    LocalEventFourStateLaw Index Time Carrier Law where
  framed := data.toFramedLocalEventObject
  exactifier_realized := data.exactifier_realized

/-- On one fixed constructive sector law, the explicit four-state assembly is
already determined by its local state bridge. No extra current-side witness
remains once the signed readout, frame, and exactifier/generator intertwining
law have been read into that bridge. -/
theorem eq_of_localEventStateBridge_eq
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    {data data' : FourStateAssembly sectorLaw}
    (hbridge :
      data.toLocalEventFourStateLaw.toLocalEventStateBridge =
        data'.toLocalEventFourStateLaw.toLocalEventStateBridge) :
    data = data' := by
  cases data with
  | mk readoutData exactifier_realized =>
    cases readoutData with
    | mk readout frame =>
    cases data' with
      | mk readoutData' exactifier_realized' =>
        cases readoutData' with
        | mk readout' frame' =>
          cases hbridge
          rfl

/-- Transporting a fixed four-state assembly along an equality of constructive
sector laws does not change the explicit local state bridge it determines. -/
theorem localEventStateBridge_transport
    {Index Time Carrier Law : Type}
    {sectorLaw sectorLaw' : ConstructiveSectorLaw Index Time Carrier Law}
    (hsector : sectorLaw = sectorLaw')
    (data : FourStateAssembly sectorLaw) :
    (hsector ▸ data).toLocalEventFourStateLaw.toLocalEventStateBridge =
      data.toLocalEventFourStateLaw.toLocalEventStateBridge := by
  cases hsector
  rfl

/-- The fixed constructive-sector assembly determines the anchored current
object on which its hidden current is exactified. This depends only on the
underlying sector law, not on any extra completion datum. -/
def toAnchoredCurrentObject
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : FourStateAssembly sectorLaw) :
    AnchoredCurrentObject Index Time Carrier Law :=
  data.toLocalEventFourStateLaw.toLocalEventStateBridge.toAnchoredCurrentObject

/-- The fixed constructive-sector assembly determines the explicit current-side
state assembly on its own anchored current object. -/
def toCurrentStateAssembly
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : FourStateAssembly sectorLaw) :
    CurrentStateAssembly data.toAnchoredCurrentObject :=
  data.toLocalEventFourStateLaw.toLocalEventStateBridge.toCurrentStateAssembly

/-- Reduced hidden coordinates read directly from one fixed constructive-sector
assembly. -/
def realizeCoordinates
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : FourStateAssembly sectorLaw) :
    PairExchangeCurrent sectorLaw.currentCarrier sectorLaw.Leg →
      BalancedCoordinates :=
  data.toCurrentStateAssembly.realizeCoordinates

/-- Selected observed state read directly from one fixed constructive-sector
assembly. -/
def observedState
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : FourStateAssembly sectorLaw) :
    PairExchangeCurrent sectorLaw.currentCarrier sectorLaw.Leg → State :=
  data.toCurrentStateAssembly.observedState

/-- Repeated reduced hidden-current transport on the fixed constructive sector
law. This iterate depends only on the selected bridge generator carried by that
sector law, not on the auxiliary readout/frame presentation of a particular
assembly. -/
def coordinateIterate
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (_data : FourStateAssembly sectorLaw) :
    Nat → BalancedCoordinates → BalancedCoordinates :=
  _data.toCurrentStateAssembly.coordinateIterate

/-- Repeated selected observed transport on the fixed constructive sector law.
Again this depends only on the sector law itself. -/
def observedIterate
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (_data : FourStateAssembly sectorLaw) :
    Nat → State → State :=
  _data.toCurrentStateAssembly.observedIterate

/-- The selected observed state of a fixed constructive-sector assembly is
already the selected projection of its reduced hidden coordinates. -/
theorem observedFromCoordinates
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : FourStateAssembly sectorLaw) :
    ∀ current : PairExchangeCurrent sectorLaw.currentCarrier sectorLaw.Leg,
      data.observedState current =
        selectedProjection sectorLaw.bridge ((data.realizeCoordinates current).toState) := by
  intro current
  simpa [FourStateAssembly.observedState,
    FourStateAssembly.realizeCoordinates,
    FourStateAssembly.toCurrentStateAssembly,
    FourStateAssembly.toAnchoredCurrentObject]
    using data.toCurrentStateAssembly.observedFromCoordinates current

/-- Repeated exactification of the hidden pair current agrees with repeated
reduced transport on the three-coordinate carrier for any fixed constructive
sector assembly. -/
theorem coordinateTrajectory
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : FourStateAssembly sectorLaw) :
    ∀ n : Nat,
      ∀ current : PairExchangeCurrent sectorLaw.currentCarrier sectorLaw.Leg,
        data.realizeCoordinates (data.toAnchoredCurrentObject.exactifyIterate n current) =
          data.coordinateIterate n (data.realizeCoordinates current) := by
  intro n current
  simpa [FourStateAssembly.realizeCoordinates,
    FourStateAssembly.coordinateIterate,
    FourStateAssembly.toCurrentStateAssembly,
    FourStateAssembly.toAnchoredCurrentObject]
    using data.toCurrentStateAssembly.coordinateTrajectory n current

/-- Repeated exactification of the hidden pair current agrees with repeated
selected observed transport on the fixed constructive sector assembly. -/
theorem observedTrajectory
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : FourStateAssembly sectorLaw) :
    ∀ n : Nat,
      ∀ current : PairExchangeCurrent sectorLaw.currentCarrier sectorLaw.Leg,
        data.observedState (data.toAnchoredCurrentObject.exactifyIterate n current) =
          data.observedIterate n (data.observedState current) := by
  intro n current
  simpa [FourStateAssembly.observedState,
    FourStateAssembly.observedIterate,
    FourStateAssembly.toCurrentStateAssembly,
    FourStateAssembly.toAnchoredCurrentObject]
    using data.toCurrentStateAssembly.observedTrajectory n current

/-- Two fixed constructive-sector assemblies induce the same reduced hidden
future whenever they agree on the initial hidden coordinates. -/
theorem sameCoordinates_sameHiddenTrajectory
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (assembly assembly' : FourStateAssembly sectorLaw) :
    ∀ n : Nat,
      ∀ current current' : PairExchangeCurrent sectorLaw.currentCarrier sectorLaw.Leg,
        assembly.realizeCoordinates current = assembly'.realizeCoordinates current' →
          assembly.realizeCoordinates
              (assembly.toAnchoredCurrentObject.exactifyIterate n current) =
            assembly'.realizeCoordinates
              (assembly'.toAnchoredCurrentObject.exactifyIterate n current') := by
  intro n current current' hcoords
  calc
    assembly.realizeCoordinates
        (assembly.toAnchoredCurrentObject.exactifyIterate n current) =
          assembly.coordinateIterate n (assembly.realizeCoordinates current) :=
      assembly.coordinateTrajectory n current
    _ = assembly.coordinateIterate n (assembly'.realizeCoordinates current') := by
      rw [hcoords]
    _ = assembly'.coordinateIterate n (assembly'.realizeCoordinates current') := by
      rfl
    _ =
        assembly'.realizeCoordinates
          (assembly'.toAnchoredCurrentObject.exactifyIterate n current') := by
      symm
      exact assembly'.coordinateTrajectory n current'

/-- Two fixed constructive-sector assemblies induce the same selected observed
future whenever they agree on the initial hidden coordinates. -/
theorem sameCoordinates_sameObservedTrajectory
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (assembly assembly' : FourStateAssembly sectorLaw) :
    ∀ n : Nat,
      ∀ current current' : PairExchangeCurrent sectorLaw.currentCarrier sectorLaw.Leg,
        assembly.realizeCoordinates current = assembly'.realizeCoordinates current' →
          assembly.observedState
              (assembly.toAnchoredCurrentObject.exactifyIterate n current) =
            assembly'.observedState
              (assembly'.toAnchoredCurrentObject.exactifyIterate n current') := by
  intro n current current' hcoords
  calc
    assembly.observedState
        (assembly.toAnchoredCurrentObject.exactifyIterate n current) =
          assembly.observedIterate n (assembly.observedState current) :=
      assembly.observedTrajectory n current
    _ = assembly.observedIterate n
          (selectedProjection sectorLaw.bridge
            ((assembly.realizeCoordinates current).toState)) := by
      rw [assembly.observedFromCoordinates current]
    _ =
        assembly.observedIterate n
          (selectedProjection sectorLaw.bridge
            ((assembly'.realizeCoordinates current').toState)) := by
      rw [hcoords]
    _ =
        assembly'.observedIterate n
          (selectedProjection sectorLaw.bridge
            ((assembly'.realizeCoordinates current').toState)) := by
      rfl
    _ = assembly'.observedIterate n (assembly'.observedState current') := by
      rw [assembly'.observedFromCoordinates current']
    _ =
        assembly'.observedState
          (assembly'.toAnchoredCurrentObject.exactifyIterate n current') := by
      symm
      exact assembly'.observedTrajectory n current'

/-- On one fixed constructive sector law, two explicit current-side assemblies
induce the same reduced hidden future whenever their initial framed pair
currents agree slot-by-slot. So the remaining current-side freedom is already
compressed to the six local slot values. -/
theorem sameLocalSlots_sameHiddenTrajectory
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (assembly assembly' : FourStateAssembly sectorLaw) :
    ∀ n : Nat,
      ∀ current current' : PairExchangeCurrent sectorLaw.currentCarrier sectorLaw.Leg,
        (∀ slot : LocalSlot,
          localSlotReadout assembly.readout assembly.frame current slot =
            localSlotReadout assembly'.readout assembly'.frame current' slot) →
          assembly.realizeCoordinates
              (assembly.toAnchoredCurrentObject.exactifyIterate n current) =
            assembly'.realizeCoordinates
              (assembly'.toAnchoredCurrentObject.exactifyIterate n current') := by
  intro n current current' hslots
  apply assembly.sameCoordinates_sameHiddenTrajectory assembly' n current current'
  simpa [FourStateAssembly.realizeCoordinates,
    FourStateAssembly.toCurrentStateAssembly]
    using assembledCoordinates_eq_of_localSlotReadout_eq hslots

/-- On one fixed constructive sector law, two explicit current-side assemblies
also induce the same selected observed future whenever their initial framed
pair currents agree slot-by-slot. The visible trajectory is therefore already
rigid at the same six-slot level. -/
theorem sameLocalSlots_sameObservedTrajectory
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (assembly assembly' : FourStateAssembly sectorLaw) :
    ∀ n : Nat,
      ∀ current current' : PairExchangeCurrent sectorLaw.currentCarrier sectorLaw.Leg,
        (∀ slot : LocalSlot,
          localSlotReadout assembly.readout assembly.frame current slot =
            localSlotReadout assembly'.readout assembly'.frame current' slot) →
          assembly.observedState
              (assembly.toAnchoredCurrentObject.exactifyIterate n current) =
            assembly'.observedState
              (assembly'.toAnchoredCurrentObject.exactifyIterate n current') := by
  intro n current current' hslots
  apply assembly.sameCoordinates_sameObservedTrajectory assembly' n current current'
  simpa [FourStateAssembly.realizeCoordinates,
    FourStateAssembly.toCurrentStateAssembly]
    using assembledCoordinates_eq_of_localSlotReadout_eq hslots

end FourStateAssembly

namespace CompletionAlignment

/-- Carrier-classification package read from one aligned completion datum. -/
def toClassification
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : CompletionAlignment sectorLaw) :
  SelectedBundle.CarrierClassification where
  phaseRepresentativeClassified := data.phaseCanonicalRepresentative
  waveRepresentativeClassified := data.waveCanonicalRepresentative
  kineticRepresentativeClassified := data.kineticRepresentativeClassified
  gaugeRepresentativeClassified := data.gaugeCanonicalRepresentative
  geometricRepresentativeClassified := data.geometricCanonicalRepresentative
  phaseRepresentativeClassified_valid :=
    data.phaseCanonicalRepresentative_valid
  waveRepresentativeClassified_valid :=
    data.waveCanonicalRepresentative_valid
  kineticRepresentativeClassified_valid :=
    data.kineticRepresentativeClassified_valid
  gaugeRepresentativeClassified_valid :=
    data.gaugeCanonicalRepresentative_valid
  geometricRepresentativeClassified_valid :=
    data.geometricCanonicalRepresentative_valid

/-- Law-native Step 4 rigidity package read from one aligned completion datum.
-/
def toCompletionRigidity
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : CompletionAlignment sectorLaw) :
    CompletionRigidity sectorLaw where
  rigidityPrinciple := {
    sectorGeneration := sectorLaw.toIntrinsicSectorGeneration
    localLawsReduceToFiniteJetOrder :=
      data.localLawsReduceToFiniteJetOrder
    generatedSymmetryActsOnJetLevel :=
      data.generatedSymmetryActsOnJetLevel
    compatibilityIdentitiesCutJetOperatorSpace :=
      data.compatibilityIdentitiesCutJetOperatorSpace
    admissibleEndpointEquivalenceRelation :=
      data.admissibleEndpointEquivalenceRelation
    minimalTruncationProducesFiniteClosureQuotient :=
      data.minimalTruncationProducesFiniteClosureQuotient
    singletonQuotientForcesUniqueCanonicalRepresentative :=
      data.singletonQuotientForcesUniqueCanonicalRepresentative
    nonsingletonQuotientForcesCanonicalNormalFormFamily :=
      data.nonsingletonQuotientForcesCanonicalNormalFormFamily
    localLawsReduceToFiniteJetOrder_valid :=
      data.localLawsReduceToFiniteJetOrder_valid
    generatedSymmetryActsOnJetLevel_valid :=
      data.generatedSymmetryActsOnJetLevel_valid
    compatibilityIdentitiesCutJetOperatorSpace_valid :=
      data.compatibilityIdentitiesCutJetOperatorSpace_valid
    admissibleEndpointEquivalenceRelation_valid :=
      data.admissibleEndpointEquivalenceRelation_valid
    minimalTruncationProducesFiniteClosureQuotient_valid :=
      data.minimalTruncationProducesFiniteClosureQuotient_valid
    singletonQuotientForcesUniqueCanonicalRepresentative_valid :=
      data.singletonQuotientForcesUniqueCanonicalRepresentative_valid
    nonsingletonQuotientForcesCanonicalNormalFormFamily_valid :=
      data.nonsingletonQuotientForcesCanonicalNormalFormFamily_valid }
  usesSectorGeneration := rfl
  endpointRigidity := data.endpointRigidity

/-- Canonical representative package read from one aligned completion datum. -/
def toCanonicalRepresentatives
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : CompletionAlignment sectorLaw) :
    CanonicalRepresentatives where
  phaseCanonicalRepresentative := data.phaseCanonicalRepresentative
  waveCanonicalRepresentative := data.waveCanonicalRepresentative
  kineticRepresentativeClassified := data.kineticRepresentativeClassified
  gaugeCanonicalRepresentative := data.gaugeCanonicalRepresentative
  geometricCanonicalRepresentative := data.geometricCanonicalRepresentative
  phaseCanonicalRepresentative_valid :=
    data.phaseCanonicalRepresentative_valid
  waveCanonicalRepresentative_valid :=
    data.waveCanonicalRepresentative_valid
  kineticRepresentativeClassified_valid :=
    data.kineticRepresentativeClassified_valid
  gaugeCanonicalRepresentative_valid :=
    data.gaugeCanonicalRepresentative_valid
  geometricCanonicalRepresentative_valid :=
    data.geometricCanonicalRepresentative_valid

/-- Rebuild the Step 4 endpoint-rigidity principle over the law-native
intrinsic sector generation carried by the fixed constructive sector law. -/
def toRigidityPrinciple
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : CompletionAlignment sectorLaw) :
    EndpointRigidity.Principle Time Carrier Law where
  sectorGeneration := sectorLaw.toIntrinsicSectorGeneration
  localLawsReduceToFiniteJetOrder :=
    data.localLawsReduceToFiniteJetOrder
  generatedSymmetryActsOnJetLevel :=
    data.generatedSymmetryActsOnJetLevel
  compatibilityIdentitiesCutJetOperatorSpace :=
    data.compatibilityIdentitiesCutJetOperatorSpace
  admissibleEndpointEquivalenceRelation :=
    data.admissibleEndpointEquivalenceRelation
  minimalTruncationProducesFiniteClosureQuotient :=
    data.minimalTruncationProducesFiniteClosureQuotient
  singletonQuotientForcesUniqueCanonicalRepresentative :=
    data.singletonQuotientForcesUniqueCanonicalRepresentative
  nonsingletonQuotientForcesCanonicalNormalFormFamily :=
    data.nonsingletonQuotientForcesCanonicalNormalFormFamily
  localLawsReduceToFiniteJetOrder_valid :=
    data.localLawsReduceToFiniteJetOrder_valid
  generatedSymmetryActsOnJetLevel_valid :=
    data.generatedSymmetryActsOnJetLevel_valid
  compatibilityIdentitiesCutJetOperatorSpace_valid :=
    data.compatibilityIdentitiesCutJetOperatorSpace_valid
  admissibleEndpointEquivalenceRelation_valid :=
    data.admissibleEndpointEquivalenceRelation_valid
  minimalTruncationProducesFiniteClosureQuotient_valid :=
    data.minimalTruncationProducesFiniteClosureQuotient_valid
  singletonQuotientForcesUniqueCanonicalRepresentative_valid :=
    data.singletonQuotientForcesUniqueCanonicalRepresentative_valid
  nonsingletonQuotientForcesCanonicalNormalFormFamily_valid :=
    data.nonsingletonQuotientForcesCanonicalNormalFormFamily_valid

/-- Rebuild the active natural-operator completion package over the
constructive sector law's own intrinsic sector generation. -/
def toNaturalOperatorCompletion
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : CompletionAlignment sectorLaw) :
    NaturalOperatorCompletion Time Carrier Law where
  phaseRepresentativeClassified := data.toClassification.phaseRepresentativeClassified
  waveRepresentativeClassified := data.toClassification.waveRepresentativeClassified
  kineticRepresentativeClassified := data.toClassification.kineticRepresentativeClassified
  gaugeRepresentativeClassified := data.toClassification.gaugeRepresentativeClassified
  geometricRepresentativeClassified := data.toClassification.geometricRepresentativeClassified
  phaseRepresentativeClassified_valid :=
    data.toClassification.phaseRepresentativeClassified_valid
  waveRepresentativeClassified_valid :=
    data.toClassification.waveRepresentativeClassified_valid
  kineticRepresentativeClassified_valid :=
    data.toClassification.kineticRepresentativeClassified_valid
  gaugeRepresentativeClassified_valid :=
    data.toClassification.gaugeRepresentativeClassified_valid
  geometricRepresentativeClassified_valid :=
    data.toClassification.geometricRepresentativeClassified_valid
  sectorGeneration := sectorLaw.toIntrinsicSectorGeneration
  rigidityPrinciple := data.toRigidityPrinciple
  rigidityPrincipleUsesSameSectorGeneration := rfl
  endpointRigidity := data.endpointRigidity
  phaseCanonicalRepresentative := data.phaseCanonicalRepresentative
  waveCanonicalRepresentative := data.waveCanonicalRepresentative
  gaugeCanonicalRepresentative := data.gaugeCanonicalRepresentative
  geometricCanonicalRepresentative := data.geometricCanonicalRepresentative
  phaseCanonicalRepresentative_valid :=
    data.phaseCanonicalRepresentative_valid
  waveCanonicalRepresentative_valid :=
    data.waveCanonicalRepresentative_valid
  gaugeCanonicalRepresentative_valid :=
    data.gaugeCanonicalRepresentative_valid
  geometricCanonicalRepresentative_valid :=
    data.geometricCanonicalRepresentative_valid

/-- The rebuilt active completion package automatically lives on the selected
cut carried by the fixed constructive sector law. -/
theorem sameSelectedSelection
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : CompletionAlignment sectorLaw) :
    data.toNaturalOperatorCompletion.sectorGeneration.selectedBundle.selectedSchurBridge.observer.selection =
      sectorLaw.bridge.selectedBridge.observer.selection := by
  rfl

/-- The rebuilt active completion package automatically uses the same physical
selected law carried by the fixed constructive sector law. -/
theorem samePhysicalPrinciple
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : CompletionAlignment sectorLaw) :
    data.toNaturalOperatorCompletion.sectorGeneration.selectedBundle.physicalPrinciple =
      sectorLaw.physicalPrinciple := by
  rfl

/-- Any actual aligned completion datum realizes the corresponding alignment
target. -/
theorem alignmentTarget
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : CompletionAlignment sectorLaw) :
    CompletionAlignmentTarget sectorLaw := by
  exact ⟨data⟩

/-- Any actual aligned completion datum realizes the corresponding exact
carrier-classification target. -/
theorem classificationTarget
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : CompletionAlignment sectorLaw) :
    CompletionClassificationTarget sectorLaw := by
  exact ⟨data.toClassification⟩

/-- Any actual aligned completion datum realizes the corresponding exact
law-native Step 4 rigidity target. -/
theorem rigidityTarget
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : CompletionAlignment sectorLaw) :
    CompletionRigidityTarget sectorLaw := by
  exact ⟨data.toCompletionRigidity⟩

/-- Any actual aligned completion datum realizes the corresponding exact
canonical-representative target. -/
theorem canonicalRepresentativeTarget
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : CompletionAlignment sectorLaw) :
    CanonicalRepresentativeTarget sectorLaw := by
  exact ⟨data.toCanonicalRepresentatives⟩

/-- Reassemble the aligned completion datum from the two smaller Step 4
packages: the law-native rigidity mechanism and the canonical representative
identities. Carrier classification is recovered from the latter. -/
def ofParts
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (rigidity : CompletionRigidity sectorLaw)
    (representatives : CanonicalRepresentatives) :
    CompletionAlignment sectorLaw where
  localLawsReduceToFiniteJetOrder :=
    rigidity.rigidityPrinciple.localLawsReduceToFiniteJetOrder
  generatedSymmetryActsOnJetLevel :=
    rigidity.rigidityPrinciple.generatedSymmetryActsOnJetLevel
  compatibilityIdentitiesCutJetOperatorSpace :=
    rigidity.rigidityPrinciple.compatibilityIdentitiesCutJetOperatorSpace
  admissibleEndpointEquivalenceRelation :=
    rigidity.rigidityPrinciple.admissibleEndpointEquivalenceRelation
  minimalTruncationProducesFiniteClosureQuotient :=
    rigidity.rigidityPrinciple.minimalTruncationProducesFiniteClosureQuotient
  singletonQuotientForcesUniqueCanonicalRepresentative :=
    rigidity.rigidityPrinciple.singletonQuotientForcesUniqueCanonicalRepresentative
  nonsingletonQuotientForcesCanonicalNormalFormFamily :=
    rigidity.rigidityPrinciple.nonsingletonQuotientForcesCanonicalNormalFormFamily
  endpointRigidity := rigidity.endpointRigidity
  phaseCanonicalRepresentative :=
    representatives.phaseCanonicalRepresentative
  waveCanonicalRepresentative :=
    representatives.waveCanonicalRepresentative
  kineticRepresentativeClassified :=
    representatives.kineticRepresentativeClassified
  gaugeCanonicalRepresentative :=
    representatives.gaugeCanonicalRepresentative
  geometricCanonicalRepresentative :=
    representatives.geometricCanonicalRepresentative
  localLawsReduceToFiniteJetOrder_valid :=
    rigidity.rigidityPrinciple.localLawsReduceToFiniteJetOrder_valid
  generatedSymmetryActsOnJetLevel_valid :=
    rigidity.rigidityPrinciple.generatedSymmetryActsOnJetLevel_valid
  compatibilityIdentitiesCutJetOperatorSpace_valid :=
    rigidity.rigidityPrinciple.compatibilityIdentitiesCutJetOperatorSpace_valid
  admissibleEndpointEquivalenceRelation_valid :=
    rigidity.rigidityPrinciple.admissibleEndpointEquivalenceRelation_valid
  minimalTruncationProducesFiniteClosureQuotient_valid :=
    rigidity.rigidityPrinciple.minimalTruncationProducesFiniteClosureQuotient_valid
  singletonQuotientForcesUniqueCanonicalRepresentative_valid :=
    rigidity.rigidityPrinciple.singletonQuotientForcesUniqueCanonicalRepresentative_valid
  nonsingletonQuotientForcesCanonicalNormalFormFamily_valid :=
    rigidity.rigidityPrinciple.nonsingletonQuotientForcesCanonicalNormalFormFamily_valid
  phaseCanonicalRepresentative_valid :=
    representatives.phaseCanonicalRepresentative_valid
  waveCanonicalRepresentative_valid :=
    representatives.waveCanonicalRepresentative_valid
  kineticRepresentativeClassified_valid :=
    representatives.kineticRepresentativeClassified_valid
  gaugeCanonicalRepresentative_valid :=
    representatives.gaugeCanonicalRepresentative_valid
  geometricCanonicalRepresentative_valid :=
    representatives.geometricCanonicalRepresentative_valid

/-- Reassembling an aligned completion datum from its own smaller Step 4 parts
recovers the original datum exactly. -/
theorem ofParts_eq
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : CompletionAlignment sectorLaw) :
    CompletionAlignment.ofParts
        data.toCompletionRigidity
        data.toCanonicalRepresentatives =
      data := by
  cases data
  rfl

/-- The reconstructed completion datum remembers exactly the rigidity package
used to build it. -/
theorem ofParts_toCompletionRigidity
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (rigidity : CompletionRigidity sectorLaw)
    (representatives : CanonicalRepresentatives) :
    (CompletionAlignment.ofParts rigidity representatives).toCompletionRigidity =
      rigidity := by
  cases rigidity with
  | mk rigidityPrinciple usesSectorGeneration endpointRigidity =>
      cases rigidityPrinciple with
      | mk sectorGeneration
          localLawsReduceToFiniteJetOrder
          generatedSymmetryActsOnJetLevel
          compatibilityIdentitiesCutJetOperatorSpace
          admissibleEndpointEquivalenceRelation
          minimalTruncationProducesFiniteClosureQuotient
          singletonQuotientForcesUniqueCanonicalRepresentative
          nonsingletonQuotientForcesCanonicalNormalFormFamily
          localLawsReduceToFiniteJetOrder_valid
          generatedSymmetryActsOnJetLevel_valid
          compatibilityIdentitiesCutJetOperatorSpace_valid
          admissibleEndpointEquivalenceRelation_valid
          minimalTruncationProducesFiniteClosureQuotient_valid
          singletonQuotientForcesUniqueCanonicalRepresentative_valid
          nonsingletonQuotientForcesCanonicalNormalFormFamily_valid =>
            cases usesSectorGeneration
            cases representatives with
            | mk phase wave kinetic gauge geometric hphase hwave hkinetic hgauge hgeometric =>
                rfl

/-- The reconstructed completion datum remembers exactly the canonical
representative package used to build it. -/
theorem ofParts_toCanonicalRepresentatives
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (rigidity : CompletionRigidity sectorLaw)
    (representatives : CanonicalRepresentatives) :
    (CompletionAlignment.ofParts rigidity representatives).toCanonicalRepresentatives =
      representatives := by
  cases rigidity
  cases representatives
  rfl

/-- Surface theorem for one aligned completion datum above a fixed
constructive sector law. -/
theorem surface
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : CompletionAlignment sectorLaw) :
    data.toNaturalOperatorCompletion.sectorGeneration.selectedBundle.selectedSchurBridge.observer.selection =
        sectorLaw.bridge.selectedBridge.observer.selection ∧
      data.toNaturalOperatorCompletion.sectorGeneration.selectedBundle.physicalPrinciple =
        sectorLaw.physicalPrinciple ∧
      PartIVLawCompletionStatement data.toNaturalOperatorCompletion := by
  exact
    ⟨data.sameSelectedSelection,
      data.samePhysicalPrinciple,
      partIV_law_completion data.toNaturalOperatorCompletion⟩

end CompletionAlignment

namespace _root_.CoherenceCalculus.NaturalOperatorCompletion

/-- Read the smaller aligned completion datum back from a natural-operator
completion package once its sector generation is identified with the fixed
intrinsic sector generation of the constructive sector law. -/
def toCompletionAlignment
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : NaturalOperatorCompletion Time Carrier Law)
    (_usesSectorGeneration :
      data.sectorGeneration = sectorLaw.toIntrinsicSectorGeneration) :
    CompletionAlignment sectorLaw where
  localLawsReduceToFiniteJetOrder :=
    data.rigidityPrinciple.localLawsReduceToFiniteJetOrder
  generatedSymmetryActsOnJetLevel :=
    data.rigidityPrinciple.generatedSymmetryActsOnJetLevel
  compatibilityIdentitiesCutJetOperatorSpace :=
    data.rigidityPrinciple.compatibilityIdentitiesCutJetOperatorSpace
  admissibleEndpointEquivalenceRelation :=
    data.rigidityPrinciple.admissibleEndpointEquivalenceRelation
  minimalTruncationProducesFiniteClosureQuotient :=
    data.rigidityPrinciple.minimalTruncationProducesFiniteClosureQuotient
  singletonQuotientForcesUniqueCanonicalRepresentative :=
    data.rigidityPrinciple.singletonQuotientForcesUniqueCanonicalRepresentative
  nonsingletonQuotientForcesCanonicalNormalFormFamily :=
    data.rigidityPrinciple.nonsingletonQuotientForcesCanonicalNormalFormFamily
  endpointRigidity := data.endpointRigidity
  phaseCanonicalRepresentative := data.phaseCanonicalRepresentative
  waveCanonicalRepresentative := data.waveCanonicalRepresentative
  kineticRepresentativeClassified := data.kineticRepresentativeClassified
  gaugeCanonicalRepresentative := data.gaugeCanonicalRepresentative
  geometricCanonicalRepresentative := data.geometricCanonicalRepresentative
  localLawsReduceToFiniteJetOrder_valid :=
    data.rigidityPrinciple.localLawsReduceToFiniteJetOrder_valid
  generatedSymmetryActsOnJetLevel_valid :=
    data.rigidityPrinciple.generatedSymmetryActsOnJetLevel_valid
  compatibilityIdentitiesCutJetOperatorSpace_valid :=
    data.rigidityPrinciple.compatibilityIdentitiesCutJetOperatorSpace_valid
  admissibleEndpointEquivalenceRelation_valid :=
    data.rigidityPrinciple.admissibleEndpointEquivalenceRelation_valid
  minimalTruncationProducesFiniteClosureQuotient_valid :=
    data.rigidityPrinciple.minimalTruncationProducesFiniteClosureQuotient_valid
  singletonQuotientForcesUniqueCanonicalRepresentative_valid :=
    data.rigidityPrinciple.singletonQuotientForcesUniqueCanonicalRepresentative_valid
  nonsingletonQuotientForcesCanonicalNormalFormFamily_valid :=
    data.rigidityPrinciple.nonsingletonQuotientForcesCanonicalNormalFormFamily_valid
  phaseCanonicalRepresentative_valid :=
    data.phaseCanonicalRepresentative_valid
  waveCanonicalRepresentative_valid :=
    data.waveCanonicalRepresentative_valid
  kineticRepresentativeClassified_valid :=
    data.kineticRepresentativeClassified_valid
  gaugeCanonicalRepresentative_valid :=
    data.gaugeCanonicalRepresentative_valid
  geometricCanonicalRepresentative_valid :=
    data.geometricCanonicalRepresentative_valid

end _root_.CoherenceCalculus.NaturalOperatorCompletion

namespace CompletionAlignment

/-- Reconstructing the aligned completion datum from its own natural-operator
completion package recovers the original datum exactly. -/
theorem toNaturalOperatorCompletion_toCompletionAlignment
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (data : CompletionAlignment sectorLaw) :
    (_root_.CoherenceCalculus.NaturalOperatorCompletion.toCompletionAlignment
      data.toNaturalOperatorCompletion
        (by rfl : data.toNaturalOperatorCompletion.sectorGeneration =
            sectorLaw.toIntrinsicSectorGeneration)) =
      data := by
  cases data
  simp [CompletionAlignment.toNaturalOperatorCompletion,
    CompletionAlignment.toClassification,
    CompletionAlignment.toRigidityPrinciple,
    _root_.CoherenceCalculus.NaturalOperatorCompletion.toCompletionAlignment]

/-- On one fixed constructive sector law, the natural-operator completion
package remembers the aligned completion datum exactly. -/
theorem eq_of_toNaturalOperatorCompletion_eq
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    {data other : CompletionAlignment sectorLaw}
    (hcompletion :
      data.toNaturalOperatorCompletion =
        other.toNaturalOperatorCompletion) :
    data = other := by
  have hrigidity :
      data.toCompletionRigidity = other.toCompletionRigidity := by
    cases data
    cases other
    simp [CompletionAlignment.toNaturalOperatorCompletion,
      CompletionAlignment.toCompletionRigidity] at hcompletion ⊢
    rcases hcompletion with
      ⟨_hclass, hrigidityPrinciple, hendpoint,
        _hphase, _hwave, _hgauge, _hgeometric⟩
    cases hrigidityPrinciple
    simp [hendpoint]
  have hrepresentatives :
      data.toCanonicalRepresentatives = other.toCanonicalRepresentatives := by
    cases data
    cases other
    simp [CompletionAlignment.toNaturalOperatorCompletion,
      CompletionAlignment.toCanonicalRepresentatives] at hcompletion ⊢
    rcases hcompletion with ⟨hclass, _hrest⟩
    cases hclass
    simp
  calc
    data =
        CompletionAlignment.ofParts
          data.toCompletionRigidity
          data.toCanonicalRepresentatives := by
            symm
            exact CompletionAlignment.ofParts_eq data
    _ =
        CompletionAlignment.ofParts
          other.toCompletionRigidity
          other.toCanonicalRepresentatives := by
            simp [hrigidity, hrepresentatives]
    _ = other := by
          exact CompletionAlignment.ofParts_eq other

end CompletionAlignment

namespace NoStageCompletionBridge

/-- The underlying proposition-level microscopic closure law carried by the
completion bridge. -/
def toMicroscopicClosureLaw
    {Index Time Carrier Law : Type}
    (data : NoStageCompletionBridge Index Time Carrier Law) :
    MicroscopicClosureLaw Index Time Carrier Law :=
  data.sectorLaw.toMicroscopicClosureLaw

/-- Any actual split completion bridge immediately realizes the corresponding
bridge target for its underlying microscopic closure law. -/
theorem bridgeTarget
    {Index Time Carrier Law : Type}
    (data : NoStageCompletionBridge Index Time Carrier Law) :
    NoStageCompletionBridgeTarget data.toMicroscopicClosureLaw := by
  exact ⟨data, rfl⟩

/-- Recover the explicit four-state assembly from the split completion bridge.
-/
def toFourStateAssembly
    {Index Time Carrier Law : Type}
    (data : NoStageCompletionBridge Index Time Carrier Law) :
    FourStateAssembly data.sectorLaw where
  readout := data.readout
  frame := data.frame
  exactifier_realized := data.exactifier_realized

/-- Recover the aligned Step 4 completion datum from the split completion
bridge. -/
def toCompletionAlignment
    {Index Time Carrier Law : Type}
    (data : NoStageCompletionBridge Index Time Carrier Law) :
    CompletionAlignment data.sectorLaw where
  localLawsReduceToFiniteJetOrder :=
    data.completion.rigidityPrinciple.localLawsReduceToFiniteJetOrder
  generatedSymmetryActsOnJetLevel :=
    data.completion.rigidityPrinciple.generatedSymmetryActsOnJetLevel
  compatibilityIdentitiesCutJetOperatorSpace :=
    data.completion.rigidityPrinciple.compatibilityIdentitiesCutJetOperatorSpace
  admissibleEndpointEquivalenceRelation :=
    data.completion.rigidityPrinciple.admissibleEndpointEquivalenceRelation
  minimalTruncationProducesFiniteClosureQuotient :=
    data.completion.rigidityPrinciple.minimalTruncationProducesFiniteClosureQuotient
  singletonQuotientForcesUniqueCanonicalRepresentative :=
    data.completion.rigidityPrinciple.singletonQuotientForcesUniqueCanonicalRepresentative
  nonsingletonQuotientForcesCanonicalNormalFormFamily :=
    data.completion.rigidityPrinciple.nonsingletonQuotientForcesCanonicalNormalFormFamily
  endpointRigidity := data.completion.endpointRigidity
  phaseCanonicalRepresentative :=
    data.completion.phaseCanonicalRepresentative
  waveCanonicalRepresentative :=
    data.completion.waveCanonicalRepresentative
  kineticRepresentativeClassified :=
    data.completion.kineticRepresentativeClassified
  gaugeCanonicalRepresentative :=
    data.completion.gaugeCanonicalRepresentative
  geometricCanonicalRepresentative :=
    data.completion.geometricCanonicalRepresentative
  localLawsReduceToFiniteJetOrder_valid :=
    data.completion.rigidityPrinciple.localLawsReduceToFiniteJetOrder_valid
  generatedSymmetryActsOnJetLevel_valid :=
    data.completion.rigidityPrinciple.generatedSymmetryActsOnJetLevel_valid
  compatibilityIdentitiesCutJetOperatorSpace_valid :=
    data.completion.rigidityPrinciple.compatibilityIdentitiesCutJetOperatorSpace_valid
  admissibleEndpointEquivalenceRelation_valid :=
    data.completion.rigidityPrinciple.admissibleEndpointEquivalenceRelation_valid
  minimalTruncationProducesFiniteClosureQuotient_valid :=
    data.completion.rigidityPrinciple.minimalTruncationProducesFiniteClosureQuotient_valid
  singletonQuotientForcesUniqueCanonicalRepresentative_valid :=
    data.completion.rigidityPrinciple.singletonQuotientForcesUniqueCanonicalRepresentative_valid
  nonsingletonQuotientForcesCanonicalNormalFormFamily_valid :=
    data.completion.rigidityPrinciple.nonsingletonQuotientForcesCanonicalNormalFormFamily_valid
  phaseCanonicalRepresentative_valid :=
    data.completion.phaseCanonicalRepresentative_valid
  waveCanonicalRepresentative_valid :=
    data.completion.waveCanonicalRepresentative_valid
  kineticRepresentativeClassified_valid :=
    data.completion.kineticRepresentativeClassified_valid
  gaugeCanonicalRepresentative_valid :=
    data.completion.gaugeCanonicalRepresentative_valid
  geometricCanonicalRepresentative_valid :=
    data.completion.geometricCanonicalRepresentative_valid

/-- The completion bridge still carries the constructive origin layer. -/
theorem originClosureTarget
    {Index Time Carrier Law : Type}
    (data : NoStageCompletionBridge Index Time Carrier Law) :
    OriginClosureTarget data.toMicroscopicClosureLaw := by
  exact data.sectorLaw.originClosureTarget

/-- The completion bridge still carries the constructive sector layer. -/
theorem sectorClosureTarget
    {Index Time Carrier Law : Type}
    (data : NoStageCompletionBridge Index Time Carrier Law) :
    SectorClosureTarget data.toMicroscopicClosureLaw := by
  exact data.sectorLaw.sectorClosureTarget

/-- Local-event object read from the constructive sector law. -/
def toLocalEventObject
    {Index Time Carrier Law : Type}
    (data : NoStageCompletionBridge Index Time Carrier Law) :
    LocalEventObject Index Time Carrier Law :=
  data.sectorLaw.toConstructiveMicroscopicLaw.toLocalEventObject

/-- Framed local-event object carried by the completion bridge. -/
def toFramedLocalEventObject
    {Index Time Carrier Law : Type}
    (data : NoStageCompletionBridge Index Time Carrier Law) :
    FramedLocalEventObject Index Time Carrier Law where
  object := data.toLocalEventObject
  readout := data.readout
  frame := data.frame

/-- No-stage local-event four-state law carried by the completion bridge. -/
def toLocalEventFourStateLaw
    {Index Time Carrier Law : Type}
    (data : NoStageCompletionBridge Index Time Carrier Law) :
    LocalEventFourStateLaw Index Time Carrier Law where
  framed := data.toFramedLocalEventObject
  exactifier_realized := data.exactifier_realized

/-- Build the no-stage completion law from the split bridge data. The
`NaturalOperatorCompletion` provides the Step 4 completion package, while the
constructive sector law plus explicit state assembly provide the current-side
and Step 3 inputs on the same selected datum. -/
def toLocalEventFourStateCompletionLaw
    {Index Time Carrier Law : Type}
    (data : NoStageCompletionBridge Index Time Carrier Law) :
    LocalEventFourStateCompletionLaw Index Time Carrier Law where
  fourStateLaw := data.toLocalEventFourStateLaw
  canonicalGeneration := data.completion.sectorGeneration.toCanonicalGeneration
  generatedFromIntrinsicChannelAlgebra :=
    data.completion.sectorGeneration.generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly :=
    data.completion.sectorGeneration.minimalCompatibleRealizationsOnly
  localLawsReduceToFiniteJetOrder :=
    data.completion.rigidityPrinciple.localLawsReduceToFiniteJetOrder
  generatedSymmetryActsOnJetLevel :=
    data.completion.rigidityPrinciple.generatedSymmetryActsOnJetLevel
  compatibilityIdentitiesCutJetOperatorSpace :=
    data.completion.rigidityPrinciple.compatibilityIdentitiesCutJetOperatorSpace
  admissibleEndpointEquivalenceRelation :=
    data.completion.rigidityPrinciple.admissibleEndpointEquivalenceRelation
  minimalTruncationProducesFiniteClosureQuotient :=
    data.completion.rigidityPrinciple.minimalTruncationProducesFiniteClosureQuotient
  singletonQuotientForcesUniqueCanonicalRepresentative :=
    data.completion.rigidityPrinciple.singletonQuotientForcesUniqueCanonicalRepresentative
  nonsingletonQuotientForcesCanonicalNormalFormFamily :=
    data.completion.rigidityPrinciple.nonsingletonQuotientForcesCanonicalNormalFormFamily
  endpointRigidity := data.completion.endpointRigidity
  phaseCanonicalRepresentative := data.completion.phaseCanonicalRepresentative
  waveCanonicalRepresentative := data.completion.waveCanonicalRepresentative
  kineticRepresentativeClassified := data.completion.kineticRepresentativeClassified
  gaugeCanonicalRepresentative := data.completion.gaugeCanonicalRepresentative
  geometricCanonicalRepresentative := data.completion.geometricCanonicalRepresentative
  generatedFromIntrinsicChannelAlgebra_valid :=
    data.completion.sectorGeneration.generatedFromIntrinsicChannelAlgebra_valid
  minimalCompatibleRealizationsOnly_valid :=
    data.completion.sectorGeneration.minimalCompatibleRealizationsOnly_valid
  localLawsReduceToFiniteJetOrder_valid :=
    data.completion.rigidityPrinciple.localLawsReduceToFiniteJetOrder_valid
  generatedSymmetryActsOnJetLevel_valid :=
    data.completion.rigidityPrinciple.generatedSymmetryActsOnJetLevel_valid
  compatibilityIdentitiesCutJetOperatorSpace_valid :=
    data.completion.rigidityPrinciple.compatibilityIdentitiesCutJetOperatorSpace_valid
  admissibleEndpointEquivalenceRelation_valid :=
    data.completion.rigidityPrinciple.admissibleEndpointEquivalenceRelation_valid
  minimalTruncationProducesFiniteClosureQuotient_valid :=
    data.completion.rigidityPrinciple.minimalTruncationProducesFiniteClosureQuotient_valid
  singletonQuotientForcesUniqueCanonicalRepresentative_valid :=
    data.completion.rigidityPrinciple.singletonQuotientForcesUniqueCanonicalRepresentative_valid
  nonsingletonQuotientForcesCanonicalNormalFormFamily_valid :=
    data.completion.rigidityPrinciple.nonsingletonQuotientForcesCanonicalNormalFormFamily_valid
  phaseCanonicalRepresentative_valid :=
    data.completion.phaseCanonicalRepresentative_valid
  waveCanonicalRepresentative_valid :=
    data.completion.waveCanonicalRepresentative_valid
  kineticRepresentativeClassified_valid :=
    data.completion.kineticRepresentativeClassified_valid
  gaugeCanonicalRepresentative_valid :=
    data.completion.gaugeCanonicalRepresentative_valid
  geometricCanonicalRepresentative_valid :=
    data.completion.geometricCanonicalRepresentative_valid

/-- The split bridge already records the exact alignment datum saying that the
active completion package lives on the same selected bridge and physical
selected law as the constructive sector law. -/
theorem alignmentSurface
    {Index Time Carrier Law : Type}
    (data : NoStageCompletionBridge Index Time Carrier Law) :
    data.completion.sectorGeneration.selectedBundle.selectedSchurBridge.observer.selection =
      data.sectorLaw.bridge.selectedBridge.observer.selection ∧
      data.completion.sectorGeneration.selectedBundle.physicalPrinciple =
        data.sectorLaw.physicalPrinciple ∧
      PartIVLawCompletionStatement
        data.toLocalEventFourStateCompletionLaw.toNaturalOperatorCompletion := by
  exact
    ⟨data.sameSelectedSelection,
      data.samePhysicalPrinciple,
      partIV_law_completion data.toLocalEventFourStateCompletionLaw.toNaturalOperatorCompletion⟩

/-- Canonical no-stage completion witness carried by the split bridge. -/
def toNoStageCompletionWitness
    {Index Time Carrier Law : Type}
    (data : NoStageCompletionBridge Index Time Carrier Law) :
    NoStageCompletionWitness data.toMicroscopicClosureLaw where
  completionLaw := data.toLocalEventFourStateCompletionLaw
  sameBridge := rfl
  samePhysicalPrinciple := rfl

/-- The split bridge already forces the no-stage completion target. -/
theorem completionTarget
    {Index Time Carrier Law : Type}
    (data : NoStageCompletionBridge Index Time Carrier Law) :
    NoStageCompletionTarget data.toMicroscopicClosureLaw := by
  exact ⟨data.toNoStageCompletionWitness⟩

/-- The detached selected-bundle forcing surface still follows from the split
completion bridge. -/
theorem originTargetSurface
    {Index Time Carrier Law : Type}
    (data : NoStageCompletionBridge Index Time Carrier Law) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      realized_generator_carries_bedrock_law data.sectorLaw.bridge.generator ∧
      AutonomousHorizon
        data.sectorLaw.bridge.selectedBridge.observer.selection.realization.tower
        data.sectorLaw.bridge.selectedBridge.observer.selection.horizon
        data.sectorLaw.bridge.generator ∧
      horizonFiberInvariant
        data.sectorLaw.bridge.selectedBridge.observer.selection.realization.tower
        data.sectorLaw.bridge.selectedBridge.observer.selection.horizon
        data.sectorLaw.bridge.generator := by
  exact data.sectorLaw.toConstructiveMicroscopicLaw.originTargetSurface

/-- The detached Step 3 forcing surface still follows from the split
completion bridge. -/
theorem sectorTargetSurface
    {Index Time Carrier Law : Type}
    (data : NoStageCompletionBridge Index Time Carrier Law) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
      realized_generator_carries_bedrock_law data.sectorLaw.bridge.generator ∧
      AutonomousHorizon
        data.sectorLaw.bridge.selectedBridge.observer.selection.realization.tower
        data.sectorLaw.bridge.selectedBridge.observer.selection.horizon
        data.sectorLaw.bridge.generator ∧
      horizonFiberInvariant
        data.sectorLaw.bridge.selectedBridge.observer.selection.realization.tower
        data.sectorLaw.bridge.selectedBridge.observer.selection.horizon
        data.sectorLaw.bridge.generator ∧
      (∃ generatedFromIntrinsicChannelAlgebra :
          Prop,
          ∃ minimalCompatibleRealizationsOnly : Prop,
            generatedFromIntrinsicChannelAlgebra ∧
              minimalCompatibleRealizationsOnly) ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  exact data.sectorLaw.sectorTargetSurface

/-- The active Part IV completion surface already follows from the split
completion bridge with no extra completion witness hypothesis. -/
theorem completionTargetSurface
    {Index Time Carrier Law : Type}
    (data : NoStageCompletionBridge Index Time Carrier Law) :
    ∃ witness : NoStageCompletionWitness data.toMicroscopicClosureLaw,
      witness.completionLaw.fourStateLaw.framed.object.bridge =
          data.toMicroscopicClosureLaw.bridge ∧
        witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          data.toMicroscopicClosureLaw.physicalPrinciple ∧
        PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion := by
  exact
    data.toMicroscopicClosureLaw.completionTargetSurface
      data.completionTarget

/-- Grouped surface carried by the split completion bridge: the constructive
origin and sector layers remain intact, and the no-stage completion surface is
already recovered from the same bridge. -/
theorem fullSurface
    {Index Time Carrier Law : Type}
    (data : NoStageCompletionBridge Index Time Carrier Law) :
    ∃ witness : NoStageCompletionWitness data.toMicroscopicClosureLaw,
      witness.completionLaw.fourStateLaw.framed.object.bridge =
          data.toMicroscopicClosureLaw.bridge ∧
        witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          data.toMicroscopicClosureLaw.physicalPrinciple ∧
        Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
        Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
        realized_generator_carries_bedrock_law data.sectorLaw.bridge.generator ∧
        AutonomousHorizon
          data.sectorLaw.bridge.selectedBridge.observer.selection.realization.tower
          data.sectorLaw.bridge.selectedBridge.observer.selection.horizon
          data.sectorLaw.bridge.generator ∧
        horizonFiberInvariant
          data.sectorLaw.bridge.selectedBridge.observer.selection.realization.tower
          data.sectorLaw.bridge.selectedBridge.observer.selection.horizon
          data.sectorLaw.bridge.generator ∧
        PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion := by
  obtain ⟨hbundle, hsector, hbedrock, haut, hfiber, _hgenmin, _hprofile⟩ :=
    data.sectorTargetSurface
  rcases data.completionTargetSurface with ⟨witness, hbridge, hprinciple, hcompletion⟩
  exact
    ⟨witness,
      hbridge,
      hprinciple,
      hbundle,
      hsector,
      hbedrock,
      haut,
      hfiber,
      hcompletion⟩

end NoStageCompletionBridge

namespace FourStateAssembly

/-- Reassemble the previous split completion bridge from one fixed constructive
sector law, one explicit four-state assembly on that law, and one aligned Step
4 datum above that same law-native intrinsic sector generation. -/
def toNoStageCompletionBridge
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    (assembly : FourStateAssembly sectorLaw)
    (alignment : CompletionAlignment sectorLaw) :
    NoStageCompletionBridge Index Time Carrier Law where
  sectorLaw := sectorLaw
  readout := assembly.readout
  frame := assembly.frame
  exactifier_realized := assembly.exactifier_realized
  completion := alignment.toNaturalOperatorCompletion
  sameSelectedSelection := alignment.sameSelectedSelection
  samePhysicalPrinciple := alignment.samePhysicalPrinciple

end FourStateAssembly

namespace ConstructiveSectorLaw

/-- A fixed current-side readout package together with its exactifier
realization already realizes the four-state assembly target above one
constructive sector law. -/
theorem fourStateAssemblyTargetOfParts
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law)
    (readout : FourStateReadout sectorLaw)
    (hexact : ExactifierRealizationTarget readout) :
    FourStateAssemblyTarget sectorLaw := by
  exact readout.assemblyTargetOfExactifierTarget hexact

/-- The two smaller Step 4 existence targets above one fixed constructive
sector law already realize the aligned completion target. Carrier
classification is recovered from the canonical representatives. -/
theorem completionAlignmentTargetOfParts
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law)
    (hrigidity : CompletionRigidityTarget sectorLaw)
    (hrepresentatives : CanonicalRepresentativeTarget sectorLaw) :
    CompletionAlignmentTarget sectorLaw := by
  rcases hrigidity with ⟨rigidity⟩
  rcases hrepresentatives with ⟨representatives⟩
  exact ⟨CompletionAlignment.ofParts rigidity representatives⟩

/-- Once the canonical representatives are supplied, carrier classification is
already forced. So the aligned completion target only needs the law-native
rigidity target together with the canonical representative target as
independent Step 4 input. -/
theorem completionAlignmentTargetOfRigidityAndRepresentatives
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law)
    (hrigidity : CompletionRigidityTarget sectorLaw)
    (hrepresentatives : CanonicalRepresentativeTarget sectorLaw) :
    CompletionAlignmentTarget sectorLaw := by
  exact
    sectorLaw.completionAlignmentTargetOfParts
      hrigidity
      hrepresentatives

/-- A fixed constructive sector law together with one explicit four-state
assembly and one aligned Step 4 completion datum already realizes the smaller
split completion target above its proposition-level microscopic law. -/
theorem completionSplitTarget
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law)
    (assembly : FourStateAssembly sectorLaw)
    (alignment : CompletionAlignment sectorLaw) :
    CompletionSplitTarget sectorLaw.toMicroscopicClosureLaw := by
  exact
    ⟨{ sectorLaw := sectorLaw
       sameLaw := rfl
       readout := assembly.toFourStateReadout
       exactifierRealized := assembly.exactifier_realized
       rigidity := alignment.rigidityTarget
       representatives := alignment.canonicalRepresentativeTarget }⟩

/-- The two smaller completion-side existence targets above one fixed
constructive sector law already realize the smaller split completion target. -/
theorem completionSplitTargetOfTargets
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law)
    (hasAssembly : FourStateAssemblyTarget sectorLaw)
    (hasAlignment : CompletionAlignmentTarget sectorLaw) :
    CompletionSplitTarget sectorLaw.toMicroscopicClosureLaw := by
  rcases hasAssembly with ⟨assembly⟩
  rcases hasAlignment with ⟨alignment⟩
  exact sectorLaw.completionSplitTarget assembly alignment

/-- One fixed current-side readout package together with its exactifier
realization, plus the two smaller Step 4 existence targets, already realize
the smaller split completion target above the same constructive sector law. -/
theorem completionSplitTargetOfSplitData
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law)
    (readout : FourStateReadout sectorLaw)
    (hexact : ExactifierRealizationTarget readout)
    (hrigidity : CompletionRigidityTarget sectorLaw)
    (hrepresentatives : CanonicalRepresentativeTarget sectorLaw) :
    CompletionSplitTarget sectorLaw.toMicroscopicClosureLaw := by
  have hasAssembly : FourStateAssemblyTarget sectorLaw :=
    sectorLaw.fourStateAssemblyTargetOfParts readout hexact
  have hasAlignment : CompletionAlignmentTarget sectorLaw :=
    sectorLaw.completionAlignmentTargetOfParts
      hrigidity hrepresentatives
  exact sectorLaw.completionSplitTargetOfTargets hasAssembly hasAlignment

/-- Once the canonical representatives are supplied, the fixed current-side
readout package and the law-native rigidity target already suffice for the
smaller split completion target. -/
theorem completionSplitTargetOfRigidityAndRepresentatives
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law)
    (readout : FourStateReadout sectorLaw)
    (hexact : ExactifierRealizationTarget readout)
    (hrigidity : CompletionRigidityTarget sectorLaw)
    (hrepresentatives : CanonicalRepresentativeTarget sectorLaw) :
    CompletionSplitTarget sectorLaw.toMicroscopicClosureLaw := by
  have hasAlignment : CompletionAlignmentTarget sectorLaw :=
    sectorLaw.completionAlignmentTargetOfRigidityAndRepresentatives
      hrigidity
      hrepresentatives
  have hasAssembly : FourStateAssemblyTarget sectorLaw :=
    sectorLaw.fourStateAssemblyTargetOfParts readout hexact
  exact sectorLaw.completionSplitTargetOfTargets hasAssembly hasAlignment

/-- A fixed constructive sector law together with one explicit four-state
assembly and one aligned Step 4 completion datum already realizes the exact
split completion-bridge target above its proposition-level microscopic law. -/
theorem completionBridgeTarget
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law)
    (assembly : FourStateAssembly sectorLaw)
    (alignment : CompletionAlignment sectorLaw) :
    NoStageCompletionBridgeTarget sectorLaw.toMicroscopicClosureLaw := by
  exact ⟨assembly.toNoStageCompletionBridge alignment, rfl⟩

/-- The two smaller completion-side existence targets above one fixed
constructive sector law already realize the split completion-bridge target. -/
theorem completionBridgeTargetOfTargets
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law)
    (hasAssembly : FourStateAssemblyTarget sectorLaw)
    (hasAlignment : CompletionAlignmentTarget sectorLaw) :
    NoStageCompletionBridgeTarget sectorLaw.toMicroscopicClosureLaw := by
  rcases hasAssembly with ⟨assembly⟩
  rcases hasAlignment with ⟨alignment⟩
  exact sectorLaw.completionBridgeTarget assembly alignment

/-- One fixed current-side readout package together with its exactifier
realization, plus the two smaller Step 4 existence targets, already realize
the split completion-bridge target above the same constructive sector law. -/
theorem completionBridgeTargetOfSplitData
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law)
    (readout : FourStateReadout sectorLaw)
    (hexact : ExactifierRealizationTarget readout)
    (hrigidity : CompletionRigidityTarget sectorLaw)
    (hrepresentatives : CanonicalRepresentativeTarget sectorLaw) :
    NoStageCompletionBridgeTarget sectorLaw.toMicroscopicClosureLaw := by
  have hasAssembly : FourStateAssemblyTarget sectorLaw :=
    sectorLaw.fourStateAssemblyTargetOfParts readout hexact
  have hasAlignment : CompletionAlignmentTarget sectorLaw :=
    sectorLaw.completionAlignmentTargetOfParts
      hrigidity hrepresentatives
  exact sectorLaw.completionBridgeTargetOfTargets hasAssembly hasAlignment

/-- Once the canonical representatives are supplied, the fixed current-side
readout package and the law-native rigidity target already suffice for the
split completion-bridge target. -/
theorem completionBridgeTargetOfRigidityAndRepresentatives
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law)
    (readout : FourStateReadout sectorLaw)
    (hexact : ExactifierRealizationTarget readout)
    (hrigidity : CompletionRigidityTarget sectorLaw)
    (hrepresentatives : CanonicalRepresentativeTarget sectorLaw) :
    NoStageCompletionBridgeTarget sectorLaw.toMicroscopicClosureLaw := by
  have hasAlignment : CompletionAlignmentTarget sectorLaw :=
    sectorLaw.completionAlignmentTargetOfRigidityAndRepresentatives
      hrigidity
      hrepresentatives
  have hasAssembly : FourStateAssemblyTarget sectorLaw :=
    sectorLaw.fourStateAssemblyTargetOfParts readout hexact
  exact sectorLaw.completionBridgeTargetOfTargets hasAssembly hasAlignment

/-- A fixed constructive sector law together with one explicit four-state
assembly and one aligned Step 4 completion datum already realizes the no-stage
completion target above its proposition-level microscopic law. -/
theorem completionTarget
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law)
    (assembly : FourStateAssembly sectorLaw)
    (alignment : CompletionAlignment sectorLaw) :
    NoStageCompletionTarget sectorLaw.toMicroscopicClosureLaw := by
  rcases sectorLaw.completionSplitTarget assembly alignment with ⟨data⟩
  have hbridge :=
    data.sectorLaw.completionBridgeTargetOfRigidityAndRepresentatives
      data.readout
      data.exactifierRealized
      data.rigidity
      data.representatives
  rw [data.sameLaw] at hbridge
  rcases hbridge with ⟨bridge, hEq⟩
  have hEq' : bridge.toMicroscopicClosureLaw = sectorLaw.toMicroscopicClosureLaw := hEq
  exact hEq' ▸ bridge.completionTarget

/-- The two smaller completion-side existence targets above one fixed
constructive sector law already realize the no-stage completion target. -/
theorem completionTargetOfTargets
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law)
    (hasAssembly : FourStateAssemblyTarget sectorLaw)
    (hasAlignment : CompletionAlignmentTarget sectorLaw) :
    NoStageCompletionTarget sectorLaw.toMicroscopicClosureLaw := by
  rcases sectorLaw.completionSplitTargetOfTargets hasAssembly hasAlignment with ⟨data⟩
  have hbridge :=
    data.sectorLaw.completionBridgeTargetOfRigidityAndRepresentatives
      data.readout
      data.exactifierRealized
      data.rigidity
      data.representatives
  rw [data.sameLaw] at hbridge
  rcases hbridge with ⟨bridge, hEq⟩
  have hEq' : bridge.toMicroscopicClosureLaw = sectorLaw.toMicroscopicClosureLaw := hEq
  exact hEq' ▸ bridge.completionTarget

/-- One fixed current-side readout package together with its exactifier
realization, plus the two smaller Step 4 existence targets, already realize
the no-stage completion target above the same constructive sector law. -/
theorem completionTargetOfSplitData
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law)
    (readout : FourStateReadout sectorLaw)
    (hexact : ExactifierRealizationTarget readout)
    (hrigidity : CompletionRigidityTarget sectorLaw)
    (hrepresentatives : CanonicalRepresentativeTarget sectorLaw) :
    NoStageCompletionTarget sectorLaw.toMicroscopicClosureLaw := by
  rcases
      sectorLaw.completionSplitTargetOfSplitData
        readout hexact hrigidity hrepresentatives with
    ⟨data⟩
  have hbridge :=
    data.sectorLaw.completionBridgeTargetOfRigidityAndRepresentatives
      data.readout
      data.exactifierRealized
      data.rigidity
      data.representatives
  rw [data.sameLaw] at hbridge
  rcases hbridge with ⟨bridge, hEq⟩
  have hEq' : bridge.toMicroscopicClosureLaw = sectorLaw.toMicroscopicClosureLaw := hEq
  exact hEq' ▸ bridge.completionTarget

/-- Once the canonical representatives are supplied, the fixed current-side
readout package and the law-native rigidity target already suffice for the
no-stage completion target. -/
theorem completionTargetOfRigidityAndRepresentatives
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law)
    (readout : FourStateReadout sectorLaw)
    (hexact : ExactifierRealizationTarget readout)
    (hrigidity : CompletionRigidityTarget sectorLaw)
    (hrepresentatives : CanonicalRepresentativeTarget sectorLaw) :
    NoStageCompletionTarget sectorLaw.toMicroscopicClosureLaw := by
  have hasAlignment : CompletionAlignmentTarget sectorLaw :=
    sectorLaw.completionAlignmentTargetOfRigidityAndRepresentatives
      hrigidity
      hrepresentatives
  have hasAssembly : FourStateAssemblyTarget sectorLaw :=
    sectorLaw.fourStateAssemblyTargetOfParts readout hexact
  exact sectorLaw.completionTargetOfTargets hasAssembly hasAlignment

/-- The active Part IV completion surface already follows from the smaller
completion-side supplement above one fixed constructive sector law: an explicit
four-state assembly and one aligned Step 4 completion datum. -/
theorem completionBridgeTargetSurface
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law)
    (assembly : FourStateAssembly sectorLaw)
    (alignment : CompletionAlignment sectorLaw) :
    ∃ witness : NoStageCompletionWitness sectorLaw.toMicroscopicClosureLaw,
      witness.completionLaw.fourStateLaw.framed.object.bridge =
          sectorLaw.toMicroscopicClosureLaw.bridge ∧
        witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          sectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
        PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion := by
  exact
    (assembly.toNoStageCompletionBridge alignment).completionTargetSurface

/-- The active Part IV completion surface already follows from the two smaller
completion-side existence targets above one fixed constructive sector law. -/
theorem completionBridgeTargetSurfaceOfTargets
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law)
    (hasAssembly : FourStateAssemblyTarget sectorLaw)
    (hasAlignment : CompletionAlignmentTarget sectorLaw) :
    ∃ witness : NoStageCompletionWitness sectorLaw.toMicroscopicClosureLaw,
      witness.completionLaw.fourStateLaw.framed.object.bridge =
          sectorLaw.toMicroscopicClosureLaw.bridge ∧
        witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          sectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
        PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion := by
  rcases hasAssembly with ⟨assembly⟩
  rcases hasAlignment with ⟨alignment⟩
  exact sectorLaw.completionBridgeTargetSurface assembly alignment

/-- The active Part IV completion surface already follows directly from the
smaller completion-side supplement above one fixed constructive sector law: an
explicit four-state assembly and one aligned Step 4 completion datum. -/
theorem completionTargetSurface
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law)
    (assembly : FourStateAssembly sectorLaw)
    (alignment : CompletionAlignment sectorLaw) :
    ∃ witness : NoStageCompletionWitness sectorLaw.toMicroscopicClosureLaw,
      witness.completionLaw.fourStateLaw.framed.object.bridge =
          sectorLaw.toMicroscopicClosureLaw.bridge ∧
        witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          sectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
        PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion := by
  rcases sectorLaw.completionSplitTarget assembly alignment with ⟨data⟩
  have hbridge :=
    data.sectorLaw.completionBridgeTargetOfRigidityAndRepresentatives
      data.readout
      data.exactifierRealized
      data.rigidity
      data.representatives
  rw [data.sameLaw] at hbridge
  rcases hbridge with ⟨bridge, hEq⟩
  have hEq' : bridge.toMicroscopicClosureLaw = sectorLaw.toMicroscopicClosureLaw := hEq
  exact hEq' ▸ bridge.completionTargetSurface

/-- The active Part IV completion surface already follows directly from the
two smaller completion-side existence targets above one fixed constructive
sector law. -/
theorem completionTargetSurfaceOfTargets
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law)
    (hasAssembly : FourStateAssemblyTarget sectorLaw)
    (hasAlignment : CompletionAlignmentTarget sectorLaw) :
    ∃ witness : NoStageCompletionWitness sectorLaw.toMicroscopicClosureLaw,
      witness.completionLaw.fourStateLaw.framed.object.bridge =
          sectorLaw.toMicroscopicClosureLaw.bridge ∧
        witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          sectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
        PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion := by
  rcases sectorLaw.completionSplitTargetOfTargets hasAssembly hasAlignment with ⟨data⟩
  have hbridge :=
    data.sectorLaw.completionBridgeTargetOfRigidityAndRepresentatives
      data.readout
      data.exactifierRealized
      data.rigidity
      data.representatives
  rw [data.sameLaw] at hbridge
  rcases hbridge with ⟨bridge, hEq⟩
  have hEq' : bridge.toMicroscopicClosureLaw = sectorLaw.toMicroscopicClosureLaw := hEq
  exact hEq' ▸ bridge.completionTargetSurface

/-- The active Part IV completion surface already follows from one fixed
current-side readout package with its exactifier realization, plus the two
smaller Step 4 existence targets above one fixed constructive sector law. -/
theorem completionBridgeTargetSurfaceOfSplitData
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law)
    (readout : FourStateReadout sectorLaw)
    (hexact : ExactifierRealizationTarget readout)
    (hrigidity : CompletionRigidityTarget sectorLaw)
    (hrepresentatives : CanonicalRepresentativeTarget sectorLaw) :
    ∃ witness : NoStageCompletionWitness sectorLaw.toMicroscopicClosureLaw,
      witness.completionLaw.fourStateLaw.framed.object.bridge =
          sectorLaw.toMicroscopicClosureLaw.bridge ∧
      witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          sectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
        PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion := by
  have hasAssembly : FourStateAssemblyTarget sectorLaw :=
    sectorLaw.fourStateAssemblyTargetOfParts readout hexact
  have hasAlignment : CompletionAlignmentTarget sectorLaw :=
    sectorLaw.completionAlignmentTargetOfParts
      hrigidity hrepresentatives
  exact
    sectorLaw.completionBridgeTargetSurfaceOfTargets
      hasAssembly hasAlignment

/-- The active Part IV completion surface already follows directly from one
fixed current-side readout package with its exactifier realization, plus the
two smaller Step 4 existence targets above one fixed constructive sector
law. -/
theorem completionTargetSurfaceOfSplitData
    {Index Time Carrier Law : Type}
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law)
    (readout : FourStateReadout sectorLaw)
    (hexact : ExactifierRealizationTarget readout)
    (hrigidity : CompletionRigidityTarget sectorLaw)
    (hrepresentatives : CanonicalRepresentativeTarget sectorLaw) :
    ∃ witness : NoStageCompletionWitness sectorLaw.toMicroscopicClosureLaw,
      witness.completionLaw.fourStateLaw.framed.object.bridge =
          sectorLaw.toMicroscopicClosureLaw.bridge ∧
      witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          sectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
        PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion := by
  rcases
      sectorLaw.completionSplitTargetOfSplitData
        readout hexact hrigidity hrepresentatives with
    ⟨data⟩
  have hbridge :=
    data.sectorLaw.completionBridgeTargetOfRigidityAndRepresentatives
      data.readout
      data.exactifierRealized
      data.rigidity
      data.representatives
  rw [data.sameLaw] at hbridge
  rcases hbridge with ⟨bridge, hEq⟩
  have hEq' : bridge.toMicroscopicClosureLaw = sectorLaw.toMicroscopicClosureLaw := hEq
  exact hEq' ▸ bridge.completionTargetSurface

end ConstructiveSectorLaw

namespace CompletionSplitWitness

/-- A split completion witness already yields the exact split completion-bridge
target above its microscopic law. -/
theorem bridgeTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : CompletionSplitWitness law) :
    NoStageCompletionBridgeTarget law := by
  rw [← data.sameLaw]
  exact
    data.sectorLaw.completionBridgeTargetOfRigidityAndRepresentatives
      data.readout
      data.exactifierRealized
      data.rigidity
      data.representatives

/-- The split completion-bridge surface already follows from a split
completion witness. -/
theorem bridgeTargetSurface
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : CompletionSplitWitness law) :
    ∃ witness : NoStageCompletionWitness law,
      witness.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
        witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          law.physicalPrinciple ∧
        PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion := by
  rcases data.bridgeTarget with ⟨bridge, rfl⟩
  exact bridge.completionTargetSurface

/-- A split completion witness already yields the no-stage completion target
above its microscopic law. -/
theorem completionTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : CompletionSplitWitness law) :
    NoStageCompletionTarget law := by
  rcases data.bridgeTarget with ⟨bridge, rfl⟩
  exact bridge.completionTarget

/-- The no-stage completion surface already follows from a split completion
witness. -/
theorem completionTargetSurface
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : CompletionSplitWitness law) :
    ∃ witness : NoStageCompletionWitness law,
      witness.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
        witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          law.physicalPrinciple ∧
        PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion := by
  rcases data.bridgeTarget with ⟨bridge, rfl⟩
  exact bridge.completionTargetSurface

end CompletionSplitWitness

/-- Once the exact split completion-bridge target is met for `law`, the
assembled no-stage completion witness target is already met as well. -/
theorem MicroscopicClosureLaw.completionTargetOfBridge
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hbridge : NoStageCompletionBridgeTarget law) :
    NoStageCompletionTarget law := by
  rcases hbridge with ⟨data, rfl⟩
  exact ⟨data.toNoStageCompletionWitness⟩

/-- If the exact split completion-bridge target is met for a microscopic
closure law, then the active Part IV completion surface follows immediately. -/
theorem MicroscopicClosureLaw.completionBridgeTargetSurface
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hbridge : NoStageCompletionBridgeTarget law) :
    ∃ witness : NoStageCompletionWitness law,
      witness.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
        witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          law.physicalPrinciple ∧
        PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion := by
  exact law.completionTargetSurface (law.completionTargetOfBridge hbridge)

/-- The smaller split completion target above a microscopic closure law
already yields the exact split completion-bridge target. -/
theorem MicroscopicClosureLaw.completionBridgeTargetOfSplitTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hsplit : CompletionSplitTarget law) :
    NoStageCompletionBridgeTarget law := by
  rcases hsplit with ⟨data⟩
  exact data.bridgeTarget

/-- The smaller split completion target above a microscopic closure law
already yields the no-stage completion target. -/
theorem MicroscopicClosureLaw.completionTargetOfSplitTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hsplit : CompletionSplitTarget law) :
    NoStageCompletionTarget law := by
  rcases hsplit with ⟨data⟩
  exact data.completionTarget

/-- If the smaller split completion target is met for a microscopic closure
law, then the split completion-bridge surface already follows immediately. -/
theorem MicroscopicClosureLaw.completionBridgeTargetSurfaceOfSplitTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hsplit : CompletionSplitTarget law) :
    ∃ witness : NoStageCompletionWitness law,
      witness.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
        witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          law.physicalPrinciple ∧
        PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion := by
  rcases hsplit with ⟨data⟩
  exact data.bridgeTargetSurface

/-- If the smaller split completion target is met for a microscopic closure
law, then the no-stage completion surface already follows immediately. -/
theorem MicroscopicClosureLaw.completionTargetSurfaceOfSplitTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hsplit : CompletionSplitTarget law) :
    ∃ witness : NoStageCompletionWitness law,
      witness.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
        witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          law.physicalPrinciple ∧
        PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion := by
  rcases hsplit with ⟨data⟩
  exact data.completionTargetSurface

end ClosureCurrent

end CoherenceCalculus
