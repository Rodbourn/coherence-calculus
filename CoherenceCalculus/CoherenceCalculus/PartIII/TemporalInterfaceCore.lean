import CoherenceCalculus.Foundation.BridgeRigidityCorollaryCore
import CoherenceCalculus.Foundation.ClosureBalanceCore
import CoherenceCalculus.Foundation.ClosureCore
import CoherenceCalculus.PartIII.ClassicalLimitCore
import CoherenceCalculus.PartIII.ContinuumIdentificationCore

namespace CoherenceCalculus

/-- On a faithful bridge, the returned residual is not a new permanent source:
its visible contribution is exactly the projection-side defect, and both that
defect and the unrecovered part vanish in the faithful limit on the recovered
domain. -/
theorem faithful_limit_returned_residual
    {H : Type}
    (data : ResidualReturnRecoveryData H) :
    (∀ x : H, data.recovery.domain x →
      data.recovery.limits.tendsTo
        (fun h => data.returnedResidual h x)
        data.recovery.zero) ∧
      (∀ x : H, data.recovery.domain x →
        data.recovery.limits.tendsTo
          (fun h => data.unrecoveredResidual h x)
          data.recovery.zero) := by
  refine ⟨?_, data.unrecoveredResidual_vanishes⟩
  intro x hx
  have hdefect :
      data.recovery.limits.tendsTo
        (fun h => data.recovery.defect h x)
        data.recovery.zero :=
    data.recovery.defect_vanishes x hx
  apply
    (data.recovery.limits.congr
      (f := fun h => data.recovery.defect h x)
      (g := fun h => data.returnedResidual h x))
  · intro h
    exact data.forcing_is_returnedResidual h x
  · exact hdefect

/-- Part III endcap: the residual `D = 3` localization, scalar-recursive
selected transport, and singleton continuum forcing determine one internal
ordering interface, prior to any Part IV physical-time identification. -/
structure TemporalInterfaceDatum
    (F : RefinementCompatibleFamily) (Time Vertex X₀ X : Type) where
  anchoredToCanonicalClosureBalance : Prop
  anchoredToCanonicalClosureBalance_valid :
    anchoredToCanonicalClosureBalance
  residualInterfaceDimension : Nat
  residualInterface_is_D3 : residualInterfaceDimension = 3
  residualInterfaceLocalized :
    holographicImbalance residualInterfaceDimension = SignedCount.ofNat 1
  selectedChannel : ScalarRecursiveSelectedChannelSystem Time Vertex
  selectedChannel_scalar_quadratic_transport_law_valid :
    selectedChannel.scalar_quadratic_transport_law
  selectedChannel_recursive_transport_law_valid :
    selectedChannel.recursive_transport_law
  reconstruction : ContinuumReconstructionDatum F.family X₀ X
  continuumClass : ContinuumLimitClass (X₀ → X)
  continuumLaw : X₀ → X
  continuumLaw_mem : continuumClass.admissible continuumLaw
  asymptoticallyConsistent :
    AsymptoticConsistency F.family reconstruction continuumLaw
  uniqueContinuumLaw :
    ∀ other : X₀ → X, continuumClass.admissible other → other = continuumLaw

/-- Residual `D = 3` localization, transport-generated scalar recursion, and a
singleton continuum limit class furnish a unique temporal interface datum. -/
def temporalInterfaceDatum
    {Time Vertex X₀ X : Type}
    (F : RefinementCompatibleFamily)
    (selected : TransportGeneratedScalarRecursiveData Time Vertex)
    (reconstruction : ContinuumReconstructionDatum F.family X₀ X)
    (continuumClass : ContinuumLimitClass (X₀ → X))
    (continuumLaw : X₀ → X)
    (anchoredToCanonicalClosureBalance : Prop)
    (hanchored : anchoredToCanonicalClosureBalance)
    (hscalar : selected.scalarQuadraticTransportLaw)
    (hrecursiveLaw : selected.recursiveTransportLaw)
    (hmem : continuumClass.admissible continuumLaw)
    (hcons :
      AsymptoticConsistency F.family reconstruction continuumLaw)
    (hunique :
      ∀ other : X₀ → X, continuumClass.admissible other → other = continuumLaw) :
    TemporalInterfaceDatum F Time Vertex X₀ X := by
  refine {
    anchoredToCanonicalClosureBalance := anchoredToCanonicalClosureBalance
    anchoredToCanonicalClosureBalance_valid := hanchored
    residualInterfaceDimension := 3
    residualInterface_is_D3 := rfl
    residualInterfaceLocalized := ?_
    selectedChannel :=
      { system := selected.system
        channel := selected.channel
        transportBase := selected.transportBase
        scalar_quadratic_transport_law := selected.scalarQuadraticTransportLaw
        recursive_transport_law := selected.recursiveTransportLaw }
    selectedChannel_scalar_quadratic_transport_law_valid := hscalar
    selectedChannel_recursive_transport_law_valid := hrecursiveLaw
    reconstruction := reconstruction
    continuumClass := continuumClass
    continuumLaw := continuumLaw
    continuumLaw_mem := hmem
    asymptoticallyConsistent := hcons
    uniqueContinuumLaw := hunique
  }
  simpa using finite_local_type_profiles.1

/-- The temporal interface datum keeps exactly the anchored bridge clause, the
`D = 3` localization, the selected transport laws, and the chosen continuum
law data used to build it. -/
theorem temporalInterfaceSurface
    {Time Vertex X₀ X : Type}
    (F : RefinementCompatibleFamily)
    (selected : TransportGeneratedScalarRecursiveData Time Vertex)
    (reconstruction : ContinuumReconstructionDatum F.family X₀ X)
    (continuumClass : ContinuumLimitClass (X₀ → X))
    (continuumLaw : X₀ → X)
    (anchoredToCanonicalClosureBalance : Prop)
    (hanchored : anchoredToCanonicalClosureBalance)
    (hscalar : selected.scalarQuadraticTransportLaw)
    (hrecursiveLaw : selected.recursiveTransportLaw)
    (hmem : continuumClass.admissible continuumLaw)
    (hcons :
      AsymptoticConsistency F.family reconstruction continuumLaw)
    (hunique :
      ∀ other : X₀ → X, continuumClass.admissible other → other = continuumLaw) :
    (temporalInterfaceDatum F selected reconstruction continuumClass continuumLaw
      anchoredToCanonicalClosureBalance hanchored hscalar hrecursiveLaw hmem
      hcons hunique).anchoredToCanonicalClosureBalance =
        anchoredToCanonicalClosureBalance ∧
      (temporalInterfaceDatum F selected reconstruction continuumClass continuumLaw
        anchoredToCanonicalClosureBalance hanchored hscalar hrecursiveLaw hmem
        hcons hunique).residualInterfaceDimension = 3 ∧
      (temporalInterfaceDatum F selected reconstruction continuumClass continuumLaw
        anchoredToCanonicalClosureBalance hanchored hscalar hrecursiveLaw hmem
        hcons hunique).selectedChannel.scalar_quadratic_transport_law =
          selected.scalarQuadraticTransportLaw ∧
      (temporalInterfaceDatum F selected reconstruction continuumClass continuumLaw
        anchoredToCanonicalClosureBalance hanchored hscalar hrecursiveLaw hmem
        hcons hunique).selectedChannel.recursive_transport_law =
          selected.recursiveTransportLaw ∧
      (temporalInterfaceDatum F selected reconstruction continuumClass continuumLaw
        anchoredToCanonicalClosureBalance hanchored hscalar hrecursiveLaw hmem
        hcons hunique).continuumLaw = continuumLaw := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Residual `D = 3` localization, transport-generated scalar recursion, and a
singleton continuum limit class furnish a unique temporal interface datum. -/
theorem temporal_interface_from_d3
    {Time Vertex X₀ X : Type}
    (F : RefinementCompatibleFamily)
    (selected : TransportGeneratedScalarRecursiveData Time Vertex)
    (reconstruction : ContinuumReconstructionDatum F.family X₀ X)
    (continuumClass : ContinuumLimitClass (X₀ → X))
    (continuumLaw : X₀ → X)
    (anchoredToCanonicalClosureBalance : Prop)
    (hanchored : anchoredToCanonicalClosureBalance)
    (hscalar : selected.scalarQuadraticTransportLaw)
    (hrecursiveLaw : selected.recursiveTransportLaw)
    (hmem : continuumClass.admissible continuumLaw)
    (hcons :
      AsymptoticConsistency F.family reconstruction continuumLaw)
    (hunique :
      ∀ other : X₀ → X, continuumClass.admissible other → other = continuumLaw) :
    Nonempty (TemporalInterfaceDatum F Time Vertex X₀ X) := by
  exact
    ⟨temporalInterfaceDatum
      F selected reconstruction continuumClass continuumLaw
      anchoredToCanonicalClosureBalance hanchored hscalar hrecursiveLaw hmem
      hcons hunique⟩

/-- Part III forces the structural temporal interface `(D = 3, [Θ])`. The
later identification of that interface with physical causal time lies beyond
this bridge lane. -/
theorem temporalInterfaceAnchorSurface
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : TemporalInterfaceDatum F Time Vertex X₀ X) :
    data.anchoredToCanonicalClosureBalance ∧
      (data.residualInterfaceDimension = 3) := by
  exact
    ⟨data.anchoredToCanonicalClosureBalance_valid,
      data.residualInterface_is_D3⟩

theorem temporalInterfaceAnchoredSurface
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : TemporalInterfaceDatum F Time Vertex X₀ X) :
    data.anchoredToCanonicalClosureBalance := by
  exact (temporalInterfaceAnchorSurface data).1

theorem temporalInterfaceDimensionSurface
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : TemporalInterfaceDatum F Time Vertex X₀ X) :
    data.residualInterfaceDimension = 3 := by
  exact (temporalInterfaceAnchorSurface data).2

theorem temporalInterfaceScalarSurface
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : TemporalInterfaceDatum F Time Vertex X₀ X) :
    data.selectedChannel.scalar_quadratic_transport_law := by
  exact data.selectedChannel_scalar_quadratic_transport_law_valid

theorem temporalInterfaceRecursiveSurface
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : TemporalInterfaceDatum F Time Vertex X₀ X) :
    data.selectedChannel.recursive_transport_law := by
  exact data.selectedChannel_recursive_transport_law_valid

/-- Part III also fixes the selected transport laws carried by the temporal
interface before any Part IV physical interpretation is added. -/
theorem temporalInterfaceTransportSurface
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : TemporalInterfaceDatum F Time Vertex X₀ X) :
    data.selectedChannel.scalar_quadratic_transport_law ∧
      data.selectedChannel.recursive_transport_law := by
  exact
    ⟨temporalInterfaceScalarSurface data,
      temporalInterfaceRecursiveSurface data⟩

/-- Part III forces the structural temporal interface `(D = 3, [Θ])`. The
later identification of that interface with physical causal time lies beyond
this bridge lane. -/
theorem temporalInterfaceStructuralSurface
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : TemporalInterfaceDatum F Time Vertex X₀ X) :
    data.anchoredToCanonicalClosureBalance ∧
      (data.residualInterfaceDimension = 3) ∧
      data.selectedChannel.scalar_quadratic_transport_law ∧
      data.selectedChannel.recursive_transport_law := by
  exact
    ⟨temporalInterfaceAnchoredSurface data,
      temporalInterfaceDimensionSurface data,
      temporalInterfaceScalarSurface data,
      temporalInterfaceRecursiveSurface data⟩

/-- The temporal interface already carries a forced continuum law on its limit
class. -/
theorem temporalInterfaceForcedContinuumLaw
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : TemporalInterfaceDatum F Time Vertex X₀ X) :
    ForcedContinuumLaw data.continuumClass data.continuumLaw := by
  exact
    discrete_to_continuum_forcing_principle
      data.continuumClass
      data.continuumLaw
      data.continuumLaw_mem
      data.uniqueContinuumLaw

/-- Manuscript-facing generator-identification surface: once the temporal
interface datum is in hand, the selected scalar recursion is already tied to
one forced continuum law on the same interface. -/
theorem scalar_recursion_identifies_continuum_generator
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : TemporalInterfaceDatum F Time Vertex X₀ X) :
    data.selectedChannel.scalar_quadratic_transport_law ∧
      data.selectedChannel.recursive_transport_law ∧
      ForcedContinuumLaw data.continuumClass data.continuumLaw := by
  exact
    ⟨temporalInterfaceScalarSurface data,
      temporalInterfaceRecursiveSurface data,
      temporalInterfaceForcedContinuumLaw data⟩

/-- Manuscript-facing exact-recursive-transport name for the existing temporal
interface construction. The active import-free bridge certifies this as the
unique temporal-interface datum built from the selected transport system, the
common reconstruction datum, and a singleton continuum limit class. -/
theorem exact_recursive_transport_yields_temporal_interface
    {Time Vertex X₀ X : Type}
    (F : RefinementCompatibleFamily)
    (selected : TransportGeneratedScalarRecursiveData Time Vertex)
    (reconstruction : ContinuumReconstructionDatum F.family X₀ X)
    (continuumClass : ContinuumLimitClass (X₀ → X))
    (continuumLaw : X₀ → X)
    (anchoredToCanonicalClosureBalance : Prop)
    (hanchored : anchoredToCanonicalClosureBalance)
    (hscalar : selected.scalarQuadraticTransportLaw)
    (hrecursiveLaw : selected.recursiveTransportLaw)
    (hmem : continuumClass.admissible continuumLaw)
    (hcons :
      AsymptoticConsistency F.family reconstruction continuumLaw)
    (hunique :
      ∀ other : X₀ → X, continuumClass.admissible other → other = continuumLaw) :
    Nonempty (TemporalInterfaceDatum F Time Vertex X₀ X) := by
  exact
    temporal_interface_from_d3
      F selected reconstruction continuumClass continuumLaw
      anchoredToCanonicalClosureBalance hanchored hscalar hrecursiveLaw hmem
      hcons hunique

/-- Persistent exactification on the unique residual `D = 3` carrier already
forces a temporal-interface datum. This is the manuscript-facing bridge from
the minimal nonterminal carrier to ordered persistence before any Part IV
physical reading is added. -/
theorem persistent_exactification_yields_temporal_interface
    {Time Vertex X₀ X : Type}
    (F : RefinementCompatibleFamily)
    (selected : TransportGeneratedScalarRecursiveData Time Vertex)
    (reconstruction : ContinuumReconstructionDatum F.family X₀ X)
    (continuumClass : ContinuumLimitClass (X₀ → X))
    (continuumLaw : X₀ → X)
    (anchoredToCanonicalClosureBalance : Prop)
    (hanchored : anchoredToCanonicalClosureBalance)
    (hscalar : selected.scalarQuadraticTransportLaw)
    (hrecursiveLaw : selected.recursiveTransportLaw)
    (hmem : continuumClass.admissible continuumLaw)
    (hcons :
      AsymptoticConsistency F.family reconstruction continuumLaw)
    (hunique :
      ∀ other : X₀ → X, continuumClass.admissible other → other = continuumLaw) :
    ∃ data : TemporalInterfaceDatum F Time Vertex X₀ X,
      data.residualInterfaceDimension = 3 ∧
        data.selectedChannel.recursive_transport_law := by
  refine
    ⟨temporalInterfaceDatum
      F selected reconstruction continuumClass continuumLaw
      anchoredToCanonicalClosureBalance hanchored hscalar hrecursiveLaw hmem
      hcons hunique, ?_, ?_⟩
  · exact
      (temporalInterfaceDatum
        F selected reconstruction continuumClass continuumLaw
        anchoredToCanonicalClosureBalance hanchored hscalar hrecursiveLaw hmem
        hcons hunique).residualInterface_is_D3
  · exact
      (temporalInterfaceDatum
        F selected reconstruction continuumClass continuumLaw
        anchoredToCanonicalClosureBalance hanchored hscalar hrecursiveLaw hmem
        hcons hunique).selectedChannel_recursive_transport_law_valid

/-- On the active import-free bridge, the manuscript's graph-temporal-generator
corollary is used through the same forced continuum-law surface already carried
by the temporal interface datum. -/
theorem exact_recursive_transport_forces_graph_temporal_generator
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : TemporalInterfaceDatum F Time Vertex X₀ X) :
    ForcedContinuumLaw data.continuumClass data.continuumLaw := by
  exact temporalInterfaceForcedContinuumLaw data

/-- Part III forces the structural temporal interface `(D = 3, [Θ])`. The
later identification of that interface with physical causal time lies beyond
this bridge lane. -/
theorem temporal_interface_precedes_physical_time
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : TemporalInterfaceDatum F Time Vertex X₀ X) :
    data.anchoredToCanonicalClosureBalance ∧
      (data.residualInterfaceDimension = 3) ∧
      data.selectedChannel.scalar_quadratic_transport_law ∧
      data.selectedChannel.recursive_transport_law ∧
      ForcedContinuumLaw data.continuumClass data.continuumLaw := by
  have hstruct := temporalInterfaceStructuralSurface data
  rcases hstruct with ⟨hanchored, hdim, hscalar, hrecursive⟩
  exact
    ⟨hanchored,
      hdim,
      hscalar,
      hrecursive,
      temporalInterfaceForcedContinuumLaw data⟩

/-- Upstream mathematical tooling currently available for the selected-
completion route: the structural temporal interface together with the complete
canonical six-slot forcing surface from closure balance. This remains entirely
on the mathematical side, before any Part IV physical-law identification. -/
structure SelectedCompletionTooling
    (F : RefinementCompatibleFamily) (Time Vertex X₀ X : Type) where
  temporal : TemporalInterfaceDatum F Time Vertex X₀ X
  sixSlot : SixSlotForcing

namespace TemporalInterfaceDatum

/-- Any temporal interface datum can be read together with the canonical
six-slot forcing package as the current upstream toolkit for the selected-
completion problem. -/
def toSelectedCompletionTooling
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : TemporalInterfaceDatum F Time Vertex X₀ X) :
    SelectedCompletionTooling F Time Vertex X₀ X where
  temporal := data
  sixSlot := canonicalSixSlotForcing

end TemporalInterfaceDatum

namespace SelectedCompletionTooling

/-- The temporal component keeps the exact anchored structural surface already
carried by the Part III interface. -/
theorem temporalSurface
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : SelectedCompletionTooling F Time Vertex X₀ X) :
    data.temporal.anchoredToCanonicalClosureBalance ∧
      (data.temporal.residualInterfaceDimension = 3) ∧
      data.temporal.selectedChannel.scalar_quadratic_transport_law ∧
      data.temporal.selectedChannel.recursive_transport_law ∧
      ForcedContinuumLaw
        data.temporal.continuumClass
        data.temporal.continuumLaw := by
  exact temporal_interface_precedes_physical_time data.temporal

/-- The carrier component keeps the exact six-slot forcing package already
carried by closure balance. -/
theorem sixSlotSurface
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : SelectedCompletionTooling F Time Vertex X₀ X) :
    balancedClosureSlotCount closureStableDimension = 6 ∧
      (natListSum [3, 2, 1] = balancedClosureSlotCount closureStableDimension) ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  exact
    ⟨data.sixSlot.slotCount,
      data.sixSlot.canonicalProfile.1,
      data.sixSlot.canonicalProfile.2⟩

/-- The six-slot component still carries the unique intrinsic normal-form
surface. -/
theorem uniqueNormalForm
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : SelectedCompletionTooling F Time Vertex X₀ X)
    (A : LocalSlot → LocalSlot → SignedCount)
    (hA : IntrinsicAdjacencyInvariant A) :
    ∃ p : IntrinsicSlotParameters,
        isIntrinsicNormalForm A p ∧
          ∀ q : IntrinsicSlotParameters, isIntrinsicNormalForm A q → q = p := by
  exact data.sixSlot.uniqueNormalForm A hA

/-- On the selected-completion six-slot carrier, a normal form determines the
law pointwise. Once two local laws share the same intrinsic parameter package,
their entries agree slot-by-slot. -/
theorem normalFormRigidity
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : SelectedCompletionTooling F Time Vertex X₀ X)
    {A B : LocalSlot → LocalSlot → SignedCount}
    {p : IntrinsicSlotParameters}
    (hA : isIntrinsicNormalForm A p)
    (hB : isIntrinsicNormalForm B p) :
    ∀ α β : LocalSlot, A α β = B α β := by
  exact data.sixSlot.normalFormRigidity hA hB

/-- The six-slot component still carries exact three-parameter control of
intrinsically equivariant local laws. -/
theorem threeParameterControl
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : SelectedCompletionTooling F Time Vertex X₀ X)
    (A : LocalSlot → LocalSlot → SignedCount)
    (hA : IntrinsicAdjacencyInvariant A) :
    ∃ a b c : SignedCount,
      ∀ α β : LocalSlot,
        A α β =
          match intrinsicSlotAdjacency α β with
          | .equal => a
          | .adjacent => b
          | .disjoint => c := by
  exact data.sixSlot.threeParameterControl A hA

/-- The six-slot component still carries the exact intrinsic channel-eigenvalue
surface. -/
theorem channelEigenvalues
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : SelectedCompletionTooling F Time Vertex X₀ X)
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
        l1 =
          SignedCount.addCount
            (SignedCount.addCount a (signedCount_nsmul 4 b)) c ∧
        l2 =
          SignedCount.addCount
            (SignedCount.subCount a (signedCount_nsmul 2 b)) c ∧
          l3 = SignedCount.subCount a c := by
  exact data.sixSlot.channelEigenvalues A hA

/-- The selected-completion toolkit already carries the canonical overlap law
on the intrinsic six-slot carrier, together with its unique normal form and
the ambient `3+2+1` carrier profile. -/
theorem canonicalOverlapLawSurface
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : SelectedCompletionTooling F Time Vertex X₀ X) :
    balancedClosureSlotCount closureStableDimension = 6 ∧
      (natListSum [3, 2, 1] = balancedClosureSlotCount closureStableDimension) ∧
      IsCanonicalLogicalProfile [3, 2, 1] ∧
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
  exact
    ⟨data.sixSlot.slotCount,
      data.sixSlot.canonicalProfile.1,
      data.sixSlot.canonicalProfile.2,
      canonicalIntrinsicOverlapLaw_existsUniqueCanonicalNormalForm⟩

/-- The selected-completion six-slot tooling therefore recognizes the
canonical overlap law rigidly: any law in canonical normal form `(2, 1, 0)`
is already the intrinsic overlap law. -/
theorem canonicalOverlapLawRigidity
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : SelectedCompletionTooling F Time Vertex X₀ X)
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
  exact data.normalFormRigidity hA canonicalIntrinsicOverlapLaw_normalForm

/-- The selected-completion toolkit also carries the canonical six-slot
coordinate readout: once two local slot carriers agree slot-by-slot, their
reduced three-coordinate readouts agree as well. -/
theorem slotCoordinateRigidity
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (_data : SelectedCompletionTooling F Time Vertex X₀ X)
    {slots slots' : LocalSlotCarrier}
    (hslots : ∀ slot : LocalSlot, slots slot = slots' slot) :
    localSlotCoordinates slots = localSlotCoordinates slots' := by
  exact localSlotCoordinates_eq_of_eq hslots

/-- The canonical overlap law carries an exact intrinsic channel spectrum on
the selected-completion carrier surface. -/
theorem canonicalOverlapExactChannelSpectrum
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (_data : SelectedCompletionTooling F Time Vertex X₀ X) :
    intrinsicChannelEigenvalue1 canonicalIntrinsicOverlapParameters =
        SignedCount.ofNat 6 ∧
      intrinsicChannelEigenvalue2 canonicalIntrinsicOverlapParameters =
        SignedCount.zero ∧
      intrinsicChannelEigenvalue3 canonicalIntrinsicOverlapParameters =
        SignedCount.ofNat 2 := by
  exact canonicalIntrinsicOverlapLaw_exactChannelSpectrum

/-- The distinguished `s12` fiber of the canonical overlap law already has one
exact reduced coordinate package on the selected-completion carrier surface. -/
theorem canonicalOverlapS12FiberCoordinates
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : SelectedCompletionTooling F Time Vertex X₀ X) :
    localSlotCoordinates canonicalIntrinsicOverlapS12Fiber =
      ⟨SignedCount.ofNat 4, SignedCount.zero, SignedCount.negOfNat 2⟩ := by
  exact data.sixSlot.canonicalS12FiberCoordinates

/-- The distinguished `s13` fiber of the canonical overlap law already has
the same exact reduced coordinates `(4, 0, -2)` on the selected-completion
carrier surface. -/
theorem canonicalOverlapS13FiberCoordinates
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : SelectedCompletionTooling F Time Vertex X₀ X) :
    localSlotCoordinates
        (intrinsicLawFiber canonicalIntrinsicOverlapLaw LocalSlot.s13) =
      ⟨SignedCount.ofNat 4, SignedCount.zero, SignedCount.negOfNat 2⟩ := by
  exact data.sixSlot.canonicalS13FiberCoordinates

/-- Any intrinsic six-slot law in canonical normal form `(2, 1, 0)` therefore
already has the same distinguished `s12` fiber coordinates as the canonical
overlap law. -/
theorem canonicalNormalFormS12FiberCoordinates
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : SelectedCompletionTooling F Time Vertex X₀ X)
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
  exact data.sixSlot.canonicalNormalFormS12FiberCoordinates hA

/-- Any intrinsic six-slot law in canonical normal form `(2, 1, 0)` therefore
already has the same distinguished `s13` fiber coordinates as the canonical
overlap law. This is the minimal single-fiber coordinate forcing theorem used
later by the selected-completion route. -/
theorem canonicalNormalFormS13FiberCoordinates
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : SelectedCompletionTooling F Time Vertex X₀ X)
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
  exact data.sixSlot.canonicalNormalFormS13FiberCoordinates hA

/-- Any intrinsic six-slot law in canonical normal form `(2, 1, 0)` already
has the same anchor-fiber coordinate family as the canonical overlap law. -/
theorem canonicalFiberCoordinates
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : SelectedCompletionTooling F Time Vertex X₀ X)
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
  exact data.sixSlot.canonicalFiberCoordinates hA

/-- An intrinsically equivariant six-slot law is already forced to be the
canonical overlap law once its `s13` anchor fiber has the canonical reduced
coordinates. This is the smallest fiber-level rigidity statement needed by the
selected-completion route. -/
theorem canonicalS13FiberRigidity
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : SelectedCompletionTooling F Time Vertex X₀ X)
    {A : LocalSlot → LocalSlot → SignedCount}
    (hA : IntrinsicAdjacencyInvariant A)
    (hs13 :
      localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13) =
        canonicalIntrinsicOverlapFiberCoordinates LocalSlot.s13) :
    ∀ α β : LocalSlot, A α β = canonicalIntrinsicOverlapLaw α β := by
  exact data.sixSlot.canonicalS13FiberRigidity hA hs13

/-- The same canonical `s13` anchor also forces the unique canonical normal
form `(2, 1, 0)` on the selected-completion six-slot carrier. So one anchored
row already determines the full intrinsic parameter package. -/
theorem canonicalS13FiberForcesCanonicalNormalForm
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : SelectedCompletionTooling F Time Vertex X₀ X)
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
  exact data.sixSlot.canonicalS13FiberForcesCanonicalNormalForm hA hs13

/-- And once that single anchor is canonical, the full anchor-fiber coordinate
family is forced on the selected-completion six-slot carrier. -/
theorem canonicalS13FiberForcesCanonicalFiberCoordinates
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : SelectedCompletionTooling F Time Vertex X₀ X)
    {A : LocalSlot → LocalSlot → SignedCount}
    (hA : IntrinsicAdjacencyInvariant A)
    (hs13 :
      localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13) =
        canonicalIntrinsicOverlapFiberCoordinates LocalSlot.s13) :
    ∀ anchor : LocalSlot,
      localSlotCoordinates (intrinsicLawFiber A anchor) =
        canonicalIntrinsicOverlapFiberCoordinates anchor := by
  exact data.sixSlot.canonicalS13FiberForcesCanonicalFiberCoordinates hA hs13

/-- If two intrinsically equivariant six-slot laws both carry the canonical
`s13` anchor fiber, then they already agree pointwise on the entire local
carrier. This is the pairwise single-anchor rigidity theorem exported to the
selected-completion route. -/
theorem canonicalS13FiberPairwiseRigidity
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : SelectedCompletionTooling F Time Vertex X₀ X)
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
  exact data.sixSlot.canonicalS13FiberPairwiseRigidity hA hs13A hB hs13B

/-- And the same pairwise single-anchor hypothesis already forces the full
anchor-fiber coordinate families to agree. So one anchored row on each law
controls every reduced local coordinate readout simultaneously. -/
theorem canonicalS13FiberPairwiseCoordinates
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : SelectedCompletionTooling F Time Vertex X₀ X)
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
  exact data.sixSlot.canonicalS13FiberPairwiseCoordinates hA hs13A hB hs13B

/-- The full anchor-fiber coordinate family also forces the canonical overlap
law. In practice this is just the `s13` rigidity theorem read through the
larger exported family surface. -/
theorem canonicalFiberRigidity
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : SelectedCompletionTooling F Time Vertex X₀ X)
    {A : LocalSlot → LocalSlot → SignedCount}
    (hA : IntrinsicAdjacencyInvariant A)
    (hcoords :
      ∀ anchor : LocalSlot,
        localSlotCoordinates (intrinsicLawFiber A anchor) =
          canonicalIntrinsicOverlapFiberCoordinates anchor) :
    ∀ α β : LocalSlot, A α β = canonicalIntrinsicOverlapLaw α β := by
  exact data.sixSlot.canonicalFiberRigidity hA hcoords

/-- Two intrinsic six-slot laws in canonical normal form `(2, 1, 0)` already
have the same anchor-fiber coordinate family. -/
theorem fiberCoordinateRigidity
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : SelectedCompletionTooling F Time Vertex X₀ X)
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
  exact data.sixSlot.fiberCoordinateRigidity hA hB

end SelectedCompletionTooling

end CoherenceCalculus
