import CoherenceCalculus.PartIV.ObserverSelectionCore

namespace CoherenceCalculus

/-- Part IV-facing alias for the exported Part III temporal interface datum.
This keeps interface-portability references inside the audited Part IV root
while remaining definitionally identical to the underlying bridge object. -/
abbrev PartIVExportedTemporalInterfaceDatum
    (F : RefinementCompatibleFamily) (Time Vertex X₀ X : Type) : Sort _ :=
  TemporalInterfaceDatum F Time Vertex X₀ X

/-- Part IV-facing alias for the upstream selected-completion toolkit exported
from the mathematical bridge lane. It combines the Part III temporal interface
with the canonical six-slot forcing surface from closure balance without
changing either proof surface. -/
abbrev PartIVExportedSelectedCompletionTooling
    (F : RefinementCompatibleFamily) (Time Vertex X₀ X : Type) : Sort _ :=
  SelectedCompletionTooling F Time Vertex X₀ X

/-- Part IV-facing wrapper for the Part III temporal-interface existence
theorem. The law-side chapters consume the exported interface package, so this
wrapper keeps that interface readable from the Part IV root without changing
its proof surface. -/
theorem partIV_temporal_interface_from_d3
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
    Nonempty (PartIVExportedTemporalInterfaceDatum F Time Vertex X₀ X) := by
  exact
    temporal_interface_from_d3
      F selected reconstruction continuumClass continuumLaw
      anchoredToCanonicalClosureBalance
      hanchored hscalar hrecursiveLaw hmem hcons hunique

/-- Part IV-facing wrapper for the bridge theorem that persistent
exactification on the residual `D = 3` carrier already yields the exported
temporal interface. -/
theorem partIV_persistent_exactification_yields_temporal_interface
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
    ∃ data : PartIVExportedTemporalInterfaceDatum F Time Vertex X₀ X,
      data.residualInterfaceDimension = 3 ∧
        data.selectedChannel.recursive_transport_law := by
  exact
    persistent_exactification_yields_temporal_interface
      F selected reconstruction continuumClass continuumLaw
      anchoredToCanonicalClosureBalance
      hanchored hscalar hrecursiveLaw hmem hcons hunique

namespace PartIVExportedTemporalInterfaceDatum

theorem anchorSurface
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedTemporalInterfaceDatum F Time Vertex X₀ X) :
    data.anchoredToCanonicalClosureBalance := by
  exact temporalInterfaceAnchoredSurface data

theorem dimensionSurface
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedTemporalInterfaceDatum F Time Vertex X₀ X) :
    data.residualInterfaceDimension = 3 := by
  exact temporalInterfaceDimensionSurface data

theorem scalarSurface
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedTemporalInterfaceDatum F Time Vertex X₀ X) :
    data.selectedChannel.scalar_quadratic_transport_law := by
  exact temporalInterfaceScalarSurface data

theorem recursiveSurface
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedTemporalInterfaceDatum F Time Vertex X₀ X) :
    data.selectedChannel.recursive_transport_law := by
  exact temporalInterfaceRecursiveSurface data

theorem transportSurface
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedTemporalInterfaceDatum F Time Vertex X₀ X) :
    data.selectedChannel.scalar_quadratic_transport_law ∧
      data.selectedChannel.recursive_transport_law := by
  exact ⟨scalarSurface data, recursiveSurface data⟩

theorem forcedContinuumLaw
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedTemporalInterfaceDatum F Time Vertex X₀ X) :
    ForcedContinuumLaw data.continuumClass data.continuumLaw := by
  exact temporalInterfaceForcedContinuumLaw data

end PartIVExportedTemporalInterfaceDatum

/-- Part IV-facing wrapper for the exported Part III temporal-interface
forcing theorem. -/
theorem partIV_temporal_interface_precedes_physical_time
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedTemporalInterfaceDatum F Time Vertex X₀ X) :
    data.anchoredToCanonicalClosureBalance ∧
      (data.residualInterfaceDimension = 3) ∧
      data.selectedChannel.scalar_quadratic_transport_law ∧
      data.selectedChannel.recursive_transport_law ∧
      ForcedContinuumLaw data.continuumClass data.continuumLaw := by
  exact
    ⟨PartIVExportedTemporalInterfaceDatum.anchorSurface data,
      PartIVExportedTemporalInterfaceDatum.dimensionSurface data,
      PartIVExportedTemporalInterfaceDatum.scalarSurface data,
      PartIVExportedTemporalInterfaceDatum.recursiveSurface data,
      PartIVExportedTemporalInterfaceDatum.forcedContinuumLaw data⟩

/-- Part IV-facing wrapper for the upstream selected-completion toolkit. This
is the current mathematical input surface available before any Part IV
physical-law forcing of the canonical completion target. -/
def partIV_selected_completion_tooling
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedTemporalInterfaceDatum F Time Vertex X₀ X) :
    PartIVExportedSelectedCompletionTooling F Time Vertex X₀ X :=
  data.toSelectedCompletionTooling

namespace PartIVExportedSelectedCompletionTooling

theorem temporalSurface
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedSelectedCompletionTooling F Time Vertex X₀ X) :
    data.temporal.anchoredToCanonicalClosureBalance ∧
      (data.temporal.residualInterfaceDimension = 3) ∧
      data.temporal.selectedChannel.scalar_quadratic_transport_law ∧
      data.temporal.selectedChannel.recursive_transport_law ∧
      ForcedContinuumLaw
        data.temporal.continuumClass
        data.temporal.continuumLaw := by
  exact SelectedCompletionTooling.temporalSurface data

theorem sixSlotSurface
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedSelectedCompletionTooling F Time Vertex X₀ X) :
    balancedClosureSlotCount closureStableDimension = 6 ∧
      (natListSum [3, 2, 1] = balancedClosureSlotCount closureStableDimension) ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  exact SelectedCompletionTooling.sixSlotSurface data

theorem uniqueNormalForm
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedSelectedCompletionTooling F Time Vertex X₀ X)
    (A : LocalSlot → LocalSlot → SignedCount)
    (hA : IntrinsicAdjacencyInvariant A) :
    ∃ p : IntrinsicSlotParameters,
        isIntrinsicNormalForm A p ∧
          ∀ q : IntrinsicSlotParameters, isIntrinsicNormalForm A q → q = p := by
  exact SelectedCompletionTooling.uniqueNormalForm data A hA

theorem normalFormRigidity
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedSelectedCompletionTooling F Time Vertex X₀ X)
    {A B : LocalSlot → LocalSlot → SignedCount}
    {p : IntrinsicSlotParameters}
    (hA : isIntrinsicNormalForm A p)
    (hB : isIntrinsicNormalForm B p) :
    ∀ α β : LocalSlot, A α β = B α β := by
  exact SelectedCompletionTooling.normalFormRigidity data hA hB

theorem threeParameterControl
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedSelectedCompletionTooling F Time Vertex X₀ X)
    (A : LocalSlot → LocalSlot → SignedCount)
    (hA : IntrinsicAdjacencyInvariant A) :
    ∃ a b c : SignedCount,
      ∀ α β : LocalSlot,
        A α β =
          match intrinsicSlotAdjacency α β with
          | .equal => a
          | .adjacent => b
          | .disjoint => c := by
  exact SelectedCompletionTooling.threeParameterControl data A hA

theorem channelEigenvalues
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedSelectedCompletionTooling F Time Vertex X₀ X)
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
  exact SelectedCompletionTooling.channelEigenvalues data A hA

theorem canonicalOverlapLawSurface
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedSelectedCompletionTooling F Time Vertex X₀ X) :
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
  exact SelectedCompletionTooling.canonicalOverlapLawSurface data

theorem canonicalOverlapLawRigidity
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedSelectedCompletionTooling F Time Vertex X₀ X)
    {A : LocalSlot → LocalSlot → SignedCount}
    {p : IntrinsicSlotParameters}
    (hA : isIntrinsicNormalForm A p)
    (hdiag : p.diagonal = SignedCount.ofNat 2)
    (hadj : p.adjacent = SignedCount.ofNat 1)
    (hdis : p.disjoint = SignedCount.zero) :
    ∀ α β : LocalSlot, A α β = canonicalIntrinsicOverlapLaw α β := by
  exact
    SelectedCompletionTooling.canonicalOverlapLawRigidity
      data hA hdiag hadj hdis

theorem slotCoordinateRigidity
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedSelectedCompletionTooling F Time Vertex X₀ X)
    {slots slots' : LocalSlotCarrier}
    (hslots : ∀ slot : LocalSlot, slots slot = slots' slot) :
    localSlotCoordinates slots = localSlotCoordinates slots' := by
  exact SelectedCompletionTooling.slotCoordinateRigidity data hslots

theorem canonicalOverlapExactChannelSpectrum
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedSelectedCompletionTooling F Time Vertex X₀ X) :
    intrinsicChannelEigenvalue1 canonicalIntrinsicOverlapParameters =
        SignedCount.ofNat 6 ∧
      intrinsicChannelEigenvalue2 canonicalIntrinsicOverlapParameters =
        SignedCount.zero ∧
      intrinsicChannelEigenvalue3 canonicalIntrinsicOverlapParameters =
        SignedCount.ofNat 2 := by
  exact SelectedCompletionTooling.canonicalOverlapExactChannelSpectrum data

theorem canonicalOverlapS12FiberCoordinates
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedSelectedCompletionTooling F Time Vertex X₀ X) :
    localSlotCoordinates canonicalIntrinsicOverlapS12Fiber =
      ⟨SignedCount.ofNat 4, SignedCount.zero, SignedCount.negOfNat 2⟩ := by
  exact SelectedCompletionTooling.canonicalOverlapS12FiberCoordinates data

theorem canonicalOverlapS13FiberCoordinates
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedSelectedCompletionTooling F Time Vertex X₀ X) :
    localSlotCoordinates
        (intrinsicLawFiber canonicalIntrinsicOverlapLaw LocalSlot.s13) =
      ⟨SignedCount.ofNat 4, SignedCount.zero, SignedCount.negOfNat 2⟩ := by
  exact SelectedCompletionTooling.canonicalOverlapS13FiberCoordinates data

theorem canonicalNormalFormS12FiberCoordinates
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedSelectedCompletionTooling F Time Vertex X₀ X)
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
  exact SelectedCompletionTooling.canonicalNormalFormS12FiberCoordinates data hA

theorem canonicalNormalFormS13FiberCoordinates
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedSelectedCompletionTooling F Time Vertex X₀ X)
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
  exact SelectedCompletionTooling.canonicalNormalFormS13FiberCoordinates data hA

theorem canonicalFiberCoordinates
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedSelectedCompletionTooling F Time Vertex X₀ X)
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
  exact SelectedCompletionTooling.canonicalFiberCoordinates data hA

theorem canonicalS13FiberRigidity
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedSelectedCompletionTooling F Time Vertex X₀ X)
    {A : LocalSlot → LocalSlot → SignedCount}
    (hA : IntrinsicAdjacencyInvariant A)
    (hs13 :
      localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13) =
        canonicalIntrinsicOverlapFiberCoordinates LocalSlot.s13) :
    ∀ α β : LocalSlot, A α β = canonicalIntrinsicOverlapLaw α β := by
  exact SelectedCompletionTooling.canonicalS13FiberRigidity data hA hs13

theorem canonicalS13FiberForcesCanonicalNormalForm
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedSelectedCompletionTooling F Time Vertex X₀ X)
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
  exact
    SelectedCompletionTooling.canonicalS13FiberForcesCanonicalNormalForm
      data hA hs13

theorem canonicalS13FiberForcesCanonicalFiberCoordinates
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedSelectedCompletionTooling F Time Vertex X₀ X)
    {A : LocalSlot → LocalSlot → SignedCount}
    (hA : IntrinsicAdjacencyInvariant A)
    (hs13 :
      localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13) =
        canonicalIntrinsicOverlapFiberCoordinates LocalSlot.s13) :
    ∀ anchor : LocalSlot,
      localSlotCoordinates (intrinsicLawFiber A anchor) =
        canonicalIntrinsicOverlapFiberCoordinates anchor := by
  exact
    SelectedCompletionTooling.canonicalS13FiberForcesCanonicalFiberCoordinates
      data hA hs13

theorem canonicalS13FiberPairwiseRigidity
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedSelectedCompletionTooling F Time Vertex X₀ X)
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
  exact
    SelectedCompletionTooling.canonicalS13FiberPairwiseRigidity
      data hA hs13A hB hs13B

theorem canonicalS13FiberPairwiseCoordinates
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedSelectedCompletionTooling F Time Vertex X₀ X)
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
  exact
    SelectedCompletionTooling.canonicalS13FiberPairwiseCoordinates
      data hA hs13A hB hs13B

theorem canonicalFiberRigidity
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedSelectedCompletionTooling F Time Vertex X₀ X)
    {A : LocalSlot → LocalSlot → SignedCount}
    (hA : IntrinsicAdjacencyInvariant A)
    (hcoords :
      ∀ anchor : LocalSlot,
        localSlotCoordinates (intrinsicLawFiber A anchor) =
          canonicalIntrinsicOverlapFiberCoordinates anchor) :
    ∀ α β : LocalSlot, A α β = canonicalIntrinsicOverlapLaw α β := by
  exact SelectedCompletionTooling.canonicalFiberRigidity data hA hcoords

theorem fiberCoordinateRigidity
    {Time Vertex X₀ X : Type}
    {F : RefinementCompatibleFamily}
    (data : PartIVExportedSelectedCompletionTooling F Time Vertex X₀ X)
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
  exact SelectedCompletionTooling.fiberCoordinateRigidity data hA hB

end PartIVExportedSelectedCompletionTooling

end CoherenceCalculus
