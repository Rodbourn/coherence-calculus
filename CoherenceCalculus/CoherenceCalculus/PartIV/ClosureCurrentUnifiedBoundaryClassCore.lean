import CoherenceCalculus.PartIV.ClosureCurrentUnifiedBoundaryFieldCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentUnifiedBoundaryClassCore

Classwise canonicity of the unified selected-horizon boundary field.

`ClosureCurrentUnifiedBoundaryFieldCore` already shows that the
endpoint-complete no-stage law determines one explicit selected-horizon
boundary field on the concrete carrier `State`.

The remaining honest abstract question is not whether there is some richer
carrier or some additional hidden datum. It is whether that same boundary field
is canonical across the whole admissible selected class already carried by the
active forcing surface.

This file records the answer. The canonical selected Schur bridge already
contains:

* one admissible realized class,
* one least-motion root datum,
* classwise horizon-preserving equivalences.

So the same selected observed law, observed boundary, and defect are already
transported across the whole class. The remaining PDE/action step is therefore
not even a choice of selected datum inside the admissible class, but only an
external presentation of this already-fixed transported boundary field.
-/

namespace ClosureCurrent

/-- One explicit classwise package for the unified selected-horizon boundary
field. The package records the already-fixed boundary field at the least-motion
root together with the admissible realized class and the exact transport of the
selected law, observed boundary, and defect across that class. -/
structure UnifiedBoundaryClass
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) where
  boundaryField : UnifiedBoundaryField data
  rootSelection_eq :
    data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.observer.selection =
      data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.cls.datum
        data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.root
  sameHorizon :
    ∀ i : Index,
      data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.observer.selection.horizon =
        (data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.cls.datum i).horizon
  selectedLawTransport :
    ∀ i : Index, ∀ x : State,
      (data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.uniqueClass
          data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.root i).transport
        ((selected_observed_law
            data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.observer.selection).op x) =
      (selected_observed_law
          (data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.cls.datum i)).op
        ((data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.uniqueClass
            data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.root i).transport x)
  observedBoundaryTransport :
    ∀ i : Index, ∀ x : State,
      (data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.uniqueClass
          data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.root i).transport
        (observedBoundary
          data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.observer.selection.realization.tower
          data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.observer.selection.horizon x) =
      observedBoundary
        (data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.cls.datum i).realization.tower
        (data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.cls.datum i).horizon
        ((data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.uniqueClass
            data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.root i).transport x)
  defectTransport :
    ∀ i : Index, ∀ x : State,
      (data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.uniqueClass
          data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.root i).transport
        (boundaryDefect
          data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.observer.selection.realization.tower
          data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.observer.selection.horizon x) =
      boundaryDefect
        (data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.cls.datum i).realization.tower
        (data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.cls.datum i).horizon
        ((data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.uniqueClass
            data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge.root i).transport x)

/-- Manuscript-facing classwise canonicity surface of the endpoint-complete
no-stage law. -/
def UnifiedBoundaryClassSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) : Prop :=
  Nonempty (UnifiedBoundaryClass data)

/-- The endpoint-complete no-stage law already determines its selected-horizon
boundary field canonically across the whole admissible realized class carried
by the selected bridge. The same selected law, observed boundary, and defect
are transported across that class by the horizon-preserving equivalences, so
the remaining PDE/action step is only an external presentation of one already
fixed classwise field. -/
theorem LocalEventFourStateFlagshipLaw.unifiedBoundaryClassSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    UnifiedBoundaryClassSurface data := by
  obtain ⟨hboundaryField⟩ := data.unifiedBoundaryFieldSurface
  let bridge := data.completionLaw.fourStateLaw.framed.object.bridge.selectedBridge
  obtain
    ⟨_hproj, _hcut, hforcing, _hmin, _hexact, _hclosed, _hnoConst, _hreturned,
      _hret, _hsplit, _hstep, _hmono, _hd3, _hprofile⟩ :=
    canonical_selected_schur_realization bridge
  refine
    ⟨{ boundaryField := hboundaryField
       rootSelection_eq := bridge.rootSelection_eq
       sameHorizon := by
         intro i
         exact (hforcing i).1
       selectedLawTransport := by
         intro i x
         exact (hforcing i).2 x
       observedBoundaryTransport := by
         intro i x
         have hrootObs :
             observedBoundary
               bridge.observer.selection.realization.tower
               bridge.observer.selection.horizon x =
             observedBoundary
               (bridge.cls.datum bridge.root).realization.tower
               (bridge.cls.datum bridge.root).horizon x := by
           simp [bridge.rootSelection_eq]
         calc
           (bridge.uniqueClass bridge.root i).transport
               (observedBoundary
                 bridge.observer.selection.realization.tower
                 bridge.observer.selection.horizon x) =
             (bridge.uniqueClass bridge.root i).transport
               (observedBoundary
                 (bridge.cls.datum bridge.root).realization.tower
                 (bridge.cls.datum bridge.root).horizon x) := by
                   rw [hrootObs]
           _ =
             observedBoundary
               (bridge.cls.datum i).realization.tower
               (bridge.cls.datum i).horizon
               ((bridge.uniqueClass bridge.root i).transport x) := by
                 exact (bridge.uniqueClass bridge.root i).observed_boundary x
       defectTransport := by
         intro i x
         have hrootDef :
             boundaryDefect
               bridge.observer.selection.realization.tower
               bridge.observer.selection.horizon x =
             boundaryDefect
               (bridge.cls.datum bridge.root).realization.tower
               (bridge.cls.datum bridge.root).horizon x := by
           simp [bridge.rootSelection_eq]
         calc
           (bridge.uniqueClass bridge.root i).transport
               (boundaryDefect
                 bridge.observer.selection.realization.tower
                 bridge.observer.selection.horizon x) =
             (bridge.uniqueClass bridge.root i).transport
               (boundaryDefect
                 (bridge.cls.datum bridge.root).realization.tower
                 (bridge.cls.datum bridge.root).horizon x) := by
                   rw [hrootDef]
           _ =
             boundaryDefect
               (bridge.cls.datum i).realization.tower
               (bridge.cls.datum i).horizon
               ((bridge.uniqueClass bridge.root i).transport x) := by
                 exact (bridge.uniqueClass bridge.root i).observed_defect x }⟩

end ClosureCurrent

end CoherenceCalculus
