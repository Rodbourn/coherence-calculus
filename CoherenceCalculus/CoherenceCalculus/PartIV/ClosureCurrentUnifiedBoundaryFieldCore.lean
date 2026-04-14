import CoherenceCalculus.PartIV.ClosureCurrentUnifiedTransportFieldCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentUnifiedBoundaryFieldCore

One explicit selected-horizon boundary field on the current flagship surface.

`ClosureCurrentUnifiedTransportFieldCore` already packages the strongest honest
transport object carried by the endpoint-complete no-stage law: one unified
`State`-valued transport field together with the exact Parts I--III transport
and Hamilton--Jacobi grammar on the same selected datum.

The next honest closure is to use the active Part I boundary calculus itself on
that same transport field. This does not introduce a new carrier, a new
dynamics, or a new horizon. It only records that the same `State`-valued
transport field already carries:

* the selected cut as the realized horizon cut;
* the observed boundary, leakage, return, and defect maps on that cut;
* the exact boundary split on selected states;
* the exact observed-boundary square law and transported defect law.

So the present detached flagship surface is already a boundary field on the
same concrete carrier `State`, not merely a differential/variational package
awaiting interpretation.
-/

namespace ClosureCurrent

/-- One explicit selected-horizon boundary field on the current detached
flagship surface. The package records the already-fixed unified transport field
together with the realized selected cut, the associated observed boundary /
leakage / return / defect maps, and the exact Part I boundary identities on
that same cut. -/
structure UnifiedBoundaryField
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) where
  transportField : UnifiedTransportField data
  selectedCut_eq :
    transportField.differentialField.unifiedField.law.project =
      (transportField.realization.tower.π transportField.horizon).toFun
  observedBoundary : State → State
  leakage : State → State
  returnMap : State → State
  defect : State → State
  observedBoundary_eq :
    observedBoundary =
      CoherenceCalculus.observedBoundary
        transportField.realization.tower transportField.horizon
  leakage_eq :
    leakage =
      boundaryLeakage transportField.realization.tower transportField.horizon
  returnMap_eq :
    returnMap =
      boundaryReturn transportField.realization.tower transportField.horizon
  defect_eq :
    defect =
      boundaryDefect transportField.realization.tower transportField.horizon
  defect_from_return :
    ∀ x : State, defect x = returnMap (leakage x)
  fullBoundary_closes :
    ∀ x : State, trueBoundary (trueBoundary x) = State.zero
  boundarySquare :
    ∀ x : State,
      observedBoundary (observedBoundary x) = State.negate (defect x)
  selectedSplit :
    ∀ u : State,
      transportField.differentialField.unifiedField.law.project u = u →
        trueBoundary u = State.add (observedBoundary u) (leakage u)
  transportObservedBoundary :
    ∀ t : Time, ∀ x : State,
      transportField.realization.U t (observedBoundary x) =
        observedBoundary (transportField.realization.U t x)
  transportDefect :
    ∀ t : Time, ∀ x : State,
      transportField.realization.U t (defect x) =
        defect (transportField.realization.U t x)

/-- Manuscript-facing selected-horizon boundary-field surface of the
endpoint-complete no-stage law. -/
def UnifiedBoundaryFieldSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) : Prop :=
  Nonempty (UnifiedBoundaryField data)

/-- The endpoint-complete no-stage law already yields one explicit
selected-horizon boundary field on the concrete carrier `State`. The same
unified transport field already carries the selected cut as a realized horizon
cut, the full boundary split on selected states, the exact
`observedBoundary^2 = - defect` law, and transported observed-boundary /
defect identities. -/
theorem LocalEventFourStateFlagshipLaw.unifiedBoundaryFieldSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateFlagshipLaw Index Time Carrier Law) :
    UnifiedBoundaryFieldSurface data := by
  obtain ⟨htransportField⟩ := data.unifiedTransportFieldSurface
  let law := data.completionLaw.fourStateLaw
  let selection := law.framed.object.bridge.selectedBridge.observer.selection
  have hcut :
      selection.selectedProjection =
        selection.realization.tower.π selection.horizon :=
    law.framed.object.bridge.selectedBridge.selectedProjection_eq_horizonCut
  have hcut' :
      selection.selectedProjection =
        htransportField.realization.tower.π htransportField.horizon := by
    calc
      selection.selectedProjection =
          selection.realization.tower.π selection.horizon := hcut
      _ = htransportField.realization.tower.π selection.horizon := by
            rw [htransportField.realization_eq]
      _ = htransportField.realization.tower.π htransportField.horizon := by
            rw [← htransportField.horizon_eq]
  have hselectedCut :
      htransportField.differentialField.unifiedField.law.project =
        (htransportField.realization.tower.π htransportField.horizon).toFun := by
    funext x
    calc
      htransportField.differentialField.unifiedField.law.project x =
          law.selectedStateFieldLaw.project x := by
            rw [htransportField.differentialField.unifiedField.law_eq]
      _ = selection.selectedProjection.toFun x := by
            rfl
      _ = (htransportField.realization.tower.π htransportField.horizon).toFun x := by
            exact congrArg (fun P : Projection => P.toFun x) hcut'
  refine
    ⟨{ transportField := htransportField
       selectedCut_eq := hselectedCut
       observedBoundary :=
         CoherenceCalculus.observedBoundary
           htransportField.realization.tower htransportField.horizon
       leakage :=
         boundaryLeakage htransportField.realization.tower htransportField.horizon
       returnMap :=
         boundaryReturn htransportField.realization.tower htransportField.horizon
       defect :=
         boundaryDefect htransportField.realization.tower htransportField.horizon
       observedBoundary_eq := rfl
       leakage_eq := rfl
       returnMap_eq := rfl
       defect_eq := rfl
       defect_from_return := by
         intro x
         rfl
       fullBoundary_closes := htransportField.partOneSurface.1
       boundarySquare := by
         intro x
         exact htransportField.partOneSurface.2 x
       selectedSplit := by
         intro u hu
         have huCut :
             (htransportField.realization.tower.π htransportField.horizon).toFun u = u := by
           calc
             (htransportField.realization.tower.π htransportField.horizon).toFun u =
                 htransportField.differentialField.unifiedField.law.project u := by
                   symm
                   exact congrArg (fun f : State → State => f u) hselectedCut
             _ = u := hu
         exact
           (through_horizon_decomposition
             htransportField.realization htransportField.horizon u huCut).1
       transportObservedBoundary := by
         intro t x
         exact (htransportField.transportSurface t x).1
       transportDefect := by
         intro t x
         exact (htransportField.transportSurface t x).2 }⟩

end ClosureCurrent

end CoherenceCalculus
