import CoherenceCalculus.PartIV.ClosureCurrentSelectedLawCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentAutonomyLawCore

Autonomy-forced flagship law for the detached closure-current lane.

`ClosureCurrentSelectedLawCore` exposed the boxed generator/transport/channel
equation on an anchored detached current object, but still through an explicit
rolewise compatibility witness. This file replaces that witness by a realized
autonomy package:

* the hidden pair current is realized as a state on the selected cut;
* each visible quotient is realized as a projection-fixed visible state;
* the realized quotient evolution is autonomous for the same selected
  exactification generator.

From that, the flagship equation is a theorem rather than extra compatibility
data.
-/

namespace ClosureCurrent

/-- Realized state of the detached pair current on the selected cut. -/
structure CurrentState
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentObject Index Time Carrier Law) where
  realize :
    PairExchangeCurrent data.currentCarrier data.Leg → State
  exactifier_realized :
    ∀ current : PairExchangeCurrent data.currentCarrier data.Leg,
      realize (data.exactifier.exactify current) =
        data.bridge.generator.toFun (realize current)

/-- A visible quotient realized as a projection-fixed state law on the selected
cut. The visible evolution is not postulated as the boxed channel equation; it
is read through an autonomous state law on the same selected cut. -/
structure VisibleStateLaw
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentObject Index Time Carrier Law)
    (currentState : CurrentState data)
    (role : VisibleCarrierRole) where
  realize : data.visible role → State
  realize_injective :
    ∀ v w : data.visible role, realize v = realize w → v = w
  realize_visible :
    ∀ v : data.visible role,
      selectedProjection data.bridge (realize v) = realize v
  read_realized :
    ∀ current : PairExchangeCurrent data.currentCarrier data.Leg,
      realize ((data.quotient role).read current) =
        selectedProjection data.bridge (currentState.realize current)
  law : State → State
  law_autonomous :
    AutonomousScaleLaw
      data.bridge.selectedBridge.observer.selection.realization.tower
      data.bridge.selectedBridge.observer.selection.horizon
      data.bridge.generator
      law
  evolve_realized :
    ∀ v : data.visible role,
      realize ((data.quotient role).evolve v) = law (realize v)

/-- Compact role-indexed state realization of the detached current lane on the
selected cut. This is the manuscript-facing autonomous realization package:
one hidden current-state realization and one role-indexed visible state field
with autonomous state laws on the same selected cut. -/
structure AutonomousStateField
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentObject Index Time Carrier Law) where
  currentRealize :
    PairExchangeCurrent data.currentCarrier data.Leg → State
  exactifier_realized :
    ∀ current : PairExchangeCurrent data.currentCarrier data.Leg,
      currentRealize (data.exactifier.exactify current) =
        data.bridge.generator.toFun (currentRealize current)
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
          selectedProjection data.bridge (currentRealize current)
  law : VisibleCarrierRole → State → State
  law_autonomous :
    ∀ role : VisibleCarrierRole,
      AutonomousScaleLaw
        data.bridge.selectedBridge.observer.selection.realization.tower
        data.bridge.selectedBridge.observer.selection.horizon
        data.bridge.generator
        (law role)
  evolve_realized :
    ∀ role : VisibleCarrierRole,
      ∀ v : data.visible role,
        visibleRealize role ((data.quotient role).evolve v) =
          law role (visibleRealize role v)

/-- The compact state field determines the realized current state. -/
def AutonomousStateField.toCurrentState
    {Index Time Carrier Law : Type}
    {data : AnchoredCurrentObject Index Time Carrier Law}
    (field : AutonomousStateField data) :
    CurrentState data where
  realize := field.currentRealize
  exactifier_realized := field.exactifier_realized

/-- The compact state field determines the realized visible law on any chosen
role. -/
def AutonomousStateField.toVisibleStateLaw
    {Index Time Carrier Law : Type}
    {data : AnchoredCurrentObject Index Time Carrier Law}
    (field : AutonomousStateField data)
    (role : VisibleCarrierRole) :
    VisibleStateLaw data field.toCurrentState role where
  realize := field.visibleRealize role
  realize_injective := field.visibleRealize_injective role
  realize_visible := field.visibleRealize_visible role
  read_realized := field.read_realized role
  law := field.law role
  law_autonomous := field.law_autonomous role
  evolve_realized := field.evolve_realized role

/-- The realized visible law agrees with the matched selected generator on
every realized visible state. This is the autonomy uniqueness clause read on
the quotient realization. -/
theorem VisibleStateLaw.law_eq_generator_on_realized
    {Index Time Carrier Law : Type}
    {data : AnchoredCurrentObject Index Time Carrier Law}
    {currentState : CurrentState data}
    {role : VisibleCarrierRole}
    (lawData : VisibleStateLaw data currentState role) :
    ∀ v : data.visible role,
      lawData.law (lawData.realize v) =
        data.bridge.generator.toFun (lawData.realize v) := by
  intro v
  exact
    selectedAutonomousLaw_unique
      data.bridge
      lawData.law_autonomous
      (lawData.realize v)
      (lawData.realize_visible v)

/-- A realized visible autonomous law forces the boxed quotient transport
equation role by role. -/
theorem VisibleStateLaw.transportCompatible
    {Index Time Carrier Law : Type}
    {data : AnchoredCurrentObject Index Time Carrier Law}
    {currentState : CurrentState data}
    {role : VisibleCarrierRole}
    (lawData : VisibleStateLaw data currentState role) :
    ∀ current : PairExchangeCurrent data.currentCarrier data.Leg,
      (data.quotient role).read (data.exactifier.exactify current) =
        (data.quotient role).evolve ((data.quotient role).read current) := by
  intro current
  apply lawData.realize_injective
  have hfactor :
      selectedProjection data.bridge
          (data.bridge.generator.toFun (currentState.realize current)) =
        lawData.law
          (selectedProjection data.bridge (currentState.realize current)) :=
    (lawData.law_autonomous.2 (currentState.realize current))
  calc
    lawData.realize ((data.quotient role).read (data.exactifier.exactify current))
        =
          selectedProjection data.bridge
            (currentState.realize (data.exactifier.exactify current)) :=
      lawData.read_realized (data.exactifier.exactify current)
    _ =
          selectedProjection data.bridge
            (data.bridge.generator.toFun (currentState.realize current)) := by
          rw [currentState.exactifier_realized current]
    _ =
          lawData.law
            (selectedProjection data.bridge (currentState.realize current)) :=
      hfactor
    _ = lawData.law (lawData.realize ((data.quotient role).read current)) := by
          rw [lawData.read_realized current]
    _ =
          lawData.realize
            ((data.quotient role).evolve ((data.quotient role).read current)) := by
          symm
          exact lawData.evolve_realized ((data.quotient role).read current)

/-- Anchored detached current object equipped with a realized autonomous law on
each visible quotient. This is the smallest detached package on which the
boxed flagship equation is forced from the autonomy grammar itself. -/
structure AnchoredAutonomyObject (Index Time Carrier Law : Type) where
  object : AnchoredCurrentObject Index Time Carrier Law
  currentState : CurrentState object
  visibleLaw :
    ∀ role : VisibleCarrierRole,
      VisibleStateLaw object currentState role

/-- Compact autonomous anchored current object. The role-indexed state field is
stored directly, and the expanded `CurrentState` / `VisibleStateLaw` package is
read from it automatically. -/
structure AutonomousAnchoredCurrentObject (Index Time Carrier Law : Type) where
  object : AnchoredCurrentObject Index Time Carrier Law
  stateField : AutonomousStateField object

/-- The compact autonomous anchored current object determines the expanded
autonomy package used by the forcing theorem. -/
def AutonomousAnchoredCurrentObject.toAnchoredAutonomyObject
    {Index Time Carrier Law : Type}
    (data : AutonomousAnchoredCurrentObject Index Time Carrier Law) :
    AnchoredAutonomyObject Index Time Carrier Law where
  object := data.object
  currentState := data.stateField.toCurrentState
  visibleLaw := fun role => data.stateField.toVisibleStateLaw role

/-- Unified selected-cut state field for the detached current lane. Unlike
`AutonomousStateField`, this package does not keep a separate autonomous law on
each visible role. All visible roles are transported by the matched selected
generator on one common ambient state space. -/
structure UnifiedStateField
    {Index Time Carrier Law : Type}
    (data : AnchoredCurrentObject Index Time Carrier Law) where
  currentRealize :
    PairExchangeCurrent data.currentCarrier data.Leg → State
  exactifier_realized :
    ∀ current : PairExchangeCurrent data.currentCarrier data.Leg,
      currentRealize (data.exactifier.exactify current) =
        data.bridge.generator.toFun (currentRealize current)
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
          selectedProjection data.bridge (currentRealize current)
  evolve_realized :
    ∀ role : VisibleCarrierRole,
      ∀ v : data.visible role,
        visibleRealize role ((data.quotient role).evolve v) =
          data.bridge.generator.toFun (visibleRealize role v)

/-- Autonomy already forces the compact role-indexed state field to unify to
the matched selected generator on the selected cut. The visible role laws are
therefore not additional primitive transport laws. -/
def AutonomousStateField.toUnifiedStateField
    {Index Time Carrier Law : Type}
    {data : AnchoredCurrentObject Index Time Carrier Law}
    (field : AutonomousStateField data) :
    UnifiedStateField data where
  currentRealize := field.currentRealize
  exactifier_realized := field.exactifier_realized
  visibleRealize := field.visibleRealize
  visibleRealize_injective := field.visibleRealize_injective
  visibleRealize_visible := field.visibleRealize_visible
  read_realized := field.read_realized
  evolve_realized := by
    intro role v
    calc
      field.visibleRealize role ((data.quotient role).evolve v)
          = field.law role (field.visibleRealize role v) :=
        field.evolve_realized role v
      _ = data.bridge.generator.toFun (field.visibleRealize role v) := by
        exact (field.toVisibleStateLaw role).law_eq_generator_on_realized v

/-- The unified state field refines to the earlier role-indexed autonomous
state field by reading every visible law through the same matched selected
generator. -/
def UnifiedStateField.toAutonomousStateField
    {Index Time Carrier Law : Type}
    {data : AnchoredCurrentObject Index Time Carrier Law}
    (field : UnifiedStateField data) :
    AutonomousStateField data where
  currentRealize := field.currentRealize
  exactifier_realized := field.exactifier_realized
  visibleRealize := field.visibleRealize
  visibleRealize_injective := field.visibleRealize_injective
  visibleRealize_visible := field.visibleRealize_visible
  read_realized := field.read_realized
  law := fun _ => data.bridge.generator.toFun
  law_autonomous := by
    intro role
    exact selectedHorizonAutonomousScale data.bridge
  evolve_realized := by
    intro role v
    exact field.evolve_realized role v

/-- A unified state field forces the boxed quotient transport equation
role by role using only the matched selected generator. -/
theorem UnifiedStateField.transportCompatible
    {Index Time Carrier Law : Type}
    {data : AnchoredCurrentObject Index Time Carrier Law}
    {role : VisibleCarrierRole}
    (field : UnifiedStateField data) :
    ∀ current : PairExchangeCurrent data.currentCarrier data.Leg,
      (data.quotient role).read (data.exactifier.exactify current) =
        (data.quotient role).evolve ((data.quotient role).read current) := by
  intro current
  apply field.visibleRealize_injective role
  calc
    field.visibleRealize role ((data.quotient role).read (data.exactifier.exactify current))
        =
          selectedProjection data.bridge
            (field.currentRealize (data.exactifier.exactify current)) :=
      field.read_realized role (data.exactifier.exactify current)
    _ =
          selectedProjection data.bridge
            (data.bridge.generator.toFun (field.currentRealize current)) := by
          rw [field.exactifier_realized current]
    _ =
          data.bridge.generator.toFun
            (selectedProjection data.bridge (field.currentRealize current)) :=
          selectedHorizonAutonomousScale data.bridge |>.2 (field.currentRealize current)
    _ =
          data.bridge.generator.toFun
            (field.visibleRealize role ((data.quotient role).read current)) := by
          rw [field.read_realized role current]
    _ =
          field.visibleRealize role
            ((data.quotient role).evolve ((data.quotient role).read current)) := by
          symm
          exact field.evolve_realized role ((data.quotient role).read current)

/-- Unified anchored detached current object. The visible roles are read on one
common ambient state field and transported there by one matched selected
generator. -/
structure UnifiedAnchoredCurrentObject (Index Time Carrier Law : Type) where
  object : AnchoredCurrentObject Index Time Carrier Law
  stateField : UnifiedStateField object

/-- The unified anchored current object determines the earlier autonomous
anchored current object. -/
def UnifiedAnchoredCurrentObject.toAutonomousAnchoredCurrentObject
    {Index Time Carrier Law : Type}
    (data : UnifiedAnchoredCurrentObject Index Time Carrier Law) :
    AutonomousAnchoredCurrentObject Index Time Carrier Law where
  object := data.object
  stateField := data.stateField.toAutonomousStateField

/-- The autonomy package already collapses to the unified state-field package.
-/
def AutonomousAnchoredCurrentObject.toUnifiedAnchoredCurrentObject
    {Index Time Carrier Law : Type}
    (data : AutonomousAnchoredCurrentObject Index Time Carrier Law) :
    UnifiedAnchoredCurrentObject Index Time Carrier Law where
  object := data.object
  stateField := data.stateField.toUnifiedStateField

/-- The realized autonomous anchored object determines the earlier selected-cut
law form. The transport equation is now proved rather than supplied. -/
def AnchoredAutonomyObject.toAnchoredLawForm
    {Index Time Carrier Law : Type}
    (data : AnchoredAutonomyObject Index Time Carrier Law) :
    AnchoredLawForm Index Time Carrier Law where
  object := data.object
  transportCompatible := by
    intro role current
    exact VisibleStateLaw.transportCompatible (data.visibleLaw role) current

/-- Surface theorem for the realized autonomous anchored object. The selected
detached flagship law is forced from current realization plus autonomous
visible quotient laws, and the realized visible laws agree pointwise with the
matched selected generator on realized visible states. -/
theorem AnchoredAutonomyObject.surface
    {Index Time Carrier Law : Type}
    (data : AnchoredAutonomyObject Index Time Carrier Law) :
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
          data.toAnchoredLawForm.channelResidual role current =
            data.toAnchoredLawForm.channelRead role
              (data.toAnchoredLawForm.returnedDefect current)) ∧
      (∀ role : VisibleCarrierRole,
        ∀ v : data.object.visible role,
          (data.visibleLaw role).law ((data.visibleLaw role).realize v) =
            data.object.bridge.generator.toFun
              ((data.visibleLaw role).realize v)) := by
  obtain ⟨hcurrent, hdirret, haut, hmin, hexact, hforced, htransport, hlaw, hresidual⟩ :=
    data.toAnchoredLawForm.surface
  exact
    ⟨hcurrent,
      hdirret,
      haut,
      hmin,
      hexact,
      hforced,
      htransport,
      hlaw,
      hresidual,
      by
        intro role v
        exact VisibleStateLaw.law_eq_generator_on_realized (data.visibleLaw role) v⟩

/-- Surface theorem for the compact autonomous anchored current object. The
boxed flagship law is forced directly from one role-indexed state field on the
anchored detached current object. -/
theorem AutonomousAnchoredCurrentObject.surface
    {Index Time Carrier Law : Type}
    (data : AutonomousAnchoredCurrentObject Index Time Carrier Law) :
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
          data.toAnchoredAutonomyObject.toAnchoredLawForm.channelResidual role current =
            data.toAnchoredAutonomyObject.toAnchoredLawForm.channelRead role
              (data.toAnchoredAutonomyObject.toAnchoredLawForm.returnedDefect current)) ∧
      (∀ role : VisibleCarrierRole,
        ∀ v : data.object.visible role,
          (data.stateField.law role) ((data.stateField.visibleRealize role) v) =
            data.object.bridge.generator.toFun
              ((data.stateField.visibleRealize role) v)) := by
  simpa [AutonomousAnchoredCurrentObject.toAnchoredAutonomyObject,
    AutonomousStateField.toCurrentState, AutonomousStateField.toVisibleStateLaw]
    using data.toAnchoredAutonomyObject.surface

/-- On a unified state field, the visible transport is already the matched
selected generator on realized visible states. -/
theorem UnifiedStateField.generator_on_visible
    {Index Time Carrier Law : Type}
    {data : AnchoredCurrentObject Index Time Carrier Law}
    (field : UnifiedStateField data) :
    ∀ role : VisibleCarrierRole,
      ∀ v : data.visible role,
        data.bridge.generator.toFun (field.visibleRealize role v) =
          field.visibleRealize role ((data.quotient role).evolve v) := by
  intro role v
  symm
  exact field.evolve_realized role v

/-- Surface theorem for the unified anchored detached current object. The
flagship equation is forced from one common selected-cut state field, with the
same matched selected generator transporting every visible role. -/
theorem UnifiedAnchoredCurrentObject.surface
    {Index Time Carrier Law : Type}
    (data : UnifiedAnchoredCurrentObject Index Time Carrier Law) :
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
          data.toAutonomousAnchoredCurrentObject.toAnchoredAutonomyObject.toAnchoredLawForm.channelResidual role current =
            data.toAutonomousAnchoredCurrentObject.toAnchoredAutonomyObject.toAnchoredLawForm.channelRead role
              (data.toAutonomousAnchoredCurrentObject.toAnchoredAutonomyObject.toAnchoredLawForm.returnedDefect current)) ∧
      (∀ role : VisibleCarrierRole,
        ∀ v : data.object.visible role,
          data.object.bridge.generator.toFun
            (data.stateField.visibleRealize role v) =
              data.stateField.visibleRealize role
                ((data.object.quotient role).evolve v)) := by
  obtain ⟨hcurrent, hdirret, haut, hmin, hexact, hforced, htransport, hlaw, hresidual,
    _hpointwise⟩ :=
    data.toAutonomousAnchoredCurrentObject.toAnchoredAutonomyObject.surface
  exact
    ⟨hcurrent,
      hdirret,
      haut,
      hmin,
      hexact,
      hforced,
      htransport,
      by
        intro role current
        exact UnifiedStateField.transportCompatible data.stateField current,
      hresidual,
      by
        intro role v
        exact UnifiedStateField.generator_on_visible data.stateField role v⟩

/-- The autonomy package already forces the unified state-field package. -/
theorem AutonomousAnchoredCurrentObject.unifiedSurface
    {Index Time Carrier Law : Type}
    (data : AutonomousAnchoredCurrentObject Index Time Carrier Law) :
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
            (data.toUnifiedAnchoredCurrentObject.stateField.visibleRealize role v) =
              data.toUnifiedAnchoredCurrentObject.stateField.visibleRealize role
                ((data.object.quotient role).evolve v)) := by
  exact data.toUnifiedAnchoredCurrentObject.surface

end ClosureCurrent

end CoherenceCalculus
