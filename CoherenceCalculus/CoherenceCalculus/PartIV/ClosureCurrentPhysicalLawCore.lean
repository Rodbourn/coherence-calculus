import CoherenceCalculus.PartIV.ClosureCurrentTargetBridgeCore
import CoherenceCalculus.PartIV.ClosureCurrentTrajectoryCore
import CoherenceCalculus.PartIV.ClosureCurrentFlagshipAnalyticCore
import CoherenceCalculus.PartIV.ClosureCurrentPhysicalEquationCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentPhysicalLawCore

Public Part II temporal realization law surface.

The public Part II law now starts from temporal realization rather than from a
least-motion-first coherent-law slogan. Physical time is read as the faithful
visible realization of ordered persistence on one coherent bundle. A second
local law, terminal exactification, is then read on a fixed selected bridge:
exact local closure is terminal, and the exactified assembled state is fixed by
the matched selected generator. A third law, endpoint completion, then says
that after terminal exactification the same bridge is microscopically complete:
the law-native fixed four-state assembly carries one boundary-complete
completion law on the same bridge and physical principle. From that explicit
three-law surface the endpoint-complete strong microscopic package and the
recognizable flagship equations follow. A detached flagship package,
introduced separately below, remains only as an alternative completion-side
normal form on the same realized datum.
-/

namespace ClosureCurrent

/-- Public Part II temporal realization law. Physical time is the faithful
visible realization of ordered persistence on a coherent bundle. The formal
surface keeps the realized same-bundle physical principle together with the
common closure transport on the faithful cut class itself, so the law already
records the horizon-preserving class invariance stated in Chapter 10. -/
structure TemporalRealizationLaw (_Index Time Carrier Law : Type)
    extends PhysicalRealizationPrinciple Time Carrier Law where
  realizedClassClosureTransport :
    ClosureClassTransport
      Time Carrier Law
      selectedLaw.selection
      selectedLaw.endpointClosureClass

/-- Detached flagship package on top of the public temporal realization law:
the same realized temporal law together with a detached no-stage completion law
on that same realized datum and its canonical carrier faces. This is an
alternative completion-side normal-form presentation, not part of the explicit
three-law Part II surface itself. -/
structure DetachedFlagshipPackage
    (Index Time Carrier Law : Type) where
  temporalLaw : TemporalRealizationLaw Index Time Carrier Law
  completionLaw : LocalEventFourStateCompletionLaw Index Time Carrier Law
  samePhysicalPrinciple :
    completionLaw.fourStateLaw.framed.object.physicalPrinciple =
      temporalLaw.toPhysicalRealizationPrinciple
  carrierFaces : FlagshipEndpointWitnesses completionLaw

/-- Derived same-bundle coherent-law surface read from the temporal
realization law. This forgets the explicit realized-class transport and keeps
only the underlying physical realization principle. -/
abbrev CoherentRealizationLaw (_Index Time Carrier Law : Type) :=
  PhysicalRealizationPrinciple Time Carrier Law

/-- Bare temporal kernel beneath the public temporal law: one exact visible law
on one coherent bundle together with exchange/return-only visible source,
internal elimination, and no exogenous constitutive completion. Least motion
and the sharper interface-localization clauses are not yet part of this
kernel. -/
structure TemporalRealizationKernel (Time Carrier Law : Type) where
  selectedLaw : SelectedVisibleEffectiveLaw Time Carrier Law
  exactVisibleOnRealizedCut :
    exactVisibleOnCut
      (selectedLaw.selection.realization.tower.π selectedLaw.selection.horizon)
      (selected_observed_law selectedLaw.selection).op
  observableDynamicsExactlySelectedLaw : Prop
  sameCoherentBundle : Prop
  observerCovariance : Prop
  visibleSourcesOnlyExchangeBoundaryReentry : Prop
  zeroNetInternalCreationOnClosedSystems : Prop
  onlyReturnActs : Prop
  visibleForcingIsReturnedResidual : Prop
  observableIrreversibilityIsUnrecoveredResidual : Prop
  selectedLawObtainedByResidualElimination : Prop
  noExogenousConstitutiveCompletion : Prop
  apparentConstitutiveTermsAreReturnedResidual : Prop
  observableDynamicsExactlySelectedLaw_valid :
    observableDynamicsExactlySelectedLaw
  sameCoherentBundle_valid : sameCoherentBundle
  observerCovariance_valid : observerCovariance
  visibleSourcesOnlyExchangeBoundaryReentry_valid :
    visibleSourcesOnlyExchangeBoundaryReentry
  zeroNetInternalCreationOnClosedSystems_valid :
    zeroNetInternalCreationOnClosedSystems
  onlyReturnActs_valid : onlyReturnActs
  visibleForcingIsReturnedResidual_valid :
    visibleForcingIsReturnedResidual
  observableIrreversibilityIsUnrecoveredResidual_valid :
    observableIrreversibilityIsUnrecoveredResidual
  selectedLawObtainedByResidualElimination_valid :
    selectedLawObtainedByResidualElimination
  noExogenousConstitutiveCompletion_valid :
    noExogenousConstitutiveCompletion
  apparentConstitutiveTermsAreReturnedResidual_valid :
    apparentConstitutiveTermsAreReturnedResidual

namespace TemporalRealizationKernel

/-- The bare temporal kernel already carries the exact visible law, same-bundle
realization, exchange/return source grammar, and self-sufficient visible
closure needed for the first law-bearing surface. -/
theorem surface
    {Time Carrier Law : Type}
    (data : TemporalRealizationKernel Time Carrier Law) :
    exactVisibleOnCut
      (data.selectedLaw.selection.realization.tower.π
        data.selectedLaw.selection.horizon)
      (selected_observed_law data.selectedLaw.selection).op ∧
      data.observableDynamicsExactlySelectedLaw ∧
      data.sameCoherentBundle ∧
      data.observerCovariance ∧
      data.visibleSourcesOnlyExchangeBoundaryReentry ∧
      data.zeroNetInternalCreationOnClosedSystems ∧
      data.onlyReturnActs ∧
      data.visibleForcingIsReturnedResidual ∧
      data.observableIrreversibilityIsUnrecoveredResidual ∧
      data.selectedLawObtainedByResidualElimination ∧
      data.noExogenousConstitutiveCompletion ∧
      data.apparentConstitutiveTermsAreReturnedResidual := by
  exact
    ⟨data.exactVisibleOnRealizedCut,
      data.observableDynamicsExactlySelectedLaw_valid,
      data.sameCoherentBundle_valid,
      data.observerCovariance_valid,
      data.visibleSourcesOnlyExchangeBoundaryReentry_valid,
      data.zeroNetInternalCreationOnClosedSystems_valid,
      data.onlyReturnActs_valid,
      data.visibleForcingIsReturnedResidual_valid,
      data.observableIrreversibilityIsUnrecoveredResidual_valid,
      data.selectedLawObtainedByResidualElimination_valid,
      data.noExogenousConstitutiveCompletion_valid,
      data.apparentConstitutiveTermsAreReturnedResidual_valid⟩

/-- The coherent realization surface is already visible on the bare temporal
kernel. -/
theorem coherentRealizationSurface
    {Time Carrier Law : Type}
    (data : TemporalRealizationKernel Time Carrier Law) :
    exactVisibleOnCut
      (data.selectedLaw.selection.realization.tower.π
        data.selectedLaw.selection.horizon)
      (selected_observed_law data.selectedLaw.selection).op ∧
      data.observableDynamicsExactlySelectedLaw ∧
      data.sameCoherentBundle ∧
      data.observerCovariance ∧
      data.visibleSourcesOnlyExchangeBoundaryReentry ∧
      data.zeroNetInternalCreationOnClosedSystems ∧
      data.onlyReturnActs ∧
      data.visibleForcingIsReturnedResidual ∧
      data.observableIrreversibilityIsUnrecoveredResidual ∧
      data.noExogenousConstitutiveCompletion := by
  rcases data.surface with
    ⟨hexact, hobs, hbundle, hcov, hexchange, hzero, hreturn, hforcing, hirr,
      _helim, hnoexo, _happ⟩
  exact ⟨hexact, hobs, hbundle, hcov, hexchange, hzero, hreturn, hforcing, hirr, hnoexo⟩

/-- The bare temporal kernel already closes the selected-cut law-side surface;
least-motion is not used at this stage. -/
theorem selectedCutCompletionSurface
    {Time Carrier Law : Type}
    (data : TemporalRealizationKernel Time Carrier Law) :
    exactVisibleOnCut
      (data.selectedLaw.selection.realization.tower.π
        data.selectedLaw.selection.horizon)
      (selected_observed_law data.selectedLaw.selection).op ∧
      data.noExogenousConstitutiveCompletion ∧
      data.apparentConstitutiveTermsAreReturnedResidual := by
  rcases data.surface with
    ⟨hexact, _hobs, _hbundle, _hcov, _hexchange, _hzero, _hreturn, _hforcing,
      _hirr, _helim, hnoexo, happ⟩
  exact ⟨hexact, hnoexo, happ⟩

end TemporalRealizationKernel

/-- Completion-side normal form on the detached flagship lane. This is the
endpoint-complete detached no-stage package, not the public temporal law
itself. -/
abbrev CoherentRealizationNormalForm (Index Time Carrier Law : Type) :=
  StrongMicroscopicLaw Index Time Carrier Law

/-- Completion-side candidate law with aggregate flagship boundary closure on
the same no-stage completion witness. Unlike `StrongMicroscopicLaw`, this keeps
the remaining flagship datum as a proposition rather than an explicit endpoint
witness bundle. -/
structure BoundaryMicroscopicLaw (Index Time Carrier Law : Type) where
  completionLaw : LocalEventFourStateCompletionLaw Index Time Carrier Law
  boundary : FlagshipBoundaryTarget completionLaw.toNoStageCompletionWitness

namespace BoundaryMicroscopicLaw

/-- The boundary-form candidate law already yields one endpoint-complete strong
microscopic package on the same completion law, and therefore the analytic
flagship surface and exact physical equation field. -/
theorem surface
    {Index Time Carrier Law : Type}
    (data : BoundaryMicroscopicLaw Index Time Carrier Law) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw = data.completionLaw ∧
        PartIVLawCompletionStatement strong.completionLaw.toNaturalOperatorCompletion ∧
        AnalyticFlagshipSurface strong ∧
        PhysicalEquationSurface strong := by
  rcases
      data.completionLaw.toNoStageCompletionWitness.flagshipSurfaceOfBoundaryTarget
        data.boundary with
    ⟨endpointWitnesses, hcompletion, _hphase, _hwave, _hgauge, _hgeometric⟩
  let strong : StrongMicroscopicLaw Index Time Carrier Law :=
    { completionLaw := data.completionLaw
      endpointWitnesses := endpointWitnesses }
  refine ⟨strong, rfl, ?_, ?_, ?_⟩
  · simpa [strong] using hcompletion
  · exact LocalEventFourStateFlagshipLaw.analyticSurface strong
  · exact LocalEventFourStateFlagshipLaw.physicalEquationSurface strong

/-- A boundary-form candidate law is determined by its completion law. The
remaining boundary field is a proposition on the canonical witness, so once
the completion law agrees the candidate laws themselves agree. -/
theorem eq_of_completionLaw_eq
    {Index Time Carrier Law : Type}
    {data other : BoundaryMicroscopicLaw Index Time Carrier Law}
    (hcompletion : data.completionLaw = other.completionLaw) :
    data = other := by
  cases data
  cases other
  cases hcompletion
  simp

end BoundaryMicroscopicLaw

/-- Smaller boundary-side candidate law on one fixed current-side four-state
assembly. Unlike `BoundaryMicroscopicLaw`, this retains only the remaining Step
4 alignment datum above that fixed law-native assembly; the completion law is
reconstructed from the assembly/alignment pair, and the remaining flagship
datum is boundary closure on its canonical witness. This is the smallest law
object currently suggested by the split completion bridge. -/
structure CompletionBoundaryLaw
    (Index Time Carrier Law : Type)
    (sectorLaw : ConstructiveSectorLaw Index Time Carrier Law)
    (assembly : FourStateAssembly sectorLaw) where
  alignment : CompletionAlignment sectorLaw
  boundary : let completionLaw :=
      (assembly.toNoStageCompletionBridge alignment).toLocalEventFourStateCompletionLaw
    FlagshipBoundaryTarget completionLaw.toNoStageCompletionWitness

namespace CompletionBoundaryLaw

/-- Reconstruct the corresponding no-stage completion law from the fixed
assembly/alignment pair. -/
def toCompletionLaw
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    {assembly : FourStateAssembly sectorLaw}
    (data : CompletionBoundaryLaw Index Time Carrier Law sectorLaw assembly) :
    LocalEventFourStateCompletionLaw Index Time Carrier Law :=
  (assembly.toNoStageCompletionBridge data.alignment).toLocalEventFourStateCompletionLaw

/-- Read the corresponding boundary-form microscopic law. -/
def toBoundaryMicroscopicLaw
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    {assembly : FourStateAssembly sectorLaw}
    (data : CompletionBoundaryLaw Index Time Carrier Law sectorLaw assembly) :
    BoundaryMicroscopicLaw Index Time Carrier Law where
  completionLaw := data.toCompletionLaw
  boundary := data.boundary

/-- On one fixed four-state assembly, the smaller boundary-side candidate law
is determined by its remaining Step 4 alignment. The boundary field is a
proposition on the canonical witness, so once the alignment agrees the laws
themselves agree. -/
theorem eq_of_alignment_eq
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    {assembly : FourStateAssembly sectorLaw}
    {data other : CompletionBoundaryLaw Index Time Carrier Law sectorLaw assembly}
    (halignment : data.alignment = other.alignment) :
    data = other := by
  cases data
  cases other
  cases halignment
  simp

/-- The smaller completion-boundary law already yields a strong microscopic
package on the same reconstructed completion law. -/
theorem surface
    {Index Time Carrier Law : Type}
    {sectorLaw : ConstructiveSectorLaw Index Time Carrier Law}
    {assembly : FourStateAssembly sectorLaw}
    (data : CompletionBoundaryLaw Index Time Carrier Law sectorLaw assembly) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw = data.toCompletionLaw ∧
        PartIVLawCompletionStatement strong.completionLaw.toNaturalOperatorCompletion ∧
        AnalyticFlagshipSurface strong ∧
        PhysicalEquationSurface strong := by
  exact data.toBoundaryMicroscopicLaw.surface

end CompletionBoundaryLaw

namespace TemporalRealizationLaw

private def trivialConstructivePairExchangeCarrier : PairExchangeCarrier where
  Value := PUnit
  Stock := PUnit
  zero := PUnit.unit
  reverse := fun _ => PUnit.unit
  stock := fun _ => PUnit.unit
  reverse_involutive := by
    intro x
    cases x
    rfl
  reverse_zero := rfl
  stock_reverse := by
    intro x
    cases x
    rfl

private def trivialConstructivePairExchangeCurrent :
    PairExchangeCurrent trivialConstructivePairExchangeCarrier PUnit where
  value := fun _ _ => PUnit.unit
  diagonal_zero := by
    intro a
    cases a
    rfl
  swap_reverse := by
    intro a b
    cases a
    cases b
    rfl

private def trivialConstructiveVisibleQuotient :
    VisibleQuotient trivialConstructivePairExchangeCarrier PUnit PUnit where
  read := fun _ => PUnit.unit
  evolve := fun _ => PUnit.unit
  autonomousReadout := True
  minimalNontrivial := True
  autonomousReadout_valid := trivial
  minimalNontrivial_valid := trivial

private def trivialConstructiveExactifier :
    EventExactifier trivialConstructivePairExchangeCarrier PUnit where
  exactify := fun _ => trivialConstructivePairExchangeCurrent
  returnedDefect := fun _ => trivialConstructivePairExchangeCurrent
  stockPreserved := True
  reverseCompatible := True
  relabelingEquivariant := True
  localLossless := True
  returnedDefectVisibleResidual := True
  stockPreserved_valid := trivial
  reverseCompatible_valid := trivial
  relabelingEquivariant_valid := trivial
  localLossless_valid := trivial
  returnedDefectVisibleResidual_valid := trivial

private def lawNativeClosureTransport
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    ClosureClassTransport
      Time Carrier Law
      bridge.selectedBridge.observer.selection
      data.selectedLaw.endpointClosureClass where
  sameSelection := by
    intro observer hsame
    have hsame' : observer.selection = data.selectedLaw.selection := by
      exact hsame.trans hsel.symm
    exact data.realizedClassClosureTransport.sameSelection observer hsame'

private def lawNativeConstructiveAnchorCurrentLaw
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    ConstructiveAnchorCurrentLaw Index Time Carrier Law where
  bridge := bridge
  physicalPrinciple := data.toPhysicalRealizationPrinciple
  sameSelectedLawAsBridge := hsel
  currentCarrier := trivialConstructivePairExchangeCarrier
  Leg := PUnit
  current := trivialConstructivePairExchangeCurrent
  visible := fun _ => PUnit
  quotient := fun _ => trivialConstructiveVisibleQuotient
  sameAnchoredContinuumClosureClass := by
    exact (lawNativeClosureTransport data bridge hsel).sameSelection
      bridge.selectedBridge.observer
      rfl
  firstStableBulkEventHasFourLegs := True
  sixPairSlots := balancedClosureSlotCount closureStableDimension = 6
  exactifier := trivialConstructiveExactifier
  firstStableBulkEventHasFourLegs_valid := trivial
  sixPairSlots_valid := forced_six_slot_balanced_carrier

private def lawNativeConstructiveCurrentLaw
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    ConstructiveCurrentLaw Index Time Carrier Law :=
  (lawNativeConstructiveAnchorCurrentLaw data bridge hsel).toConstructiveCurrentLaw
    (lawNativeClosureTransport data bridge hsel)

/-- The bare temporal kernel read from the public temporal realization law. -/
def toTemporalRealizationKernel
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law) :
    TemporalRealizationKernel Time Carrier Law :=
  { selectedLaw := data.selectedLaw
    exactVisibleOnRealizedCut := data.exactVisibleSelectedLawOnLeastMotionCut
    observableDynamicsExactlySelectedLaw := data.observableDynamicsExactlySelectedLaw
    sameCoherentBundle := data.sameCoherentBundle
    observerCovariance := data.observerCovariance
    visibleSourcesOnlyExchangeBoundaryReentry :=
      data.visibleSourcesOnlyExchangeBoundaryReentry
    zeroNetInternalCreationOnClosedSystems :=
      data.zeroNetInternalCreationOnClosedSystems
    onlyReturnActs := data.onlyReturnActs
    visibleForcingIsReturnedResidual := data.visibleForcingIsReturnedResidual
    observableIrreversibilityIsUnrecoveredResidual :=
      data.observableIrreversibilityIsUnrecoveredResidual
    selectedLawObtainedByResidualElimination :=
      data.selectedLawObtainedByResidualElimination
    noExogenousConstitutiveCompletion := data.noExogenousConstitutiveCompletion
    apparentConstitutiveTermsAreReturnedResidual :=
      data.apparentConstitutiveTermsAreReturnedResidual
    observableDynamicsExactlySelectedLaw_valid :=
      data.observableDynamicsExactlySelectedLaw_valid
    sameCoherentBundle_valid := data.sameCoherentBundle_valid
    observerCovariance_valid := data.observerCovariance_valid
    visibleSourcesOnlyExchangeBoundaryReentry_valid :=
      data.visibleSourcesOnlyExchangeBoundaryReentry_valid
    zeroNetInternalCreationOnClosedSystems_valid :=
      data.zeroNetInternalCreationOnClosedSystems_valid
    onlyReturnActs_valid := data.onlyReturnActs_valid
    visibleForcingIsReturnedResidual_valid :=
      data.visibleForcingIsReturnedResidual_valid
    observableIrreversibilityIsUnrecoveredResidual_valid :=
      data.observableIrreversibilityIsUnrecoveredResidual_valid
    selectedLawObtainedByResidualElimination_valid :=
      data.selectedLawObtainedByResidualElimination_valid
    noExogenousConstitutiveCompletion_valid :=
      data.noExogenousConstitutiveCompletion_valid
    apparentConstitutiveTermsAreReturnedResidual_valid :=
      data.apparentConstitutiveTermsAreReturnedResidual_valid }

/-- The public temporal law is already the primitive temporal realization
surface: one exact visible law on one coherent bundle together with the
exchange/return and closure grammar. -/
theorem surface
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law) :
    exactVisibleOnCut
      (data.selectedLaw.selection.realization.tower.π
        data.selectedLaw.selection.horizon)
      (selected_observed_law data.selectedLaw.selection).op ∧
      data.intrinsicallyClosedOnLeastMotionCut ∧
      data.noExogenousConstitutiveCompletion ∧
      data.apparentConstitutiveTermsAreReturnedResidual ∧
      data.observableDynamicsExactlySelectedLaw ∧
      data.sameCoherentBundle ∧
      data.lawClauses.observerCovariance ∧
      data.lawClauses.leastMotionFaithfulCutUnique ∧
      data.lawClauses.visibleSourcesOnlyExchangeBoundaryReentry ∧
      data.lawClauses.zeroNetInternalCreationOnClosedSystems ∧
      data.residualReturn.onlyReturnActs ∧
      data.residualReturn.visibleForcingIsReturnedResidual ∧
      data.residualReturn.observableIrreversibilityIsUnrecoveredResidual ∧
      data.residualReturn.residualLocalizesOnUniqueInterface ∧
      data.residualReturn.selectedLawObtainedByResidualElimination := by
  exact physical_realization_principle data.toPhysicalRealizationPrinciple

/-- The public temporal law already records the common continuum-closure
transport on the realized faithful cut class. -/
theorem closureTransportSurface
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law) :
    ∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
      observer.selection = data.selectedLaw.selection →
        data.selectedLaw.endpointClosureClass = observer.continuumClass := by
  intro observer hsel
  exact data.realizedClassClosureTransport.sameSelection observer hsel

/-- The coherent realization law is the same temporal realization data read as
the public same-bundle law surface on the realized class. -/
def toCoherentRealizationLaw
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law) :
    CoherentRealizationLaw Index Time Carrier Law :=
  data.toPhysicalRealizationPrinciple

/-- The temporal realization law already determines the coherent same-bundle
law surface on the realized faithful cut class. -/
theorem coherentRealizationSurface
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law) :
    exactVisibleOnCut
        (data.selectedLaw.selection.realization.tower.π
          data.selectedLaw.selection.horizon)
        (selected_observed_law
          data.selectedLaw.selection).op ∧
      data.observableDynamicsExactlySelectedLaw ∧
      data.sameCoherentBundle ∧
      data.observerCovariance ∧
      data.visibleSourcesOnlyExchangeBoundaryReentry ∧
      data.zeroNetInternalCreationOnClosedSystems ∧
      data.onlyReturnActs ∧
      data.visibleForcingIsReturnedResidual ∧
      data.observableIrreversibilityIsUnrecoveredResidual ∧
      data.noExogenousConstitutiveCompletion := by
  exact data.toTemporalRealizationKernel.coherentRealizationSurface

/-- One exact visible law on one coherent bundle, read directly from the
temporal realization law. -/
theorem realizationSurface
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law) :
    exactVisibleOnCut
        (data.selectedLaw.selection.realization.tower.π
          data.selectedLaw.selection.horizon)
        (selected_observed_law
          data.selectedLaw.selection).op ∧
      data.observableDynamicsExactlySelectedLaw ∧
      data.sameCoherentBundle ∧
      data.observerCovariance := by
  have h := data.surface
  rcases h with
    ⟨hexact, _hclosed, _hnoConst, _happarent, hobs, hbundle, hcov, _hleast,
      _hexchange, _hzero, _hreturn, _hforcing, _hirr, _hloc, _helim⟩
  exact ⟨hexact, hobs, hbundle, hcov⟩

/-- Same-bundle exchange / return surface read directly from the temporal
realization law. -/
theorem exchangeReturnSurface
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law) :
    data.visibleSourcesOnlyExchangeBoundaryReentry ∧
      data.zeroNetInternalCreationOnClosedSystems ∧
      data.onlyReturnActs ∧
      data.visibleForcingIsReturnedResidual ∧
      data.observableIrreversibilityIsUnrecoveredResidual ∧
      data.residualLocalizesOnUniqueInterface ∧
      data.selectedLawObtainedByResidualElimination := by
  rcases data.surface with
    ⟨_hexact, _hclosed, _hnoexo, _happ, _hobs, _hbundle, _hcov, _hleast,
      hexchange, hzero, hreturn, hforcing, hirr, hloc, helim⟩
  exact ⟨hexchange, hzero, hreturn, hforcing, hirr, hloc, helim⟩

/-- Self-sufficient selected-cut closure read directly from the temporal
realization law. -/
theorem selectedCutCompletionSurface
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law) :
    exactVisibleOnCut
        (data.selectedLaw.selection.realization.tower.π
          data.selectedLaw.selection.horizon)
        (selected_observed_law
          data.selectedLaw.selection).op ∧
      data.intrinsicallyClosedOnLeastMotionCut ∧
      data.noExogenousConstitutiveCompletion ∧
      data.apparentConstitutiveTermsAreReturnedResidual := by
  have hkernel := data.toTemporalRealizationKernel.selectedCutCompletionSurface
  rcases hkernel with ⟨hexact, hnoexo, happ⟩
  exact
    ⟨hexact,
      data.intrinsicallyClosedOnLeastMotionCut_valid,
      hnoexo,
      happ⟩

/-- On any microscopic closure law carrying the same public temporal
realization law, the common grammar and bundle-intrinsicity clauses of the
detached constructive lane are already supplied by that public law itself. -/
theorem constructiveClauseSurface
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (_hsame : law.physicalPrinciple = data.toPhysicalRealizationPrinciple) :
    ConstructiveMicroscopicClausesTarget law := by
  exact law.constructiveMicroscopicClausesTargetOfPhysicalPrinciple

/-- On any microscopic closure law carrying the same public temporal
realization law, the common selected-cut closure transport is already supplied
by the realized-class transport of that public law itself. -/
theorem originReadoutClosureSurface
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hsame : law.physicalPrinciple = data.toPhysicalRealizationPrinciple) :
    OriginReadoutClosureTarget law := by
  refine ⟨{ sameSelection := ?_ }⟩
  intro observer hsel
  have hlawsel :
      law.bridge.selectedBridge.observer.selection = data.selectedLaw.selection := by
    calc
      law.bridge.selectedBridge.observer.selection
          = law.physicalPrinciple.selectedLaw.selection := by
              symm
              exact law.sameSelectedLawAsBridge
      _ = data.selectedLaw.selection := by
            simp [hsame]
  have hsel' : observer.selection = data.selectedLaw.selection := by
    exact hsel.trans hlawsel
  simpa [hsame] using data.realizedClassClosureTransport.sameSelection observer hsel'

/-- If a microscopic closure law carries the public temporal realization law
and already meets the constructive current target, then the detached
selected-bundle forcing surface follows with no extra detached clause package.
-/
theorem originTargetSurfaceOfConstructiveCurrentTarget
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (_hsame : law.physicalPrinciple = data.toPhysicalRealizationPrinciple)
    (hcurrent : ConstructiveCurrentTarget law) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      realized_generator_carries_bedrock_law law.bridge.generator ∧
      AutonomousHorizon
        law.bridge.selectedBridge.observer.selection.realization.tower
        law.bridge.selectedBridge.observer.selection.horizon
        law.bridge.generator ∧
      horizonFiberInvariant
        law.bridge.selectedBridge.observer.selection.realization.tower
        law.bridge.selectedBridge.observer.selection.horizon
        law.bridge.generator := by
  exact law.originTargetSurfaceOfConstructiveCurrentTarget hcurrent

/-- Under the same hypothesis, the constructive microscopic target itself is
already recovered from the constructive current target alone. -/
theorem constructiveMicroscopicTargetOfConstructiveCurrentTarget
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (_hsame : law.physicalPrinciple = data.toPhysicalRealizationPrinciple)
    (hcurrent : ConstructiveCurrentTarget law) :
    ConstructiveMicroscopicTarget law := by
  exact law.constructiveMicroscopicTargetOfConstructiveCurrentTarget hcurrent

/-- Once the public temporal law already supplies the realized-class closure
transport and the common law-native clauses, the detached selected-bundle
forcing seam drops to the selected-anchor readout target alone. -/
theorem originReadoutTargetOfOriginReadoutAnchorTarget
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hsame : law.physicalPrinciple = data.toPhysicalRealizationPrinciple)
    (hanchor : OriginReadoutAnchorTarget law) :
    OriginReadoutTarget law := by
  exact
    law.originReadoutTargetOfParts
      (law.originReadoutTransportTargetOfParts
        hanchor
        (data.originReadoutClosureSurface law hsame))
      (law.originReadoutClausesTargetOfConstructiveMicroscopicClausesTarget
        (data.constructiveClauseSurface law hsame))

/-- The selected-anchor readout target is canonical, so the public temporal law
already determines the full detached origin-readout target on any microscopic
closure law carrying that same physical principle. -/
theorem originReadoutTargetSurface
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hsame : law.physicalPrinciple = data.toPhysicalRealizationPrinciple) :
    OriginReadoutTarget law := by
  exact
    data.originReadoutTargetOfOriginReadoutAnchorTarget
      law
      hsame
      law.trivialOriginReadoutAnchorTarget

/-- Under the same hypothesis, the detached selected-bundle/readout witness is
already recovered from the selected-anchor readout target alone. -/
theorem originClosureTargetOfOriginReadoutAnchorTarget
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hsame : law.physicalPrinciple = data.toPhysicalRealizationPrinciple)
    (hanchor : OriginReadoutAnchorTarget law) :
    OriginClosureTarget law := by
  exact
    law.originClosureTargetOfReadout
      (data.originReadoutTargetOfOriginReadoutAnchorTarget law hsame hanchor)

/-- The public temporal law already determines the detached selected-bundle /
readout witness on any microscopic closure law carrying that same physical
principle. -/
theorem originClosureSurface
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hsame : law.physicalPrinciple = data.toPhysicalRealizationPrinciple) :
    OriginClosureTarget law := by
  exact
    law.originClosureTargetOfReadout
      (data.originReadoutTargetSurface law hsame)

/-- Under the same hypothesis, the detached selected-bundle forcing surface is
already recovered from the selected-anchor readout target alone. -/
theorem originTargetSurfaceOfOriginReadoutAnchorTarget
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hsame : law.physicalPrinciple = data.toPhysicalRealizationPrinciple)
    (hanchor : OriginReadoutAnchorTarget law) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      realized_generator_carries_bedrock_law law.bridge.generator ∧
      AutonomousHorizon
        law.bridge.selectedBridge.observer.selection.realization.tower
        law.bridge.selectedBridge.observer.selection.horizon
        law.bridge.generator ∧
      horizonFiberInvariant
        law.bridge.selectedBridge.observer.selection.realization.tower
        law.bridge.selectedBridge.observer.selection.horizon
        law.bridge.generator := by
  exact
    law.originReadoutTargetSurface
      (data.originReadoutTargetOfOriginReadoutAnchorTarget law hsame hanchor)

/-- The public temporal law already determines the detached selected-bundle
forcing surface on any microscopic closure law carrying that same physical
principle. No extra detached origin-side datum remains at this stage. -/
theorem originTargetSurface
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hsame : law.physicalPrinciple = data.toPhysicalRealizationPrinciple) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      realized_generator_carries_bedrock_law law.bridge.generator ∧
      AutonomousHorizon
        law.bridge.selectedBridge.observer.selection.realization.tower
        law.bridge.selectedBridge.observer.selection.horizon
        law.bridge.generator ∧
      horizonFiberInvariant
        law.bridge.selectedBridge.observer.selection.realization.tower
        law.bridge.selectedBridge.observer.selection.horizon
        law.bridge.generator := by
  exact
    law.originReadoutTargetSurface
      (data.originReadoutTargetSurface law hsame)

/-- Once the public temporal law already supplies the realized-class closure
transport, the stronger detached constructive origin seam drops to the
selected-anchor current target alone. -/
theorem originTargetSurfaceOfConstructiveAnchorCurrentTarget
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hsame : law.physicalPrinciple = data.toPhysicalRealizationPrinciple)
    (hanchor : ConstructiveAnchorCurrentTarget law) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      realized_generator_carries_bedrock_law law.bridge.generator ∧
      AutonomousHorizon
        law.bridge.selectedBridge.observer.selection.realization.tower
        law.bridge.selectedBridge.observer.selection.horizon
        law.bridge.generator ∧
      horizonFiberInvariant
        law.bridge.selectedBridge.observer.selection.realization.tower
        law.bridge.selectedBridge.observer.selection.horizon
        law.bridge.generator := by
  exact
    law.originTargetSurfaceOfConstructiveAnchorCurrentTarget
      hanchor
      (data.originReadoutClosureSurface law hsame)
      (data.constructiveClauseSurface law hsame)

/-- Under the same hypothesis, the bundled constructive microscopic target is
already recovered from the selected-anchor current target alone. -/
theorem constructiveMicroscopicTargetOfConstructiveAnchorCurrentTarget
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hsame : law.physicalPrinciple = data.toPhysicalRealizationPrinciple)
    (hanchor : ConstructiveAnchorCurrentTarget law) :
    ConstructiveMicroscopicTarget law := by
  exact
    law.constructiveMicroscopicTargetOfConstructiveAnchorCurrentTargetAndClosure
      hanchor
      (data.originReadoutClosureSurface law hsame)

/-- Once a selected bridge datum is fixed on the same realized cut, the public
temporal law canonically determines a microscopic closure law on that bridge.
This removes the remaining current-side proposition packaging from the bridge
lane itself: the law-native current object already supplies the microscopic
surface there. -/
def microscopicClosureLawOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    MicroscopicClosureLaw Index Time Carrier Law :=
  (lawNativeConstructiveCurrentLaw data bridge hsel).toMicroscopicClosureLaw

/-- The bridge-native microscopic closure law carried by the public temporal
law uses exactly that same public physical realization principle. -/
theorem microscopicClosureLawOnBridge_samePhysicalPrinciple
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    (data.microscopicClosureLawOnBridge bridge hsel).physicalPrinciple =
      data.toPhysicalRealizationPrinciple := by
  rfl

/-- On a fixed selected bridge datum, the public temporal law already
determines the exact constructive current target for its own law-native
microscopic closure law. No extra detached current-side datum remains at this
stage. -/
theorem constructiveCurrentTargetOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    ConstructiveCurrentTarget (data.microscopicClosureLawOnBridge bridge hsel) := by
  exact ⟨lawNativeConstructiveCurrentLaw data bridge hsel, rfl⟩

/-- On a fixed selected bridge datum, the public temporal law therefore
already determines the full constructive microscopic target on that same
bridge. The first remaining detached seam lies strictly above the current-side
constructive layer. -/
theorem constructiveMicroscopicTargetOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    ConstructiveMicroscopicTarget
      (data.microscopicClosureLawOnBridge bridge hsel) := by
  let law := data.microscopicClosureLawOnBridge bridge hsel
  change ConstructiveMicroscopicTarget law
  exact
    law.constructiveMicroscopicTargetOfConstructiveCurrentTarget
      (data.constructiveCurrentTargetOnBridge bridge hsel)

/-- On a fixed selected bridge datum, the public temporal law already
determines the full constructive microscopic law on that same bridge. This is
the current-side detached law itself, not merely the existence-level target. -/
def constructiveMicroscopicLawOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    ConstructiveMicroscopicLaw Index Time Carrier Law := by
  let currentLaw := lawNativeConstructiveCurrentLaw data bridge hsel
  let law := currentLaw.toMicroscopicClosureLaw
  let clauses := law.lawNativeConstructiveMicroscopicClauses
  exact
    { toAnchoredCurrentTransport := currentLaw.toAnchoredCurrentTransport
      commonGrammar := law.lawNativeCommonGrammar
      firstStableBulkEventHasFourLegs := currentLaw.firstStableBulkEventHasFourLegs
      sixPairSlots := currentLaw.sixPairSlots
      exactifier := currentLaw.exactifier
      bundleArisesIntrinsicallyOnLeastMotionCut :=
        clauses.bundleArisesIntrinsicallyOnLeastMotionCut
      noCarrierWiseVisibilityHypotheses :=
        clauses.noCarrierWiseVisibilityHypotheses
      firstStableBulkEventHasFourLegs_valid :=
        currentLaw.firstStableBulkEventHasFourLegs_valid
      sixPairSlots_valid := currentLaw.sixPairSlots_valid
      hiddenCoherentLaw_valid := clauses.hiddenCoherentLaw_valid
      residualReturnFieldOnSelectedCut_valid :=
        clauses.residualReturnFieldOnSelectedCut_valid
      selectedVisibleLawPhysicallyRealized_valid :=
        clauses.selectedVisibleLawPhysicallyRealized_valid
      onlyReturnActsOnVisibleBundle_valid :=
        clauses.onlyReturnActsOnVisibleBundle_valid
      characteristicEndpointReduction_valid :=
        clauses.characteristicEndpointReduction_valid
      canonicalSectorGeneration_valid :=
        clauses.canonicalSectorGeneration_valid
      symmetryRigidMinimalClosure_valid :=
        clauses.symmetryRigidMinimalClosure_valid
      carrierLevelPhysicalLaw_valid :=
        clauses.carrierLevelPhysicalLaw_valid
      bundleArisesIntrinsicallyOnLeastMotionCut_valid :=
        clauses.bundleArisesIntrinsicallyOnLeastMotionCut_valid
      noCarrierWiseVisibilityHypotheses_valid :=
        clauses.noCarrierWiseVisibilityHypotheses_valid }

/-- The bridge-native constructive microscopic law still carries exactly the
same public physical realization principle. -/
theorem constructiveMicroscopicLawOnBridge_samePhysicalPrinciple
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    (data.constructiveMicroscopicLawOnBridge bridge hsel).physicalPrinciple =
      data.toPhysicalRealizationPrinciple := by
  rfl

/-- The bridge-native constructive microscopic law reduces to the bridge-native
microscopic closure law previously extracted from the temporal law. -/
theorem constructiveMicroscopicLawOnBridge_toMicroscopicClosureLaw
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    (data.constructiveMicroscopicLawOnBridge bridge hsel).toMicroscopicClosureLaw =
      data.microscopicClosureLawOnBridge bridge hsel := by
  rfl

/-- The origin-closure witness on a fixed selected bridge is already carried by
the bridge-native constructive microscopic law determined by the temporal law.
-/
def originClosureWitnessOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    OriginClosureWitness (data.microscopicClosureLawOnBridge bridge hsel) := by
  simpa [data.constructiveMicroscopicLawOnBridge_toMicroscopicClosureLaw
    bridge hsel] using
    (data.constructiveMicroscopicLawOnBridge bridge hsel).toOriginClosureWitness

/-- On a fixed selected bridge datum, the bridge-native origin witness already
determines the exact selected-bundle forcing object on that same bridge. -/
def selectedBundleForcingOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    SelectedBundleForcing Index Time Carrier Law :=
  (data.originClosureWitnessOnBridge bridge hsel).toSelectedBundleForcing

/-- On a fixed selected bridge datum, the public temporal law already
determines the active selected-bundle object itself, not merely the existence
of such an object. -/
def selectedBundleOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    IntrinsicSelectedBundleExistence Time Carrier Law :=
  (data.selectedBundleForcingOnBridge bridge hsel).toIntrinsicSelectedBundleExistence

/-- The temporal law therefore already determines the concrete local-event
object on any fixed selected bridge datum. -/
def localEventObjectOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    LocalEventObject Index Time Carrier Law :=
  (data.constructiveMicroscopicLawOnBridge bridge hsel).toLocalEventObject

/-- On a fixed selected bridge datum, the public temporal law already forces
the full active selected-bundle surface on that same bridge. -/
theorem selectedBundleSurfaceOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    let bundle := data.selectedBundleOnBridge bridge hsel
    bundle.bundleArisesIntrinsicallyOnLeastMotionCut ∧
      bundle.noCarrierWiseVisibilityHypotheses ∧
      (bundle.selectedSchurBridge.observer.selection.selectedProjection =
        selectedCandidateProjection bundle.selectedSchurBridge.observer.selection) ∧
      (bundle.selectedSchurBridge.observer.selection.selectedProjection =
        bundle.selectedSchurBridge.observer.selection.realization.tower.π
          bundle.selectedSchurBridge.observer.selection.horizon) ∧
      (bundle.physicalPrinciple.selectedLaw.selection =
        bundle.selectedSchurBridge.observer.selection) ∧
      (bundle.physicalPrinciple.selectedLaw.endpointClosureClass =
        bundle.selectedSchurBridge.observer.continuumClass) ∧
      (holographicImbalance 3 = SignedCount.ofNat 1) ∧
      bundle.selectedObservedBundle ∧
      bundle.bundleSharedByAllCarriers ∧
      bundle.sameSelectedEffectiveLawOnEachCarrier ∧
      bundle.carrierLevelIdentificationOnlyFinalStep := by
  simpa [selectedBundleOnBridge] using
    intrinsic_selected_bundle_existence (data.selectedBundleOnBridge bridge hsel)

/-- On a fixed selected bridge datum, the selected bundle already carries the
canonical visible carrier-generation package. -/
theorem canonicalGenerationSurfaceOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    let generation := (data.selectedBundleOnBridge bridge hsel).toCanonicalGeneration
    generation.scalarChannelVisible ∧
      generation.scalarChannelGeneratesPhase ∧
      generation.scalarChannelGeneratesWave ∧
      generation.balanceCompatibleCarrierGeneratesKinetic ∧
      generation.exactOneFormExchangeGeneratesGauge ∧
      generation.symmetricResponseGeneratesGeometry ∧
      generation.notPrimitiveDictionary := by
  simpa [selectedBundleOnBridge,
    IntrinsicSelectedBundleExistence.toCanonicalGeneration] using
    (data.selectedBundleOnBridge bridge hsel).canonicalGenerationSurface

/-- On a fixed selected bridge datum, the public temporal law already forces
the detached selected-bundle/readout witness on that same bridge. -/
theorem originClosureTargetOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    OriginClosureTarget (data.microscopicClosureLawOnBridge bridge hsel) := by
  simpa [data.constructiveMicroscopicLawOnBridge_toMicroscopicClosureLaw
    bridge hsel] using
    (data.constructiveMicroscopicLawOnBridge bridge hsel).originClosureTarget

/-- On a fixed selected bridge datum, the public temporal law already forces
the detached selected-bundle forcing surface on that same bridge. -/
theorem originTargetSurfaceOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      realized_generator_carries_bedrock_law
        (data.microscopicClosureLawOnBridge bridge hsel).bridge.generator ∧
      AutonomousHorizon
        (data.microscopicClosureLawOnBridge bridge hsel).bridge.selectedBridge.observer.selection.realization.tower
        (data.microscopicClosureLawOnBridge bridge hsel).bridge.selectedBridge.observer.selection.horizon
        (data.microscopicClosureLawOnBridge bridge hsel).bridge.generator ∧
      horizonFiberInvariant
        (data.microscopicClosureLawOnBridge bridge hsel).bridge.selectedBridge.observer.selection.realization.tower
        (data.microscopicClosureLawOnBridge bridge hsel).bridge.selectedBridge.observer.selection.horizon
        (data.microscopicClosureLawOnBridge bridge hsel).bridge.generator := by
  simpa [data.constructiveMicroscopicLawOnBridge_toMicroscopicClosureLaw
    bridge hsel] using
    (data.constructiveMicroscopicLawOnBridge bridge hsel).originTargetSurface

/-- On a fixed selected bridge datum, the public temporal law and the active
Part I continuation calculus already force the realized bedrock recurrence
profile on that same datum: the matched selected generator carries the bedrock
law, the unique residual interface occurs at `D = 3`, the balanced carrier has
six slots, and the intrinsic `[3,2,1]` channel profile is canonical there.

This is the strongest current certified recursive surface. It does not yet
identify the full Step 3 carrier-generation package, but it isolates the exact
bedrock profile that any such package would have to realize on the selected
bundle. -/
theorem bedrockRecurrenceSurfaceOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      realized_generator_carries_bedrock_law bridge.generator ∧
      AutonomousHorizon
        bridge.selectedBridge.observer.selection.realization.tower
        bridge.selectedBridge.observer.selection.horizon
        bridge.generator ∧
      horizonFiberInvariant
        bridge.selectedBridge.observer.selection.realization.tower
        bridge.selectedBridge.observer.selection.horizon
        bridge.generator ∧
      (holographicImbalance 3 = SignedCount.ofNat 1) ∧
      (balancedClosureSlotCount closureStableDimension = 6) ∧
      (natListSum [3, 2, 1] = balancedClosureSlotCount closureStableDimension) ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  obtain ⟨hbundle, hbedrock, haut, hfiber⟩ :=
    data.originTargetSurfaceOnBridge bridge hsel
  obtain ⟨hprofile, hcanonical⟩ := forced_intrinsic_channel_profile
  exact
    ⟨hbundle,
      hbedrock,
      haut,
      hfiber,
      forced_residual_interface_D3,
      forced_six_slot_balanced_carrier,
      hprofile,
      hcanonical⟩

/-- The strongest current certified recursive-realization ladder on a fixed
selected bridge pairs the unit-balanced `D = 2` spectral seed with the
selected-bundle bridge profile forced by the public temporal law: the seed
remains one-fiber and continuum-forced, the unique nontrivial residual
interface occurs at `D = 3`, and the selected `D = 4` bridge carries the
six-slot canonical `[3,2,1]` profile.

This is still weaker than full carrier generation. It does, however, isolate
the exact seed/interface/bulk ladder that any later Step 3 generation package
must realize on the same selected bridge. -/
theorem recursiveRealizationLadderOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection)
    (seed : D2SpectralSeedData Law) :
    Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
      seed.singleChannelUnitSeed ∧
      seed.oneFiberVisibleLaw ∧
      seed.repeatCyclesNoNewCarrier ∧
      seed.family.primitiveSupportGenerated ∧
      seed.primeData.samePrimeIndexMultiset ∧
      seed.continuumData.selfAdjointPositiveSemidefinite ∧
      ForcedContinuumLaw
        seed.continuumData.continuumClass
        seed.continuumData.target ∧
      realized_generator_carries_bedrock_law bridge.generator ∧
      AutonomousHorizon
        bridge.selectedBridge.observer.selection.realization.tower
        bridge.selectedBridge.observer.selection.horizon
        bridge.generator ∧
      horizonFiberInvariant
        bridge.selectedBridge.observer.selection.realization.tower
        bridge.selectedBridge.observer.selection.horizon
        bridge.generator ∧
      (holographicImbalance 3 = SignedCount.ofNat 1) ∧
      (balancedClosureSlotCount closureStableDimension = 6) ∧
      (natListSum [3, 2, 1] = balancedClosureSlotCount closureStableDimension) ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  obtain
      ⟨hseed,
        hone,
        hrepeat,
        hsupport,
        hprime,
        hpsd,
        hmem,
        hunique⟩ :=
    d2_spectral_seed_package seed
  obtain
      ⟨hbundle,
        hbedrock,
        haut,
        hfiber,
        hd3,
        hsix,
        hprofile,
        hcanonical⟩ :=
    data.bedrockRecurrenceSurfaceOnBridge bridge hsel
  have hcontinuum :
      ForcedContinuumLaw
        seed.continuumData.continuumClass
        seed.continuumData.target :=
    exact_discrete_to_continuum_forcing_principle
      seed.continuumData.continuumClass
      seed.continuumData.target
      hmem
      hunique
  exact
    ⟨hbundle,
      hseed,
      hone,
      hrepeat,
      hsupport,
      hprime,
      hpsd,
      hcontinuum,
      hbedrock,
      haut,
      hfiber,
      hd3,
      hsix,
      hprofile,
      hcanonical⟩

/-- On a fixed selected bridge datum, the public temporal law already realizes
the diophantine pair carrier behind the bridge-local event: the first stable
bulk event has four legs, the law-native hidden current lives on oriented pair
slots, and the finite carrier count is exactly `binomial 4 2 = 6`.

So the pair count is not an extra microscopic choice principle. It is the
counting formula for the law-native local pair carrier on that bridge. -/
theorem diophantinePairCarrierSurfaceOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    let obj := data.localEventObjectOnBridge bridge hsel
    obj.firstStableBulkEventHasFourLegs ∧
      obj.sixPairSlots ∧
      (∀ a b : obj.Leg,
        obj.current.value b a =
          obj.currentCarrier.reverse (obj.current.value a b)) ∧
      (closureStableDimension = 4) ∧
      (binomial closureStableDimension 2 = 6) := by
  dsimp
  refine
    ⟨(data.localEventObjectOnBridge bridge hsel).firstStableBulkEventHasFourLegs_valid,
      (data.localEventObjectOnBridge bridge hsel).sixPairSlots_valid,
      ?_,
      rfl,
      ?_⟩
  · intro a b
    exact (data.localEventObjectOnBridge bridge hsel).current.swap_reverse a b
  · simpa [balancedClosureSlotCount] using forced_six_slot_balanced_carrier

/-- Once the law-native local event realizes the diophantine six-slot pair
carrier on a fixed bridge, the Part I intrinsic six-slot channel calculus
already acts on that carrier through its canonical overlap law. So the local
pair carrier is no longer an open-ended microscopic object there: it already
has a canonical adjacency-invariant three-parameter/eigenvalue surface. -/
theorem diophantinePairCarrierIntrinsicChannelSurfaceOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    let A := localSlotOverlapLaw
    (data.localEventObjectOnBridge bridge hsel).sixPairSlots ∧
      IntrinsicAdjacencyInvariant A ∧
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
  dsimp
  refine
    ⟨(data.localEventObjectOnBridge bridge hsel).sixPairSlots_valid,
      localSlotOverlapLaw_intrinsic,
      localSlotOverlapLaw_channelSurface⟩

/-- On a fixed selected bridge datum, the law-native six-slot pair carrier is
already rigid at the intrinsic local-law level: the canonical overlap law has
one unique normal form with explicit parameter values `(2, 1, 0)`. This is
already forced by temporal realization on that bridge, before any terminal
exactification data are attached. -/
theorem pairCarrierLawSurfaceOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    (balancedClosureSlotCount closureStableDimension = 6) ∧
      (natListSum [3, 2, 1] = balancedClosureSlotCount closureStableDimension) ∧
      IsCanonicalLogicalProfile [3, 2, 1] ∧
      ∃ p : IntrinsicSlotParameters,
        (isIntrinsicNormalForm ClosureCurrent.localSlotOverlapLaw p ∧
          p.diagonal = SignedCount.ofNat 2 ∧
          p.adjacent = SignedCount.ofNat 1 ∧
          p.disjoint = SignedCount.zero) ∧
        ∀ q : IntrinsicSlotParameters,
          (isIntrinsicNormalForm ClosureCurrent.localSlotOverlapLaw q ∧
            q.diagonal = SignedCount.ofNat 2 ∧
            q.adjacent = SignedCount.ofNat 1 ∧
            q.disjoint = SignedCount.zero) →
          q = p := by
  obtain ⟨_hsix, _hoverlap, _hchannels⟩ :=
    data.diophantinePairCarrierIntrinsicChannelSurfaceOnBridge bridge hsel
  obtain ⟨_hbundle, _hbedrock, _haut, _hfiber, _hd3, _hsix, hsum, hprofile⟩ :=
    data.bedrockRecurrenceSurfaceOnBridge bridge hsel
  exact
    ⟨forced_six_slot_balanced_carrier,
      hsum,
      hprofile,
      ClosureCurrent.localSlotOverlapLaw_existsUniqueCanonicalNormalForm⟩

/-- On a fixed selected bridge datum, the law-native six-slot pair carrier is
already pointwise rigid: any candidate local six-slot law with the canonical
overlap normal form `(2, 1, 0)` agrees slot-by-slot with the canonical
law-native overlap law. This again lives already on the temporal realization
surface, before terminal exactification. -/
theorem pairCarrierLawPointwiseUniqueOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection)
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
    ∀ α β : LocalSlot, A α β = ClosureCurrent.localSlotOverlapLaw α β := by
  obtain ⟨_hsix, _hsum, _hprofile, _hlaw⟩ :=
    data.pairCarrierLawSurfaceOnBridge bridge hsel
  exact pointwise_eq_canonicalIntrinsicOverlapLaw_of_existsCanonicalNormalForm hA

/-- On a fixed selected bridge datum, the canonical six-slot pair carrier
already carries the exact intrinsic channel spectrum `(6, 0, 2)`. This is
forced on the temporal realization surface before any terminal exactification
data are attached. -/
theorem pairCarrierExactChannelSpectrumOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    intrinsicChannelEigenvalue1 canonicalIntrinsicOverlapParameters =
        SignedCount.ofNat 6 ∧
      intrinsicChannelEigenvalue2 canonicalIntrinsicOverlapParameters =
        SignedCount.zero ∧
      intrinsicChannelEigenvalue3 canonicalIntrinsicOverlapParameters =
        SignedCount.ofNat 2 := by
  obtain ⟨_hsix, _hsum, _hprofile, _hlaw⟩ :=
    data.pairCarrierLawSurfaceOnBridge bridge hsel
  exact canonicalIntrinsicOverlapLaw_exactChannelSpectrum

/-- On a fixed selected bridge datum, the distinguished `s12` fiber of the
law-native six-slot pair law already has exact reduced coordinates `(4, 0,
-2)`. This is the first anchored current-side coordinate package forced before
any terminal exactification data are attached. -/
theorem pairCarrierS12FiberCoordinatesOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    localSlotCoordinates
        (intrinsicLawFiber ClosureCurrent.localSlotOverlapLaw LocalSlot.s12) =
      ⟨SignedCount.ofNat 4, SignedCount.zero, SignedCount.negOfNat 2⟩ := by
  obtain ⟨_hsix, _hsum, _hprofile, _hlaw⟩ :=
    data.pairCarrierLawSurfaceOnBridge bridge hsel
  exact canonicalIntrinsicOverlapS12Fiber_coordinates

/-- On a fixed selected bridge datum, any intrinsic six-slot law in canonical
normal form `(2, 1, 0)` already has the full canonical anchor-fiber coordinate
family. This is the exact coordinate-level forcing theorem exported to the
current-side route before any terminal exactification data are attached. -/
theorem pairCarrierCanonicalNormalFormFiberCoordinatesOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection)
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
  let _ := hsel
  exact fiberCoordinates_of_existsCanonicalNormalForm hA

/-- On a fixed selected bridge datum, any intrinsic six-slot law in canonical
normal form `(2, 1, 0)` already has the canonical `s13` fiber coordinates
`(4, 0, -2)`. This is the minimal single-fiber coordinate forcing statement on
the current-side route before any terminal exactification data are attached. -/
theorem pairCarrierCanonicalNormalFormS13FiberCoordinatesOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection)
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
  let _ := hsel
  exact s13FiberCoordinates_of_existsCanonicalNormalForm hA

/-- On a fixed selected bridge datum, the law-native six-slot pair law already
has the full canonical anchor-fiber coordinate family. So the reduced
three-coordinate readout is forced simultaneously at every local anchor before
any terminal exactification data are attached. -/
theorem pairCarrierFiberCoordinatesOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    ∀ anchor : LocalSlot,
      localSlotCoordinates
          (intrinsicLawFiber ClosureCurrent.localSlotOverlapLaw anchor) =
        canonicalIntrinsicOverlapFiberCoordinates anchor := by
  obtain ⟨_hsix, _hsum, _hprofile, hlaw⟩ :=
    data.pairCarrierLawSurfaceOnBridge bridge hsel
  exact fiberCoordinates_of_existsCanonicalNormalForm hlaw

/-- On a fixed selected bridge datum, one canonical `s13` anchor fiber already
forces the full intrinsic six-slot law. This is the smallest exported
fiber-level rigidity statement available before any terminal exactification
data are attached. -/
theorem pairCarrierCanonicalS13FiberRigidityOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection)
    {A : LocalSlot → LocalSlot → SignedCount}
    (hA : IntrinsicAdjacencyInvariant A)
    (hs13 :
      localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13) =
        canonicalIntrinsicOverlapFiberCoordinates LocalSlot.s13) :
    ∀ α β : LocalSlot, A α β = ClosureCurrent.localSlotOverlapLaw α β := by
  let _ := hsel
  exact
    pointwise_eq_canonicalIntrinsicOverlapLaw_of_intrinsic_and_s13FiberCoordinates
      hA hs13

/-- On a fixed selected bridge datum, one canonical `s13` anchor fiber already
forces the unique canonical normal form `(2, 1, 0)` on any intrinsically
equivariant six-slot current-side law. So the single anchored row already
determines the full intrinsic parameter package before terminal exactification
data are attached. -/
theorem pairCarrierCanonicalS13FiberForcesCanonicalNormalFormOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection)
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
  let _ := hsel
  exact canonicalNormalForm_of_intrinsic_and_s13FiberCoordinates hA hs13

/-- On a fixed selected bridge datum, the same canonical `s13` anchor already
forces the full anchor-fiber coordinate family on any intrinsically equivariant
current-side six-slot law. So one anchored row determines every reduced local
coordinate readout before terminal exactification data are attached. -/
theorem pairCarrierCanonicalS13FiberForcesCanonicalFiberCoordinatesOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection)
    {A : LocalSlot → LocalSlot → SignedCount}
    (hA : IntrinsicAdjacencyInvariant A)
    (hs13 :
      localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13) =
        canonicalIntrinsicOverlapFiberCoordinates LocalSlot.s13) :
    ∀ anchor : LocalSlot,
      localSlotCoordinates (intrinsicLawFiber A anchor) =
        canonicalIntrinsicOverlapFiberCoordinates anchor := by
  let _ := hsel
  exact canonicalFiberCoordinates_of_intrinsic_and_s13FiberCoordinates hA hs13

/-- On a fixed selected bridge datum, if two intrinsically equivariant
six-slot laws both carry the canonical `s13` anchor fiber, then they already
agree pointwise on the whole local pair carrier. This is the pairwise
single-anchor rigidity theorem on the temporal realization surface. -/
theorem pairCarrierCanonicalS13FiberPairwiseRigidityOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection)
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
  let _ := hsel
  exact
    pointwise_eq_of_intrinsic_and_canonicalS13FiberCoordinates
      hA hs13A hB hs13B

/-- And the same pairwise single-anchor hypothesis already forces the full
anchor-fiber coordinate families of the two laws to agree on the fixed
selected bridge. So one anchored row on each law determines every reduced
local coordinate readout there. -/
theorem pairCarrierCanonicalS13FiberPairwiseCoordinatesOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection)
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
  let _ := hsel
  exact
    fiberCoordinateFamily_eq_of_intrinsic_and_canonicalS13FiberCoordinates
      hA hs13A hB hs13B

/-- On a fixed selected bridge datum, the public temporal law already reduces
Step 3 to one explicit carrier-generation supplement on that same selected
bundle. The selected-bundle forcing object is already law-native there, so the
only remaining Step 3 input is the canonical carrier-generation package
together with the two non-dictionary generation clauses. -/
def intrinsicSectorForcingOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection)
    (canonicalGeneration : SelectedBundle.CanonicalGeneration)
    (generatedFromIntrinsicChannelAlgebra : Prop)
    (minimalCompatibleRealizationsOnly : Prop)
    (hgenerated : generatedFromIntrinsicChannelAlgebra)
    (hminimal : minimalCompatibleRealizationsOnly) :
    IntrinsicSectorForcing Index Time Carrier Law where
  selectedBundle := data.selectedBundleForcingOnBridge bridge hsel
  canonicalGeneration := canonicalGeneration
  generatedFromIntrinsicChannelAlgebra := generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly := minimalCompatibleRealizationsOnly
  generatedFromIntrinsicChannelAlgebra_valid := hgenerated
  minimalCompatibleRealizationsOnly_valid := hminimal

/-- If the selected bundle itself is used to provide the canonical
carrier-generation package, then only the two explicit Step 3
intrinsic-generation clauses remain to be attached on that bridge. -/
def intrinsicSectorForcingOnBridgeOfClauses
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection)
    (generatedFromIntrinsicChannelAlgebra : Prop)
    (minimalCompatibleRealizationsOnly : Prop)
    (hgenerated : generatedFromIntrinsicChannelAlgebra)
    (hminimal : minimalCompatibleRealizationsOnly) :
    IntrinsicSectorForcing Index Time Carrier Law :=
  data.intrinsicSectorForcingOnBridge
    bridge
    hsel
    (data.selectedBundleOnBridge bridge hsel).toCanonicalGeneration
    generatedFromIntrinsicChannelAlgebra
    minimalCompatibleRealizationsOnly
    hgenerated
    hminimal

/-- Once the fixed-bridge recursive seed has been established, the active Step
3 surface is reduced exactly to the canonical carrier-generation package and
its two explicit intrinsic-generation clauses. No further current-side or
origin-side datum remains below carrier generation on that bridge. -/
theorem intrinsicSectorSurfaceOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection)
    (canonicalGeneration : SelectedBundle.CanonicalGeneration)
    (generatedFromIntrinsicChannelAlgebra : Prop)
    (minimalCompatibleRealizationsOnly : Prop)
    (hgenerated : generatedFromIntrinsicChannelAlgebra)
    (hminimal : minimalCompatibleRealizationsOnly) :
    Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
      generatedFromIntrinsicChannelAlgebra ∧
      minimalCompatibleRealizationsOnly ∧
      closureTypedPromotionFiniteCarrier.finite_carrier_available ∧
      closureTypedPromotionFiniteCarrier.canonical_signature_available ∧
      closureTypedPromotionFiniteCarrier.three_parameter_control ∧
      (natListSum [3, 2, 1] = balancedClosureSlotCount closureStableDimension) ∧
      IsCanonicalLogicalProfile [3, 2, 1] ∧
      canonicalGeneration.scalarChannelGeneratesPhase ∧
      canonicalGeneration.scalarChannelGeneratesWave ∧
      canonicalGeneration.balanceCompatibleCarrierGeneratesKinetic ∧
      canonicalGeneration.exactOneFormExchangeGeneratesGauge ∧
      canonicalGeneration.symmetricResponseGeneratesGeometry ∧
      canonicalGeneration.notPrimitiveDictionary := by
  simpa [intrinsicSectorForcingOnBridge] using
    (data.intrinsicSectorForcingOnBridge
      bridge
      hsel
      canonicalGeneration
      generatedFromIntrinsicChannelAlgebra
      minimalCompatibleRealizationsOnly
      hgenerated
      hminimal).surface

/-- Hence, on a fixed selected bridge, the public temporal law already reduces
Step 3 to the two explicit intrinsic-generation clauses themselves: the
selected bundle supplies the canonical carrier-generation package, and every
other Step 3 surface follows. -/
theorem intrinsicSectorSurfaceOnBridgeOfClauses
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection)
    (generatedFromIntrinsicChannelAlgebra : Prop)
    (minimalCompatibleRealizationsOnly : Prop)
    (hgenerated : generatedFromIntrinsicChannelAlgebra)
    (hminimal : minimalCompatibleRealizationsOnly) :
    Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
      generatedFromIntrinsicChannelAlgebra ∧
      minimalCompatibleRealizationsOnly ∧
      closureTypedPromotionFiniteCarrier.finite_carrier_available ∧
      closureTypedPromotionFiniteCarrier.canonical_signature_available ∧
      closureTypedPromotionFiniteCarrier.three_parameter_control ∧
      (natListSum [3, 2, 1] = balancedClosureSlotCount closureStableDimension) ∧
      IsCanonicalLogicalProfile [3, 2, 1] ∧
      (data.selectedBundleOnBridge bridge hsel).toCanonicalGeneration.scalarChannelGeneratesPhase ∧
      (data.selectedBundleOnBridge bridge hsel).toCanonicalGeneration.scalarChannelGeneratesWave ∧
      (data.selectedBundleOnBridge bridge hsel).toCanonicalGeneration.balanceCompatibleCarrierGeneratesKinetic ∧
      (data.selectedBundleOnBridge bridge hsel).toCanonicalGeneration.exactOneFormExchangeGeneratesGauge ∧
      (data.selectedBundleOnBridge bridge hsel).toCanonicalGeneration.symmetricResponseGeneratesGeometry ∧
      (data.selectedBundleOnBridge bridge hsel).toCanonicalGeneration.notPrimitiveDictionary := by
  simpa [intrinsicSectorForcingOnBridgeOfClauses, intrinsicSectorForcingOnBridge] using
    data.intrinsicSectorSurfaceOnBridge
      bridge
      hsel
      (data.selectedBundleOnBridge bridge hsel).toCanonicalGeneration
      generatedFromIntrinsicChannelAlgebra
      minimalCompatibleRealizationsOnly
      hgenerated
      hminimal

/-- Law-native intrinsic-generation clause on a fixed selected bridge. It says
that the selected bundle is intrinsic on the least-motion cut, all carrier
sectors share the same selected bundle and effective law, the final
carrier-level identification is the only non-common step, the bridge-local
pair carrier is governed by the canonical intrinsic overlap law, and the
canonical `[3,2,1]` profile is already forced there. -/
def intrinsicGenerationClauseOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) : Prop :=
  let bundle := data.selectedBundleOnBridge bridge hsel
  bundle.bundleArisesIntrinsicallyOnLeastMotionCut ∧
    bundle.bundleSharedByAllCarriers ∧
    bundle.sameSelectedEffectiveLawOnEachCarrier ∧
    bundle.carrierLevelIdentificationOnlyFinalStep ∧
    IntrinsicAdjacencyInvariant localSlotOverlapLaw ∧
    IsCanonicalLogicalProfile [3, 2, 1]

/-- Law-native minimal-compatibility clause on a fixed selected bridge. It is
exactly the finite-carrier, canonical-signature, and three-parameter control
surface forced by the active Part I calculus. -/
def minimalCompatibilityClauseOnBridge
    {Index Time Carrier Law : Type}
    (_data : TemporalRealizationLaw Index Time Carrier Law)
    (_bridge : BridgeData Index Time Carrier Law)
    (_hsel :
      _data.selectedLaw.selection =
        _bridge.selectedBridge.observer.selection) : Prop :=
  closureTypedPromotionFiniteCarrier.finite_carrier_available ∧
    closureTypedPromotionFiniteCarrier.canonical_signature_available ∧
    closureTypedPromotionFiniteCarrier.three_parameter_control

/-- The public temporal law already forces the law-native intrinsic-generation
clause on any fixed selected bridge. -/
theorem intrinsicGenerationClauseOnBridge_valid
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    data.intrinsicGenerationClauseOnBridge bridge hsel := by
  obtain ⟨hintrinsic, _hnoCarrier, _hproj, _hcutEq, _hsel, _hclosure, _hd3,
    _hobs, hshared, hsameLaw, hfinal⟩ :=
    data.selectedBundleSurfaceOnBridge bridge hsel
  obtain ⟨_hsix, hoverlap, _hchannels⟩ :=
    data.diophantinePairCarrierIntrinsicChannelSurfaceOnBridge bridge hsel
  obtain ⟨_hbundle, _hbedrock, _haut, _hfiber, _hd3, _hsix, _hsum, hprofile⟩ :=
    data.bedrockRecurrenceSurfaceOnBridge bridge hsel
  exact ⟨hintrinsic, hshared, hsameLaw, hfinal, hoverlap, hprofile⟩

/-- The public temporal law already forces the law-native
minimal-compatibility clause on any fixed selected bridge. -/
theorem minimalCompatibilityClauseOnBridge_valid
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    data.minimalCompatibilityClauseOnBridge bridge hsel := by
  exact closureTypedPromotionFiniteCarrier_surface

/-- The fixed-bridge Step 3 forcing package with no detached Step 3 input. The
selected bundle already supplies canonical generation, and the two remaining
Step 3 clauses are read law-natively from the same bridge. -/
def lawNativeIntrinsicSectorForcingOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    IntrinsicSectorForcing Index Time Carrier Law :=
  data.intrinsicSectorForcingOnBridge
    bridge
    hsel
    (data.selectedBundleOnBridge bridge hsel).toCanonicalGeneration
    (data.intrinsicGenerationClauseOnBridge bridge hsel)
    (data.minimalCompatibilityClauseOnBridge bridge hsel)
    (data.intrinsicGenerationClauseOnBridge_valid bridge hsel)
    (data.minimalCompatibilityClauseOnBridge_valid bridge hsel)

/-- Hence Step 3 is already fully law-native on any fixed selected bridge:
the temporal realization law alone determines the intrinsic sector-generation
surface there, with no additional Step 3 supplement. -/
theorem lawNativeIntrinsicSectorSurfaceOnBridge
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      data.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :
    Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
      data.intrinsicGenerationClauseOnBridge bridge hsel ∧
      data.minimalCompatibilityClauseOnBridge bridge hsel ∧
      closureTypedPromotionFiniteCarrier.finite_carrier_available ∧
      closureTypedPromotionFiniteCarrier.canonical_signature_available ∧
      closureTypedPromotionFiniteCarrier.three_parameter_control ∧
      (natListSum [3, 2, 1] = balancedClosureSlotCount closureStableDimension) ∧
      IsCanonicalLogicalProfile [3, 2, 1] ∧
      (data.selectedBundleOnBridge bridge hsel).toCanonicalGeneration.scalarChannelGeneratesPhase ∧
      (data.selectedBundleOnBridge bridge hsel).toCanonicalGeneration.scalarChannelGeneratesWave ∧
      (data.selectedBundleOnBridge bridge hsel).toCanonicalGeneration.balanceCompatibleCarrierGeneratesKinetic ∧
      (data.selectedBundleOnBridge bridge hsel).toCanonicalGeneration.exactOneFormExchangeGeneratesGauge ∧
      (data.selectedBundleOnBridge bridge hsel).toCanonicalGeneration.symmetricResponseGeneratesGeometry ∧
      (data.selectedBundleOnBridge bridge hsel).toCanonicalGeneration.notPrimitiveDictionary := by
  simpa [lawNativeIntrinsicSectorForcingOnBridge, intrinsicGenerationClauseOnBridge,
    minimalCompatibilityClauseOnBridge, intrinsicSectorForcingOnBridge] using
    data.intrinsicSectorSurfaceOnBridgeOfClauses
      bridge
      hsel
      (data.intrinsicGenerationClauseOnBridge bridge hsel)
      (data.minimalCompatibilityClauseOnBridge bridge hsel)
      (data.intrinsicGenerationClauseOnBridge_valid bridge hsel)
      (data.minimalCompatibilityClauseOnBridge_valid bridge hsel)

/-- The coherent cut class carried by the temporal realization law already has
the least-motion representative as its canonical selector. -/
theorem canonicalRepresentativeSurface
    {Index Time Carrier Law : Type}
    (data : TemporalRealizationLaw Index Time Carrier Law) :
    data.observerCovariance ∧
      data.leastMotionFaithfulCutUnique := by
  exact
    ⟨data.lawClauses.observerCovariance_valid,
      data.lawClauses.leastMotionFaithfulCutUnique_valid⟩

end TemporalRealizationLaw

private abbrev bridgeLocalEventObject
    {Index Time Carrier Law : Type}
    (temporalLaw : TemporalRealizationLaw Index Time Carrier Law)
    (bridge : BridgeData Index Time Carrier Law)
    (hsel :
      temporalLaw.selectedLaw.selection =
        bridge.selectedBridge.observer.selection) :=
  temporalLaw.localEventObjectOnBridge bridge hsel

/-- Local Part II terminal exactification law on one fixed selected bridge.
It does not reintroduce a second global dynamics. Instead it reads the
law-native local event already forced by temporal realization through one
explicit assembled-state readout, requires exactifier/generator intertwining on
that assembled state, and records terminality by exactification idempotence. -/
structure TerminalExactificationLaw (Index Time Carrier Law : Type) where
  temporalLaw : TemporalRealizationLaw Index Time Carrier Law
  bridge : BridgeData Index Time Carrier Law
  sameSelectedLawAsBridge :
    temporalLaw.selectedLaw.selection =
      bridge.selectedBridge.observer.selection
  readout :
    SignedExchangeReadout
      (bridgeLocalEventObject temporalLaw bridge sameSelectedLawAsBridge).currentCarrier
  frame :
    FourLegFrame
      (bridgeLocalEventObject temporalLaw bridge sameSelectedLawAsBridge).Leg
  exactifierRealized :
    ∀ current :
        PairExchangeCurrent
          (bridgeLocalEventObject temporalLaw bridge sameSelectedLawAsBridge).currentCarrier
          (bridgeLocalEventObject temporalLaw bridge sameSelectedLawAsBridge).Leg,
      assembledState readout frame
          ((bridgeLocalEventObject temporalLaw bridge sameSelectedLawAsBridge).exactifier.exactify
            current) =
        bridge.generator.toFun (assembledState readout frame current)
  exactificationIdempotent :
    ∀ current :
        PairExchangeCurrent
          (bridgeLocalEventObject temporalLaw bridge sameSelectedLawAsBridge).currentCarrier
          (bridgeLocalEventObject temporalLaw bridge sameSelectedLawAsBridge).Leg,
      (bridgeLocalEventObject temporalLaw bridge sameSelectedLawAsBridge).exactifier.exactify
          ((bridgeLocalEventObject temporalLaw bridge sameSelectedLawAsBridge).exactifier.exactify
            current) =
        (bridgeLocalEventObject temporalLaw bridge sameSelectedLawAsBridge).exactifier.exactify
          current
  onlyReturnedDefectRemainsActive : Prop
  onlyReturnedDefectRemainsActive_valid :
    onlyReturnedDefectRemainsActive

namespace TerminalExactificationLaw

/-- The local event read by the terminal exactification law is the same
law-native local event already forced by the temporal realization law on the
fixed selected bridge. -/
abbrev localEventObject
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    LocalEventObject Index Time Carrier Law :=
  bridgeLocalEventObject
    data.temporalLaw
    data.bridge
    data.sameSelectedLawAsBridge

/-- The selected-bundle object carried by the underlying temporal law on the
same fixed selected bridge. -/
abbrev selectedBundle
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    IntrinsicSelectedBundleExistence Time Carrier Law :=
  data.temporalLaw.selectedBundleOnBridge
    data.bridge
    data.sameSelectedLawAsBridge

/-- The fixed-bridge selected bundle already determines the canonical visible
carrier-generation package, so Step 3 no longer needs this package as
separate detached datum on that same bridge. -/
abbrev canonicalGeneration
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    SelectedBundle.CanonicalGeneration :=
  data.selectedBundle.toCanonicalGeneration

/-- The terminal exactification law already carries the exact local-state
bridge needed to read the reduced hidden-coordinate dynamics on the fixed
selected bridge. -/
def toLocalEventStateBridge
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    LocalEventStateBridge Index Time Carrier Law where
  object := data.localEventObject
  readout := data.readout
  frame := data.frame
  exactifier_realized := data.exactifierRealized

/-- Surface theorem for the local terminal exactification law. -/
theorem surface
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    (∀ current :
        PairExchangeCurrent
          data.localEventObject.currentCarrier
          data.localEventObject.Leg,
      assembledState data.readout data.frame
          (data.localEventObject.exactifier.exactify current) =
        data.bridge.generator.toFun
          (assembledState data.readout data.frame current)) ∧
      (∀ current :
          PairExchangeCurrent
            data.localEventObject.currentCarrier
            data.localEventObject.Leg,
        data.localEventObject.exactifier.exactify
            (data.localEventObject.exactifier.exactify current) =
          data.localEventObject.exactifier.exactify current) ∧
      data.onlyReturnedDefectRemainsActive := by
  exact
    ⟨data.exactifierRealized,
      data.exactificationIdempotent,
      data.onlyReturnedDefectRemainsActive_valid⟩

/-- The selected bundle already carries the canonical visible
carrier-generation surface on the same fixed bridge. -/
theorem canonicalGenerationSurface
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    let generation := data.canonicalGeneration
    generation.scalarChannelVisible ∧
      generation.scalarChannelGeneratesPhase ∧
      generation.scalarChannelGeneratesWave ∧
      generation.balanceCompatibleCarrierGeneratesKinetic ∧
      generation.exactOneFormExchangeGeneratesGauge ∧
      generation.symmetricResponseGeneratesGeometry ∧
      generation.notPrimitiveDictionary := by
  simpa [TerminalExactificationLaw.canonicalGeneration] using
    data.selectedBundle.canonicalGenerationSurface

/-- On the fixed selected bridge, terminal exactification already forces the
exact reduced hidden-coordinate transport law `t_n -> t_(n+1)` on the
three-coordinate balanced carrier. -/
theorem coordinateTransport
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    ∀ current :
        PairExchangeCurrent
          data.localEventObject.currentCarrier
          data.localEventObject.Leg,
      assembledCoordinates data.readout data.frame
          (data.localEventObject.exactifier.exactify current) =
        BalancedCoordinates.transport data.bridge.generator.toFun
          (assembledCoordinates data.readout data.frame current) := by
  intro current
  exact data.toLocalEventStateBridge.coordinateTransport current

/-- Exactified assembled states are fixed points of the matched selected
generator. Terminality is therefore read as a genuine generator-side fixed
point rather than as an external minimization slogan. -/
theorem fixedPointOnExactifiedState
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (current :
      PairExchangeCurrent
        data.localEventObject.currentCarrier
        data.localEventObject.Leg) :
    data.bridge.generator.toFun
        (assembledState data.readout data.frame
          (data.localEventObject.exactifier.exactify current)) =
      assembledState data.readout data.frame
        (data.localEventObject.exactifier.exactify current) := by
  have hrealized :=
    data.exactifierRealized (data.localEventObject.exactifier.exactify current)
  have hidem :
      assembledState data.readout data.frame
          (data.localEventObject.exactifier.exactify
            (data.localEventObject.exactifier.exactify current)) =
        assembledState data.readout data.frame
          (data.localEventObject.exactifier.exactify current) := by
    exact
      congrArg
        (assembledState data.readout data.frame)
        (data.exactificationIdempotent current)
  exact hrealized.symm.trans hidem

/-- The fixed-bridge two-law surface already determines the full discrete
hidden trajectory: repeated exactification of the law-native local event is
exactly the reduced hidden orbit determined by the selected bridge generator
and the initial reduced coordinate. -/
theorem hiddenTrajectory_initialStateOf
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    ∀ n : Nat,
      ∀ current :
          PairExchangeCurrent
            data.localEventObject.currentCarrier
            data.localEventObject.Leg,
        assembledCoordinates data.readout data.frame
            (data.toLocalEventStateBridge.toAnchoredCurrentObject.exactifyIterate
              n current) =
          (data.toLocalEventStateBridge.initialStateOf current).hiddenTrajectory n := by
  intro n current
  exact data.toLocalEventStateBridge.hiddenTrajectory_initialStateOf n current

private abbrev bridgeObservedState
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :=
  ReducedAnchoredCurrentObject.currentObservedState
    (CoordinateAnchoredCurrentObject.toReducedAnchoredCurrentObject
      (LocalEventCoordinateObject.toCoordinateAnchoredCurrentObject
        (LocalEventStateBridge.toLocalEventCoordinateObject
          data.toLocalEventStateBridge)))

/-- The same fixed-bridge two-law surface determines the corresponding
selected observed trajectory exactly as the selected projection of that
reduced hidden orbit. -/
theorem observedTrajectory_initialStateOf
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    ∀ n : Nat,
      ∀ current :
          PairExchangeCurrent
            data.localEventObject.currentCarrier
            data.localEventObject.Leg,
        (bridgeObservedState data)
          (data.toLocalEventStateBridge.toAnchoredCurrentObject.exactifyIterate
            n current) =
          (data.toLocalEventStateBridge.initialStateOf current).observedTrajectory n := by
  intro n current
  exact data.toLocalEventStateBridge.observedTrajectory_initialStateOf n current

/-- Surface theorem for the bridge-local recursive dynamics forced by the
public two-law surface. Once the fixed selected bridge, signed readout, and
four-leg frame are in hand, no further recurrence datum is needed: the hidden
and observed discrete futures are already the canonical reduced trajectories
of the selected bridge. -/
theorem recursiveTrajectorySurface
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    (∀ current :
        PairExchangeCurrent
          data.localEventObject.currentCarrier
          data.localEventObject.Leg,
      assembledCoordinates data.readout data.frame
          (data.localEventObject.exactifier.exactify current) =
        BalancedCoordinates.transport data.bridge.generator.toFun
          (assembledCoordinates data.readout data.frame current)) ∧
      (∀ n : Nat,
        ∀ current :
            PairExchangeCurrent
              data.localEventObject.currentCarrier
              data.localEventObject.Leg,
          assembledCoordinates data.readout data.frame
              (data.toLocalEventStateBridge.toAnchoredCurrentObject.exactifyIterate
                n current) =
            (data.toLocalEventStateBridge.initialStateOf current).hiddenTrajectory n) ∧
      (∀ n : Nat,
        ∀ current :
            PairExchangeCurrent
              data.localEventObject.currentCarrier
              data.localEventObject.Leg,
          (bridgeObservedState data)
            (data.toLocalEventStateBridge.toAnchoredCurrentObject.exactifyIterate
              n current) =
            (data.toLocalEventStateBridge.initialStateOf current).observedTrajectory n) := by
  exact
    ⟨data.coordinateTransport,
      data.hiddenTrajectory_initialStateOf,
      data.observedTrajectory_initialStateOf⟩

/-- On the fixed selected bridge, the terminal exactification law already reads
the hidden three-coordinate state from the canonical six pair slots of the
framed local event. Thus the reduced hidden state is not an extra microscopic
carrier layered above the pair current; it is the direct `binomial 4 2 = 6`
slot readout assembled onto the first three framed legs. -/
theorem localSlotCoordinateSurface
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    ∀ current :
        PairExchangeCurrent
          data.localEventObject.currentCarrier
          data.localEventObject.Leg,
      let slots := localSlotReadout data.readout data.frame current
      assembledCoordinates data.readout data.frame current =
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
  intro current
  exact assembledCoordinates_localSlotFormula data.readout data.frame current

/-- On the fixed selected bridge, the reduced hidden trajectory already
depends only on the initial six local slot values. Once two initial hidden
currents agree slot-by-slot on the framed pair carrier, the exactified reduced
hidden coordinates agree at every later step. -/
theorem sameLocalSlots_force_sameHiddenTrajectory
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    ∀ n : Nat,
      ∀ current current' :
          PairExchangeCurrent
            data.localEventObject.currentCarrier
            data.localEventObject.Leg,
        (∀ slot : LocalSlot,
          localSlotReadout data.readout data.frame current slot =
            localSlotReadout data.readout data.frame current' slot) →
          assembledCoordinates data.readout data.frame
              (data.toLocalEventStateBridge.toAnchoredCurrentObject.exactifyIterate
                n current) =
            assembledCoordinates data.readout data.frame
              (data.toLocalEventStateBridge.toAnchoredCurrentObject.exactifyIterate
                n current') := by
  intro n current current' hslots
  simpa [CurrentStateAssembly.realizeCoordinates]
    using
      CurrentStateAssembly.sameLocalSlots_sameHiddenTrajectory
        (data.toLocalEventStateBridge.toCurrentStateAssembly)
        n current current' hslots

/-- On the fixed selected bridge, the selected observed trajectory likewise
depends only on the initial six local slot values. Once two initial hidden
currents agree slot-by-slot on the framed pair carrier, their selected visible
trajectories agree at every later step. -/
theorem sameLocalSlots_force_sameObservedTrajectory
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    ∀ n : Nat,
      ∀ current current' :
          PairExchangeCurrent
            data.localEventObject.currentCarrier
            data.localEventObject.Leg,
        (∀ slot : LocalSlot,
          localSlotReadout data.readout data.frame current slot =
            localSlotReadout data.readout data.frame current' slot) →
          (bridgeObservedState data)
            (data.toLocalEventStateBridge.toAnchoredCurrentObject.exactifyIterate
              n current) =
            (bridgeObservedState data)
              (data.toLocalEventStateBridge.toAnchoredCurrentObject.exactifyIterate
                n current') := by
  intro n current current' hslots
  have hcoords :=
    data.sameLocalSlots_force_sameHiddenTrajectory n current current' hslots
  simpa [bridgeObservedState, ReducedAnchoredCurrentObject.currentObservedState,
    CoordinateAnchoredCurrentObject.toReducedAnchoredCurrentObject,
    LocalEventCoordinateObject.toCoordinateAnchoredCurrentObject,
    LocalEventStateBridge.toLocalEventCoordinateObject,
    CurrentCoordinateAssembly.toReducedCurrentAssembly,
    CurrentCoordinateAssembly.currentCoordinates]
    using congrArg (fun coords => selectedProjection data.bridge (coords.toState)) hcoords

/-- Attach Step 3 sector-generation clauses to the law-native local event on
the fixed selected bridge. -/
def localEventSectorObject
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (canonicalGeneration : SelectedBundle.CanonicalGeneration)
    (generatedFromIntrinsicChannelAlgebra : Prop)
    (minimalCompatibleRealizationsOnly : Prop)
    (hgenerated : generatedFromIntrinsicChannelAlgebra)
    (hminimal : minimalCompatibleRealizationsOnly) :
    LocalEventSectorObject Index Time Carrier Law where
  toLocalEventObject := data.localEventObject
  canonicalGeneration := canonicalGeneration
  generatedFromIntrinsicChannelAlgebra := generatedFromIntrinsicChannelAlgebra
  minimalCompatibleRealizationsOnly := minimalCompatibleRealizationsOnly
  generatedFromIntrinsicChannelAlgebra_valid := hgenerated
  minimalCompatibleRealizationsOnly_valid := hminimal

/-- The corresponding constructive sector law on the same fixed bridge. -/
def constructiveSectorLaw
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (canonicalGeneration : SelectedBundle.CanonicalGeneration)
    (generatedFromIntrinsicChannelAlgebra : Prop)
    (minimalCompatibleRealizationsOnly : Prop)
    (hgenerated : generatedFromIntrinsicChannelAlgebra)
    (hminimal : minimalCompatibleRealizationsOnly) :
    ConstructiveSectorLaw Index Time Carrier Law :=
  (data.localEventSectorObject
      canonicalGeneration
      generatedFromIntrinsicChannelAlgebra
      minimalCompatibleRealizationsOnly
      hgenerated
      hminimal).toConstructiveSectorLaw

/-- If the canonical carrier-generation package is read directly from the
selected bundle, then only the two explicit Step 3 intrinsic-generation
clauses remain to be attached on the fixed selected bridge. -/
def constructiveSectorLawOfClauses
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (generatedFromIntrinsicChannelAlgebra : Prop)
    (minimalCompatibleRealizationsOnly : Prop)
    (hgenerated : generatedFromIntrinsicChannelAlgebra)
    (hminimal : minimalCompatibleRealizationsOnly) :
    ConstructiveSectorLaw Index Time Carrier Law :=
  data.constructiveSectorLaw
    data.canonicalGeneration
    generatedFromIntrinsicChannelAlgebra
    minimalCompatibleRealizationsOnly
    hgenerated
    hminimal

/-- Once terminal exactification is assumed on the fixed bridge, attaching the
Step 3 carrier-generation clauses already determines the full constructive
sector-law surface on that same bridge. No further current-side, origin-side,
or exactifier supplement remains below Step 4 there. -/
theorem constructiveSectorSurface
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (canonicalGeneration : SelectedBundle.CanonicalGeneration)
    (generatedFromIntrinsicChannelAlgebra : Prop)
    (minimalCompatibleRealizationsOnly : Prop)
    (hgenerated : generatedFromIntrinsicChannelAlgebra)
    (hminimal : minimalCompatibleRealizationsOnly) :
    let sectorLaw :=
      data.constructiveSectorLaw
        canonicalGeneration
        generatedFromIntrinsicChannelAlgebra
        minimalCompatibleRealizationsOnly
        hgenerated
        hminimal
    Nonempty (PairExchangeCurrent sectorLaw.currentCarrier sectorLaw.Leg) ∧
      sectorLaw.toConstructiveMicroscopicLaw.toCurrentAnchor.currentDirectReturnCompatible ∧
      sectorLaw.toConstructiveMicroscopicLaw.toCurrentAnchor.visiblePrimitiveReadoutAutonomous ∧
      sectorLaw.toConstructiveMicroscopicLaw.toCurrentAnchor.minimalVisibleQuotients ∧
      exactVisibleOnCut
        (sectorLaw.bridge.selectedBridge.observer.selection.realization.tower.π
          sectorLaw.bridge.selectedBridge.observer.selection.horizon)
        (selected_observed_law sectorLaw.bridge.selectedBridge.observer.selection).op ∧
      ForcedContinuumLaw
        sectorLaw.bridge.selectedBridge.observer.continuumClass
        sectorLaw.physicalPrinciple.selectedLaw.selectedClosureLaw ∧
      (∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
        observer.selection = sectorLaw.bridge.selectedBridge.observer.selection →
          sectorLaw.physicalPrinciple.selectedLaw.endpointClosureClass =
            observer.continuumClass) ∧
      sectorLaw.toConstructiveMicroscopicLaw.bundleArisesIntrinsicallyOnLeastMotionCut ∧
      sectorLaw.toConstructiveMicroscopicLaw.noCarrierWiseVisibilityHypotheses ∧
      sectorLaw.generatedFromIntrinsicChannelAlgebra ∧
      sectorLaw.minimalCompatibleRealizationsOnly ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  simpa [constructiveSectorLaw] using
    (data.constructiveSectorLaw
      canonicalGeneration
      generatedFromIntrinsicChannelAlgebra
      minimalCompatibleRealizationsOnly
      hgenerated
      hminimal).surface

/-- On the fixed selected bridge, once the two explicit Step 3
intrinsic-generation clauses are attached, the selected bundle already
supplies the canonical carrier-generation package and the full constructive
sector-law surface follows with no further detached Step 3 datum. -/
theorem constructiveSectorSurfaceOfClauses
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (generatedFromIntrinsicChannelAlgebra : Prop)
    (minimalCompatibleRealizationsOnly : Prop)
    (hgenerated : generatedFromIntrinsicChannelAlgebra)
    (hminimal : minimalCompatibleRealizationsOnly) :
    let sectorLaw :=
      data.constructiveSectorLawOfClauses
        generatedFromIntrinsicChannelAlgebra
        minimalCompatibleRealizationsOnly
        hgenerated
        hminimal
    Nonempty (PairExchangeCurrent sectorLaw.currentCarrier sectorLaw.Leg) ∧
      sectorLaw.toConstructiveMicroscopicLaw.toCurrentAnchor.currentDirectReturnCompatible ∧
      sectorLaw.toConstructiveMicroscopicLaw.toCurrentAnchor.visiblePrimitiveReadoutAutonomous ∧
      sectorLaw.toConstructiveMicroscopicLaw.toCurrentAnchor.minimalVisibleQuotients ∧
      exactVisibleOnCut
        (sectorLaw.bridge.selectedBridge.observer.selection.realization.tower.π
          sectorLaw.bridge.selectedBridge.observer.selection.horizon)
        (selected_observed_law sectorLaw.bridge.selectedBridge.observer.selection).op ∧
      ForcedContinuumLaw
        sectorLaw.bridge.selectedBridge.observer.continuumClass
        sectorLaw.physicalPrinciple.selectedLaw.selectedClosureLaw ∧
      (∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
        observer.selection = sectorLaw.bridge.selectedBridge.observer.selection →
          sectorLaw.physicalPrinciple.selectedLaw.endpointClosureClass =
            observer.continuumClass) ∧
      sectorLaw.toConstructiveMicroscopicLaw.bundleArisesIntrinsicallyOnLeastMotionCut ∧
      sectorLaw.toConstructiveMicroscopicLaw.noCarrierWiseVisibilityHypotheses ∧
      sectorLaw.generatedFromIntrinsicChannelAlgebra ∧
      sectorLaw.minimalCompatibleRealizationsOnly ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  simpa [constructiveSectorLawOfClauses] using
    data.constructiveSectorSurface
      data.canonicalGeneration
      generatedFromIntrinsicChannelAlgebra
      minimalCompatibleRealizationsOnly
      hgenerated
      hminimal

/-- On the fixed selected bridge, once the canonical carrier-generation
package and the two explicit Step 3 clauses are attached to the terminal
exactification law, every other Step 3 control surface is already forced:
finite carrier, canonical signature, three-parameter control, the canonical
`[3,2,1]` profile, and the visible generation outputs. Thus the genuinely
independent Step 3 input on that bridge is exactly the carrier-generation
package together with those two explicit clauses. -/
theorem intrinsicSectorGenerationSurface
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (canonicalGeneration : SelectedBundle.CanonicalGeneration)
    (generatedFromIntrinsicChannelAlgebra : Prop)
    (minimalCompatibleRealizationsOnly : Prop)
    (hgenerated : generatedFromIntrinsicChannelAlgebra)
    (hminimal : minimalCompatibleRealizationsOnly) :
    let sectorGeneration :=
      (data.constructiveSectorLaw
        canonicalGeneration
        generatedFromIntrinsicChannelAlgebra
        minimalCompatibleRealizationsOnly
        hgenerated
        hminimal).toIntrinsicSectorGeneration
    sectorGeneration.generatedFromIntrinsicChannelAlgebra ∧
      sectorGeneration.minimalCompatibleRealizationsOnly ∧
      closureTypedPromotionFiniteCarrier.finite_carrier_available ∧
      closureTypedPromotionFiniteCarrier.canonical_signature_available ∧
      closureTypedPromotionFiniteCarrier.three_parameter_control ∧
      (natListSum [3, 2, 1] = balancedClosureSlotCount closureStableDimension) ∧
      IsCanonicalLogicalProfile [3, 2, 1] ∧
      sectorGeneration.scalarChannelGeneratesPhase ∧
      sectorGeneration.scalarChannelGeneratesWave ∧
      sectorGeneration.balanceCompatibleCarrierGeneratesKinetic ∧
      sectorGeneration.exactOneFormExchangeGeneratesGauge ∧
      sectorGeneration.symmetricResponseGeneratesGeometry ∧
      sectorGeneration.notPrimitiveDictionary := by
  simpa [constructiveSectorLaw] using
    intrinsic_sector_generation
      ((data.constructiveSectorLaw
        canonicalGeneration
        generatedFromIntrinsicChannelAlgebra
        minimalCompatibleRealizationsOnly
        hgenerated
        hminimal).toIntrinsicSectorGeneration)

/-- Hence, on a fixed selected bridge, the genuinely independent Step 3 input
has contracted to the two explicit intrinsic-generation clauses themselves:
the selected bundle already supplies the canonical carrier-generation package,
and every other Step 3 control surface follows. -/
theorem intrinsicSectorGenerationSurfaceOfClauses
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (generatedFromIntrinsicChannelAlgebra : Prop)
    (minimalCompatibleRealizationsOnly : Prop)
    (hgenerated : generatedFromIntrinsicChannelAlgebra)
    (hminimal : minimalCompatibleRealizationsOnly) :
    let sectorGeneration :=
      (data.constructiveSectorLawOfClauses
        generatedFromIntrinsicChannelAlgebra
        minimalCompatibleRealizationsOnly
        hgenerated
        hminimal).toIntrinsicSectorGeneration
    sectorGeneration.generatedFromIntrinsicChannelAlgebra ∧
      sectorGeneration.minimalCompatibleRealizationsOnly ∧
      closureTypedPromotionFiniteCarrier.finite_carrier_available ∧
      closureTypedPromotionFiniteCarrier.canonical_signature_available ∧
      closureTypedPromotionFiniteCarrier.three_parameter_control ∧
      (natListSum [3, 2, 1] = balancedClosureSlotCount closureStableDimension) ∧
      IsCanonicalLogicalProfile [3, 2, 1] ∧
      sectorGeneration.scalarChannelGeneratesPhase ∧
      sectorGeneration.scalarChannelGeneratesWave ∧
      sectorGeneration.balanceCompatibleCarrierGeneratesKinetic ∧
      sectorGeneration.exactOneFormExchangeGeneratesGauge ∧
      sectorGeneration.symmetricResponseGeneratesGeometry ∧
      sectorGeneration.notPrimitiveDictionary := by
  simpa [constructiveSectorLawOfClauses] using
    data.intrinsicSectorGenerationSurface
      data.canonicalGeneration
      generatedFromIntrinsicChannelAlgebra
      minimalCompatibleRealizationsOnly
      hgenerated
      hminimal

/-- The terminal exactification law inherits the law-native intrinsic
generation clause from the underlying temporal law on the same fixed selected
bridge. -/
abbrev intrinsicGenerationClause
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  data.temporalLaw.intrinsicGenerationClauseOnBridge
    data.bridge
    data.sameSelectedLawAsBridge

/-- The terminal exactification law inherits the law-native minimal
compatibility clause from the underlying temporal law on the same fixed
selected bridge. -/
abbrev minimalCompatibilityClause
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  data.temporalLaw.minimalCompatibilityClauseOnBridge
    data.bridge
    data.sameSelectedLawAsBridge

/-- The inherited intrinsic-generation clause is already valid on the fixed
selected bridge. -/
theorem intrinsicGenerationClause_valid
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.intrinsicGenerationClause := by
  exact
    data.temporalLaw.intrinsicGenerationClauseOnBridge_valid
      data.bridge
      data.sameSelectedLawAsBridge

/-- The inherited minimal-compatibility clause is already valid on the fixed
selected bridge. -/
theorem minimalCompatibilityClause_valid
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.minimalCompatibilityClause := by
  exact
    data.temporalLaw.minimalCompatibilityClauseOnBridge_valid
      data.bridge
      data.sameSelectedLawAsBridge

/-- The smaller law-native constructive microscopic law on the fixed selected
bridge, before the Step 3 carrier-generation package is attached. -/
abbrev lawNativeConstructiveMicroscopicLaw
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    ConstructiveMicroscopicLaw Index Time Carrier Law :=
  data.temporalLaw.constructiveMicroscopicLawOnBridge
    data.bridge
    data.sameSelectedLawAsBridge

/-- The law-native constructive sector law on the fixed selected bridge. No
detached Step 3 supplement remains: canonical generation comes from the
selected bundle, and the two remaining Step 3 clauses are inherited from the
underlying temporal-law bridge surface. -/
def lawNativeConstructiveSectorLaw
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    ConstructiveSectorLaw Index Time Carrier Law :=
  data.constructiveSectorLawOfClauses
    data.intrinsicGenerationClause
    data.minimalCompatibilityClause
    data.intrinsicGenerationClause_valid
    data.minimalCompatibilityClause_valid

/-- Attaching the law-native Step 3 sector-generation surface does not alter
the smaller current-side constructive microscopic law on the fixed bridge. -/
theorem lawNativeConstructiveSectorLaw_toConstructiveMicroscopicLaw
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.lawNativeConstructiveSectorLaw.toConstructiveMicroscopicLaw =
      data.lawNativeConstructiveMicroscopicLaw := by
  unfold TerminalExactificationLaw.lawNativeConstructiveSectorLaw
  unfold TerminalExactificationLaw.constructiveSectorLawOfClauses
  unfold TerminalExactificationLaw.constructiveSectorLaw
  unfold TerminalExactificationLaw.localEventSectorObject
  change
    data.localEventObject.toConstructiveMicroscopicLaw =
      data.temporalLaw.constructiveMicroscopicLawOnBridge
        data.bridge
        data.sameSelectedLawAsBridge
  simp [TerminalExactificationLaw.localEventObject,
    TemporalRealizationLaw.localEventObjectOnBridge,
    ConstructiveMicroscopicLaw.toLocalEventObject_toConstructiveMicroscopicLaw]

/-- Hence the law-native constructive sector law also carries exactly the same
public physical principle as the smaller law-native constructive microscopic
law determined by temporal realization. -/
theorem lawNativeConstructiveMicroscopicLaw_samePhysicalPrinciple
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.lawNativeConstructiveMicroscopicLaw.physicalPrinciple =
      data.temporalLaw.toPhysicalRealizationPrinciple := by
  exact
    data.temporalLaw.constructiveMicroscopicLawOnBridge_samePhysicalPrinciple
      data.bridge
      data.sameSelectedLawAsBridge

/-- The smaller law-native constructive microscopic law still reduces to the
same law-native microscopic closure law on the fixed selected bridge. -/
theorem lawNativeConstructiveMicroscopicLaw_toMicroscopicClosureLaw
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.lawNativeConstructiveMicroscopicLaw.toMicroscopicClosureLaw =
      data.temporalLaw.microscopicClosureLawOnBridge
        data.bridge
        data.sameSelectedLawAsBridge := by
  exact
    data.temporalLaw.constructiveMicroscopicLawOnBridge_toMicroscopicClosureLaw
      data.bridge
      data.sameSelectedLawAsBridge

/-- The smaller law-native constructive microscopic law reconstructs exactly
the same bridge-local event object already carried by the fixed selected
bridge. -/
theorem lawNativeConstructiveMicroscopicLaw_toLocalEventObject
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.lawNativeConstructiveMicroscopicLaw.toLocalEventObject =
      data.localEventObject := by
  rfl

/-- Thus the terminal exactification law already determines the full
constructive sector-law surface on the fixed selected bridge, with no
additional Step 3 supplement. -/
theorem lawNativeConstructiveSectorSurface
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    let sectorLaw := data.lawNativeConstructiveSectorLaw
    Nonempty (PairExchangeCurrent sectorLaw.currentCarrier sectorLaw.Leg) ∧
      sectorLaw.toConstructiveMicroscopicLaw.toCurrentAnchor.currentDirectReturnCompatible ∧
      sectorLaw.toConstructiveMicroscopicLaw.toCurrentAnchor.visiblePrimitiveReadoutAutonomous ∧
      sectorLaw.toConstructiveMicroscopicLaw.toCurrentAnchor.minimalVisibleQuotients ∧
      exactVisibleOnCut
        (sectorLaw.bridge.selectedBridge.observer.selection.realization.tower.π
          sectorLaw.bridge.selectedBridge.observer.selection.horizon)
        (selected_observed_law sectorLaw.bridge.selectedBridge.observer.selection).op ∧
      ForcedContinuumLaw
        sectorLaw.bridge.selectedBridge.observer.continuumClass
        sectorLaw.physicalPrinciple.selectedLaw.selectedClosureLaw ∧
      (∀ observer : ObserverSelection.LeastMotion Time Carrier Law,
        observer.selection = sectorLaw.bridge.selectedBridge.observer.selection →
          sectorLaw.physicalPrinciple.selectedLaw.endpointClosureClass =
            observer.continuumClass) ∧
      sectorLaw.toConstructiveMicroscopicLaw.bundleArisesIntrinsicallyOnLeastMotionCut ∧
      sectorLaw.toConstructiveMicroscopicLaw.noCarrierWiseVisibilityHypotheses ∧
      sectorLaw.generatedFromIntrinsicChannelAlgebra ∧
      sectorLaw.minimalCompatibleRealizationsOnly ∧
      IsCanonicalLogicalProfile [3, 2, 1] := by
  simpa [lawNativeConstructiveSectorLaw, intrinsicGenerationClause,
    minimalCompatibilityClause] using
    data.constructiveSectorSurfaceOfClauses
      data.intrinsicGenerationClause
      data.minimalCompatibilityClause
      data.intrinsicGenerationClause_valid
      data.minimalCompatibilityClause_valid

/-- Attaching the law-native Step 3 carrier-generation surface also
reconstructs exactly the fixed-bridge local-event sector object used to define
that same law-native sector law. -/
theorem lawNativeConstructiveSectorLaw_toLocalEventSectorObject
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.lawNativeConstructiveSectorLaw.toLocalEventSectorObject =
      data.localEventSectorObject
        data.canonicalGeneration
        data.intrinsicGenerationClause
        data.minimalCompatibilityClause
        data.intrinsicGenerationClause_valid
        data.minimalCompatibilityClause_valid := by
  unfold TerminalExactificationLaw.lawNativeConstructiveSectorLaw
  unfold TerminalExactificationLaw.constructiveSectorLawOfClauses
  unfold TerminalExactificationLaw.constructiveSectorLaw
  cases data.lawNativeConstructiveSectorLaw_toConstructiveMicroscopicLaw
  cases data.lawNativeConstructiveMicroscopicLaw_toLocalEventObject
  rfl

/-- The law-native constructive sector law carries exactly the same canonical
generation package already read from the fixed selected bundle. -/
theorem lawNativeConstructiveSectorLaw_canonicalGeneration
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.lawNativeConstructiveSectorLaw.canonicalGeneration =
      data.canonicalGeneration := by
  rfl

/-- The law-native constructive sector law also carries exactly the same
intrinsic-generation clause inherited from the temporal law on the fixed
selected bridge. -/
theorem lawNativeConstructiveSectorLaw_generatedFromIntrinsicChannelAlgebra
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.lawNativeConstructiveSectorLaw.generatedFromIntrinsicChannelAlgebra =
      data.intrinsicGenerationClause := by
  rfl

/-- And the law-native constructive sector law carries exactly the same
minimal-compatibility clause inherited from the temporal law on that same
bridge. -/
theorem lawNativeConstructiveSectorLaw_minimalCompatibleRealizationsOnly
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.lawNativeConstructiveSectorLaw.minimalCompatibleRealizationsOnly =
      data.minimalCompatibilityClause := by
  rfl

/-- And the full Step 3 intrinsic sector-generation surface is already forced
on the fixed selected bridge by the public two-law surface itself. -/
theorem lawNativeIntrinsicSectorGenerationSurface
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    let sectorGeneration := data.lawNativeConstructiveSectorLaw.toIntrinsicSectorGeneration
    sectorGeneration.generatedFromIntrinsicChannelAlgebra ∧
      sectorGeneration.minimalCompatibleRealizationsOnly ∧
      closureTypedPromotionFiniteCarrier.finite_carrier_available ∧
      closureTypedPromotionFiniteCarrier.canonical_signature_available ∧
      closureTypedPromotionFiniteCarrier.three_parameter_control ∧
      (natListSum [3, 2, 1] = balancedClosureSlotCount closureStableDimension) ∧
      IsCanonicalLogicalProfile [3, 2, 1] ∧
      sectorGeneration.scalarChannelGeneratesPhase ∧
      sectorGeneration.scalarChannelGeneratesWave ∧
      sectorGeneration.balanceCompatibleCarrierGeneratesKinetic ∧
      sectorGeneration.exactOneFormExchangeGeneratesGauge ∧
      sectorGeneration.symmetricResponseGeneratesGeometry ∧
      sectorGeneration.notPrimitiveDictionary := by
  simpa [lawNativeConstructiveSectorLaw, intrinsicGenerationClause,
    minimalCompatibilityClause] using
    data.intrinsicSectorGenerationSurfaceOfClauses
      data.intrinsicGenerationClause
      data.minimalCompatibilityClause
      data.intrinsicGenerationClause_valid
      data.minimalCompatibilityClause_valid

/-- On the public two-law surface, the current-side six-slot pair carrier is
already rigid at the intrinsic local-law level: the canonical overlap law has
one unique normal form, with explicit parameter values `(2, 1, 0)`. So before
any Step 4 completion data are chosen, the law-native pair carrier already
carries a unique intrinsic current-side law. -/
theorem lawNativePairCarrierLawSurface
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    (balancedClosureSlotCount closureStableDimension = 6) ∧
      (natListSum [3, 2, 1] = balancedClosureSlotCount closureStableDimension) ∧
      IsCanonicalLogicalProfile [3, 2, 1] ∧
      ∃ p : IntrinsicSlotParameters,
        (isIntrinsicNormalForm ClosureCurrent.localSlotOverlapLaw p ∧
          p.diagonal = SignedCount.ofNat 2 ∧
          p.adjacent = SignedCount.ofNat 1 ∧
          p.disjoint = SignedCount.zero) ∧
        ∀ q : IntrinsicSlotParameters,
          (isIntrinsicNormalForm ClosureCurrent.localSlotOverlapLaw q ∧
            q.diagonal = SignedCount.ofNat 2 ∧
            q.adjacent = SignedCount.ofNat 1 ∧
            q.disjoint = SignedCount.zero) →
          q = p := by
  exact
    data.temporalLaw.pairCarrierLawSurfaceOnBridge
      data.bridge
      data.sameSelectedLawAsBridge

/-- On the public two-law surface, the law-native six-slot pair carrier is
already pointwise rigid: any candidate local six-slot law with the canonical
overlap normal form `(2, 1, 0)` agrees slot-by-slot with the canonical
law-native overlap law. So the current-side pair law is no longer an
independent datum there. -/
theorem lawNativePairCarrierLawPointwiseUnique
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
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
    ∀ α β : LocalSlot, A α β = ClosureCurrent.localSlotOverlapLaw α β := by
  exact
    data.temporalLaw.pairCarrierLawPointwiseUniqueOnBridge
      data.bridge
      data.sameSelectedLawAsBridge
      hA

/-- The law-native six-slot pair carrier on the public two-law surface already
has the exact intrinsic channel spectrum `(6, 0, 2)`. -/
theorem lawNativePairCarrierExactChannelSpectrum
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    intrinsicChannelEigenvalue1 canonicalIntrinsicOverlapParameters =
        SignedCount.ofNat 6 ∧
      intrinsicChannelEigenvalue2 canonicalIntrinsicOverlapParameters =
        SignedCount.zero ∧
      intrinsicChannelEigenvalue3 canonicalIntrinsicOverlapParameters =
        SignedCount.ofNat 2 := by
  exact
    data.temporalLaw.pairCarrierExactChannelSpectrumOnBridge
      data.bridge
      data.sameSelectedLawAsBridge

/-- The public two-law surface also fixes the distinguished `s12` fiber
coordinates of the law-native six-slot pair law. So before any Step 4
completion data are chosen, one anchored current-side coordinate package is
already forced exactly. -/
theorem lawNativePairCarrierS12FiberCoordinates
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    localSlotCoordinates
        (intrinsicLawFiber ClosureCurrent.localSlotOverlapLaw LocalSlot.s12) =
      ⟨SignedCount.ofNat 4, SignedCount.zero, SignedCount.negOfNat 2⟩ := by
  exact
    data.temporalLaw.pairCarrierS12FiberCoordinatesOnBridge
      data.bridge
      data.sameSelectedLawAsBridge

/-- The public two-law surface also fixes the full anchor-fiber coordinate
family of the law-native six-slot pair law. So before any Step 4 completion
data are chosen, the reduced current-side coordinate readout is already forced
at every local anchor. -/
theorem lawNativePairCarrierFiberCoordinates
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    ∀ anchor : LocalSlot,
      localSlotCoordinates
          (intrinsicLawFiber ClosureCurrent.localSlotOverlapLaw anchor) =
        canonicalIntrinsicOverlapFiberCoordinates anchor := by
  exact
    data.temporalLaw.pairCarrierFiberCoordinatesOnBridge
      data.bridge
      data.sameSelectedLawAsBridge

/-- On the public two-law surface, any intrinsic six-slot law in canonical
normal form `(2, 1, 0)` already has the full canonical anchor-fiber
coordinate family. This is the law-native coordinate forcing surface
available before any Step 4 completion data are chosen. -/
theorem lawNativePairCarrierCanonicalNormalFormFiberCoordinates
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
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
  exact
    data.temporalLaw.pairCarrierCanonicalNormalFormFiberCoordinatesOnBridge
      data.bridge
      data.sameSelectedLawAsBridge
      hA

/-- On the public two-law surface, any intrinsic six-slot law in canonical
normal form `(2, 1, 0)` already has the canonical `s13` fiber coordinates
`(4, 0, -2)`. This is the minimal single-fiber coordinate forcing statement
available before any Step 4 completion data are chosen. -/
theorem lawNativePairCarrierCanonicalNormalFormS13FiberCoordinates
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
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
  exact
    data.temporalLaw.pairCarrierCanonicalNormalFormS13FiberCoordinatesOnBridge
      data.bridge
      data.sameSelectedLawAsBridge
      hA

/-- On the public two-law surface, one canonical `s13` anchor fiber already
forces the full intrinsic six-slot law. This is the smallest law-native
fiber-level rigidity statement available before any Step 4 completion data are
chosen. -/
theorem lawNativePairCarrierCanonicalS13FiberRigidity
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    {A : LocalSlot → LocalSlot → SignedCount}
    (hA : IntrinsicAdjacencyInvariant A)
    (hs13 :
      localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13) =
        canonicalIntrinsicOverlapFiberCoordinates LocalSlot.s13) :
    ∀ α β : LocalSlot, A α β = ClosureCurrent.localSlotOverlapLaw α β := by
  exact
    data.temporalLaw.pairCarrierCanonicalS13FiberRigidityOnBridge
      data.bridge
      data.sameSelectedLawAsBridge
      hA
      hs13

/-- On the public two-law surface, one canonical `s13` anchor fiber already
forces the unique canonical normal form `(2, 1, 0)` on any intrinsically
equivariant six-slot current-side law. So the law-native current-side pair law
admits no additional intrinsic parameter freedom there. -/
theorem lawNativePairCarrierCanonicalS13FiberForcesCanonicalNormalForm
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
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
    data.temporalLaw.pairCarrierCanonicalS13FiberForcesCanonicalNormalFormOnBridge
      data.bridge
      data.sameSelectedLawAsBridge
      hA
      hs13

/-- On the public two-law surface, the same canonical `s13` anchor already
forces the full anchor-fiber coordinate family on any intrinsically equivariant
six-slot current-side law. So one anchored current-side row determines every
reduced local coordinate readout there. -/
theorem lawNativePairCarrierCanonicalS13FiberForcesCanonicalFiberCoordinates
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    {A : LocalSlot → LocalSlot → SignedCount}
    (hA : IntrinsicAdjacencyInvariant A)
    (hs13 :
      localSlotCoordinates (intrinsicLawFiber A LocalSlot.s13) =
        canonicalIntrinsicOverlapFiberCoordinates LocalSlot.s13) :
    ∀ anchor : LocalSlot,
      localSlotCoordinates (intrinsicLawFiber A anchor) =
        canonicalIntrinsicOverlapFiberCoordinates anchor := by
  exact
    data.temporalLaw.pairCarrierCanonicalS13FiberForcesCanonicalFiberCoordinatesOnBridge
      data.bridge
      data.sameSelectedLawAsBridge
      hA
      hs13

/-- On the public two-law surface, if two intrinsically equivariant six-slot
laws both carry the canonical `s13` anchor fiber, then they already agree
pointwise on the whole local pair carrier. So the single-anchor rigidity
theorem is now available directly on the law-native surface. -/
theorem lawNativePairCarrierCanonicalS13FiberPairwiseRigidity
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
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
    data.temporalLaw.pairCarrierCanonicalS13FiberPairwiseRigidityOnBridge
      data.bridge
      data.sameSelectedLawAsBridge
      hA
      hs13A
      hB
      hs13B

/-- And the same pairwise single-anchor hypothesis already forces the full
anchor-fiber coordinate families of the two laws to agree on the public
two-law surface. This is the pairwise coordinate-level rigidity theorem later
needed by the current-side collapse route. -/
theorem lawNativePairCarrierCanonicalS13FiberPairwiseCoordinates
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
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
    data.temporalLaw.pairCarrierCanonicalS13FiberPairwiseCoordinatesOnBridge
      data.bridge
      data.sameSelectedLawAsBridge
      hA
      hs13A
      hB
      hs13B

/-- The terminal exactification law already determines the current-side
four-state readout package on the law-native fixed-bridge sector law. -/
def lawNativeFourStateReadout
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    FourStateReadout data.lawNativeConstructiveSectorLaw where
  readout := data.readout
  frame := data.frame

/-- The exactifier/generator intertwining target is already carried by the
terminal exactification law on its law-native fixed-bridge sector law. -/
theorem lawNativeExactifierRealizationTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    ExactifierRealizationTarget data.lawNativeFourStateReadout := by
  exact data.exactifierRealized

/-- The public two-law surface therefore also fixes the full current-side
four-state assembly on the same law-native fixed-bridge sector law. -/
def lawNativeFourStateAssembly
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    FourStateAssembly data.lawNativeConstructiveSectorLaw :=
  data.lawNativeFourStateReadout.toFourStateAssembly
    data.lawNativeExactifierRealizationTarget

/-- The law-native four-state assembly reconstructs exactly the same explicit
local-event state bridge already carried by terminal exactification on the
fixed selected bridge. -/
theorem lawNativeFourStateAssembly_toLocalEventStateBridge
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.lawNativeFourStateAssembly.toLocalEventFourStateLaw.toLocalEventStateBridge =
      data.toLocalEventStateBridge := by
  unfold TerminalExactificationLaw.lawNativeFourStateAssembly
  unfold TerminalExactificationLaw.lawNativeFourStateReadout
  cases data.lawNativeConstructiveSectorLaw_toConstructiveMicroscopicLaw
  cases data.lawNativeConstructiveMicroscopicLaw_toLocalEventObject
  rfl

/-- Hence the law-native four-state assembly also reconstructs exactly the
same explicit current-state assembly on the fixed selected bridge. -/
theorem lawNativeFourStateAssembly_toCurrentStateAssembly
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.lawNativeFourStateAssembly.toCurrentStateAssembly =
      data.toLocalEventStateBridge.toCurrentStateAssembly := by
  cases data.lawNativeFourStateAssembly_toLocalEventStateBridge
  rfl

/-- The law-native four-state assembly reads exactly the same hidden
coordinates and selected visible state as the explicit current-state assembly
already carried by the terminal exactification datum on the fixed selected
bridge. So attaching Step 3 does not change the current-side state assembly
itself. -/
theorem lawNativeFourStateAssemblyCurrentSurface
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    (∀ current :
        PairExchangeCurrent
          data.lawNativeConstructiveSectorLaw.currentCarrier
          data.lawNativeConstructiveSectorLaw.Leg,
      data.lawNativeFourStateAssembly.realizeCoordinates current =
        data.toLocalEventStateBridge.toCurrentStateAssembly.realizeCoordinates current) ∧
      (∀ current :
          PairExchangeCurrent
            data.lawNativeConstructiveSectorLaw.currentCarrier
            data.lawNativeConstructiveSectorLaw.Leg,
        data.lawNativeFourStateAssembly.observedState current =
          data.toLocalEventStateBridge.toCurrentStateAssembly.observedState current) := by
  constructor <;> intro current
  · cases data.lawNativeFourStateAssembly_toCurrentStateAssembly
    rfl
  · cases data.lawNativeFourStateAssembly_toCurrentStateAssembly
    rfl

/-- A constructive sector law is determined by its smaller constructive
microscopic law together with its three Step 3 fields. This keeps the fieldwise
current-side equality route available without any proof-irrelevant rewriting
through proposition extensionality. -/
private theorem constructiveSectorLaw_eq_of_field_eq
    {Index Time Carrier Law : Type}
    {sectorLaw other : ConstructiveSectorLaw Index Time Carrier Law}
    (hmicroscopic :
      sectorLaw.toConstructiveMicroscopicLaw =
        other.toConstructiveMicroscopicLaw)
    (hgeneration : sectorLaw.canonicalGeneration = other.canonicalGeneration)
    (hintrinsic :
      sectorLaw.generatedFromIntrinsicChannelAlgebra =
        other.generatedFromIntrinsicChannelAlgebra)
    (hminimal :
      sectorLaw.minimalCompatibleRealizationsOnly =
        other.minimalCompatibleRealizationsOnly) :
    sectorLaw = other := by
  cases sectorLaw
  cases other
  cases hmicroscopic
  cases hgeneration
  cases hintrinsic
  cases hminimal
  rfl

/-- Once a candidate no-stage completion law already uses the same explicit
local state bridge and the same remaining Step 3 data as the law-native
terminal exactification datum, its smaller constructive sector law is forced.
This is the first exact current-side collapse statement needed upstream. -/
theorem lawNativeSectorCollapseOfStateBridgeAndStep3Data
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (completionLaw : LocalEventFourStateCompletionLaw Index Time Carrier Law)
    (hstateBridge :
      completionLaw.fourStateLaw.toLocalEventStateBridge =
        data.toLocalEventStateBridge)
    (hgeneration :
      completionLaw.canonicalGeneration = data.canonicalGeneration)
    (hintrinsic :
      completionLaw.generatedFromIntrinsicChannelAlgebra =
        data.intrinsicGenerationClause)
    (hminimal :
      completionLaw.minimalCompatibleRealizationsOnly =
        data.minimalCompatibilityClause) :
    completionLaw.toConstructiveSectorLaw =
      data.lawNativeConstructiveSectorLaw := by
  have hmicroscopic₀ :
      completionLaw.fourStateLaw.framed.object.toConstructiveMicroscopicLaw =
        data.localEventObject.toConstructiveMicroscopicLaw := by
    simpa [LocalEventFourStateLaw.toLocalEventStateBridge,
      TerminalExactificationLaw.toLocalEventStateBridge] using
      congrArg (fun bridge => bridge.object.toConstructiveMicroscopicLaw) hstateBridge
  have hlawNativeObject :
      data.localEventObject.toConstructiveMicroscopicLaw =
        data.lawNativeConstructiveMicroscopicLaw := by
    simpa using
      congrArg LocalEventObject.toConstructiveMicroscopicLaw
        (data.lawNativeConstructiveMicroscopicLaw_toLocalEventObject).symm
  have hmicroscopic :
      completionLaw.toConstructiveSectorLaw.toConstructiveMicroscopicLaw =
        data.lawNativeConstructiveSectorLaw.toConstructiveMicroscopicLaw := by
    calc
      completionLaw.toConstructiveSectorLaw.toConstructiveMicroscopicLaw =
          completionLaw.fourStateLaw.framed.object.toConstructiveMicroscopicLaw := by
        rfl
      _ = data.localEventObject.toConstructiveMicroscopicLaw := hmicroscopic₀
      _ = data.lawNativeConstructiveMicroscopicLaw := hlawNativeObject
      _ = data.lawNativeConstructiveSectorLaw.toConstructiveMicroscopicLaw := by
        symm
        exact data.lawNativeConstructiveSectorLaw_toConstructiveMicroscopicLaw
  exact
    constructiveSectorLaw_eq_of_field_eq
      hmicroscopic
      hgeneration
      hintrinsic
      hminimal

/-- The same sector-law collapse theorem only really needs the smaller
constructive microscopic law together with the three explicit Step 3 fields.
So once the microscopic law has already collapsed, no full local-state-bridge
equality is needed to force the smaller constructive sector law. -/
theorem lawNativeSectorCollapseOfMicroscopicLawAndStep3Data
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (completionLaw : LocalEventFourStateCompletionLaw Index Time Carrier Law)
    (hmicroscopic :
      completionLaw.toConstructiveSectorLaw.toConstructiveMicroscopicLaw =
        data.lawNativeConstructiveMicroscopicLaw)
    (hgeneration :
      completionLaw.canonicalGeneration = data.canonicalGeneration)
    (hintrinsic :
      completionLaw.generatedFromIntrinsicChannelAlgebra =
        data.intrinsicGenerationClause)
    (hminimal :
      completionLaw.minimalCompatibleRealizationsOnly =
        data.minimalCompatibilityClause) :
    completionLaw.toConstructiveSectorLaw =
      data.lawNativeConstructiveSectorLaw := by
  have hmicroscopic' :
      completionLaw.toConstructiveSectorLaw.toConstructiveMicroscopicLaw =
        data.lawNativeConstructiveSectorLaw.toConstructiveMicroscopicLaw := by
    calc
      completionLaw.toConstructiveSectorLaw.toConstructiveMicroscopicLaw =
          data.lawNativeConstructiveMicroscopicLaw := hmicroscopic
      _ = data.lawNativeConstructiveSectorLaw.toConstructiveMicroscopicLaw := by
        symm
        exact data.lawNativeConstructiveSectorLaw_toConstructiveMicroscopicLaw
  exact
    constructiveSectorLaw_eq_of_field_eq
      hmicroscopic'
      hgeneration
      hintrinsic
      hminimal

/-- The extracted assembly state bridge already remembers the smaller
constructive microscopic law: its local-event object is exactly the one read
from that smaller law. So once the extracted assembly state bridge matches the
law-native terminal exactification bridge, the smaller constructive
microscopic law is already forced, and the three explicit Step 3 fields then
force the whole constructive sector law. -/
theorem lawNativeSectorCollapseOfExtractedStateBridgeAndStep3Data
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (completionLaw : LocalEventFourStateCompletionLaw Index Time Carrier Law)
    (hassemblyStateBridge :
      completionLaw.toFourStateAssembly.toLocalEventFourStateLaw.toLocalEventStateBridge =
        data.toLocalEventStateBridge)
    (hgeneration :
      completionLaw.canonicalGeneration = data.canonicalGeneration)
    (hintrinsic :
      completionLaw.generatedFromIntrinsicChannelAlgebra =
        data.intrinsicGenerationClause)
    (hminimal :
      completionLaw.minimalCompatibleRealizationsOnly =
        data.minimalCompatibilityClause) :
    completionLaw.toConstructiveSectorLaw =
      data.lawNativeConstructiveSectorLaw := by
  have hobject :
      completionLaw.toConstructiveSectorLaw.toConstructiveMicroscopicLaw.toLocalEventObject =
        data.localEventObject := by
    simpa [LocalEventFourStateCompletionLaw.toFourStateAssembly,
      FourStateAssembly.toLocalEventFourStateLaw,
      FourStateAssembly.toLocalEventObject,
      LocalEventFourStateLaw.toLocalEventStateBridge]
      using congrArg LocalEventStateBridge.object hassemblyStateBridge
  have hmicroscopic :
      completionLaw.toConstructiveSectorLaw.toConstructiveMicroscopicLaw =
        data.lawNativeConstructiveMicroscopicLaw := by
    calc
      completionLaw.toConstructiveSectorLaw.toConstructiveMicroscopicLaw =
          completionLaw.toConstructiveSectorLaw.toConstructiveMicroscopicLaw.toLocalEventObject.toConstructiveMicroscopicLaw := by
        symm
        exact
          ConstructiveMicroscopicLaw.toLocalEventObject_toConstructiveMicroscopicLaw
            completionLaw.toConstructiveSectorLaw.toConstructiveMicroscopicLaw
      _ = data.localEventObject.toConstructiveMicroscopicLaw := by
        exact congrArg LocalEventObject.toConstructiveMicroscopicLaw hobject
      _ = data.lawNativeConstructiveMicroscopicLaw := by
        simpa [data.lawNativeConstructiveMicroscopicLaw_toLocalEventObject]
          using
            (ConstructiveMicroscopicLaw.toLocalEventObject_toConstructiveMicroscopicLaw
              data.lawNativeConstructiveMicroscopicLaw)
  exact
    data.lawNativeSectorCollapseOfMicroscopicLawAndStep3Data
      completionLaw
      hmicroscopic
      hgeneration
      hintrinsic
      hminimal

/-- Once the smaller constructive sector law has already collapsed to the
law-native one, an explicit local state-bridge identification for the
extracted four-state assembly forces the fixed law-native assembly itself. This
isolates the remaining current-side assembly comparison from the Step 3
collapse. -/
theorem lawNativeAssemblyFillOfExtractedStateBridge
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (completionLaw : LocalEventFourStateCompletionLaw Index Time Carrier Law)
    (hsector :
      completionLaw.toConstructiveSectorLaw =
        data.lawNativeConstructiveSectorLaw)
    (hassemblyStateBridge :
      completionLaw.toFourStateAssembly.toLocalEventFourStateLaw.toLocalEventStateBridge =
        data.toLocalEventStateBridge) :
    hsector ▸ completionLaw.toFourStateAssembly =
      data.lawNativeFourStateAssembly := by
  have hassemblyBridge :
      (hsector ▸ completionLaw.toFourStateAssembly).toLocalEventFourStateLaw.toLocalEventStateBridge =
        data.lawNativeFourStateAssembly.toLocalEventFourStateLaw.toLocalEventStateBridge := by
    calc
      (hsector ▸ completionLaw.toFourStateAssembly).toLocalEventFourStateLaw.toLocalEventStateBridge =
          completionLaw.toFourStateAssembly.toLocalEventFourStateLaw.toLocalEventStateBridge := by
        exact FourStateAssembly.localEventStateBridge_transport hsector completionLaw.toFourStateAssembly
      _ = data.toLocalEventStateBridge := hassemblyStateBridge
      _ = data.lawNativeFourStateAssembly.toLocalEventFourStateLaw.toLocalEventStateBridge := by
        symm
        exact data.lawNativeFourStateAssembly_toLocalEventStateBridge
  exact FourStateAssembly.eq_of_localEventStateBridge_eq hassemblyBridge

/-- One Step 4 completion alignment on the law-native sector law upgrades that
fixed four-state assembly to a canonical law-native no-stage completion law. -/
def lawNativeCompletionLawOfAlignment
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (alignment : CompletionAlignment data.lawNativeConstructiveSectorLaw) :
    LocalEventFourStateCompletionLaw Index Time Carrier Law :=
  let bridge :=
    data.lawNativeFourStateAssembly.toNoStageCompletionBridge alignment
  bridge.toLocalEventFourStateCompletionLaw

/-- The reconstructed law-native completion law lives on the same selected
bridge as the law-native microscopic law. -/
theorem lawNativeCompletionLawOfAlignment_sameBridge
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (alignment : CompletionAlignment data.lawNativeConstructiveSectorLaw) :
    (data.lawNativeCompletionLawOfAlignment alignment).fourStateLaw.framed.object.bridge =
      data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge := by
  unfold TerminalExactificationLaw.lawNativeCompletionLawOfAlignment
  simp [NoStageCompletionBridge.toLocalEventFourStateCompletionLaw,
    NoStageCompletionBridge.toLocalEventFourStateLaw,
    NoStageCompletionBridge.toFramedLocalEventObject,
    NoStageCompletionBridge.toLocalEventObject,
    FourStateAssembly.toNoStageCompletionBridge,
    ConstructiveMicroscopicLaw.toLocalEventObject]
  unfold ConstructiveSectorLaw.toMicroscopicClosureLaw
  rfl

/-- The reconstructed law-native completion law uses the same physical
principle as the law-native microscopic law. -/
theorem lawNativeCompletionLawOfAlignment_samePhysicalPrinciple
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (alignment : CompletionAlignment data.lawNativeConstructiveSectorLaw) :
    (data.lawNativeCompletionLawOfAlignment alignment).fourStateLaw.framed.object.physicalPrinciple =
      data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple := by
  unfold TerminalExactificationLaw.lawNativeCompletionLawOfAlignment
  simp [NoStageCompletionBridge.toLocalEventFourStateCompletionLaw,
    NoStageCompletionBridge.toLocalEventFourStateLaw,
    NoStageCompletionBridge.toFramedLocalEventObject,
    NoStageCompletionBridge.toLocalEventObject,
    FourStateAssembly.toNoStageCompletionBridge,
    ConstructiveMicroscopicLaw.toLocalEventObject]
  unfold ConstructiveSectorLaw.toMicroscopicClosureLaw
  rfl

private theorem lawNativeCompletionLawOfAlignment_sector
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (alignment : CompletionAlignment data.lawNativeConstructiveSectorLaw) :
    (data.lawNativeCompletionLawOfAlignment alignment).toConstructiveSectorLaw =
      data.lawNativeConstructiveSectorLaw := by
  unfold TerminalExactificationLaw.lawNativeCompletionLawOfAlignment
  simp [NoStageCompletionBridge.toLocalEventFourStateCompletionLaw,
    NoStageCompletionBridge.toLocalEventFourStateLaw,
    NoStageCompletionBridge.toFramedLocalEventObject,
    NoStageCompletionBridge.toLocalEventObject,
    FourStateAssembly.toNoStageCompletionBridge,
    LocalEventFourStateCompletionLaw.toConstructiveSectorLaw,
    ConstructiveMicroscopicLaw.toLocalEventObject]
  unfold TerminalExactificationLaw.lawNativeConstructiveSectorLaw
  rfl

private theorem lawNativeCompletionLawOfAlignment_assembly
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (alignment : CompletionAlignment data.lawNativeConstructiveSectorLaw) :
    (lawNativeCompletionLawOfAlignment_sector data alignment) ▸
        (data.lawNativeCompletionLawOfAlignment alignment).toFourStateAssembly =
      data.lawNativeFourStateAssembly := by
  cases lawNativeCompletionLawOfAlignment_sector data alignment
  unfold TerminalExactificationLaw.lawNativeCompletionLawOfAlignment
  simp [NoStageCompletionBridge.toLocalEventFourStateCompletionLaw,
    NoStageCompletionBridge.toLocalEventFourStateLaw,
    NoStageCompletionBridge.toFramedLocalEventObject,
    NoStageCompletionBridge.toLocalEventObject,
    FourStateAssembly.toNoStageCompletionBridge,
    LocalEventFourStateCompletionLaw.toConstructiveSectorLaw,
    LocalEventFourStateCompletionLaw.toFourStateReadout,
    LocalEventFourStateCompletionLaw.toFourStateAssembly,
    ConstructiveMicroscopicLaw.toLocalEventObject]
  unfold TerminalExactificationLaw.lawNativeConstructiveSectorLaw
  unfold TerminalExactificationLaw.lawNativeFourStateAssembly
  unfold TerminalExactificationLaw.lawNativeFourStateReadout
  rfl

/-- On the fixed selected bridge, canonical representative identities already
realize the weaker carrier-classification target on the law-native Step 4
surface. So carrier classification is no longer an independent Step 4 import
once the canonical representatives themselves are supplied. -/
theorem completionClassificationTargetOfRepresentatives
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (hrepresentatives :
      CanonicalRepresentativeTarget data.lawNativeConstructiveSectorLaw) :
    CompletionClassificationTarget data.lawNativeConstructiveSectorLaw := by
  rcases hrepresentatives with ⟨representatives⟩
  exact representatives.classificationTarget

/-- The terminal exactification law already determines the current-side
four-state readout package on the law-native fixed-bridge sector law. -/
def fourStateReadout
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (canonicalGeneration : SelectedBundle.CanonicalGeneration)
    (generatedFromIntrinsicChannelAlgebra : Prop)
    (minimalCompatibleRealizationsOnly : Prop)
    (hgenerated : generatedFromIntrinsicChannelAlgebra)
    (hminimal : minimalCompatibleRealizationsOnly) :
    FourStateReadout
      (data.constructiveSectorLaw
        canonicalGeneration
        generatedFromIntrinsicChannelAlgebra
        minimalCompatibleRealizationsOnly
        hgenerated
        hminimal) where
  readout := data.readout
  frame := data.frame

/-- The exactifier/generator intertwining target on the fixed-bridge sector law
is already carried by the terminal exactification law itself. -/
theorem exactifierRealizationTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (canonicalGeneration : SelectedBundle.CanonicalGeneration)
    (generatedFromIntrinsicChannelAlgebra : Prop)
    (minimalCompatibleRealizationsOnly : Prop)
    (hgenerated : generatedFromIntrinsicChannelAlgebra)
    (hminimal : minimalCompatibleRealizationsOnly) :
    ExactifierRealizationTarget
      (data.fourStateReadout
        canonicalGeneration
        generatedFromIntrinsicChannelAlgebra
        minimalCompatibleRealizationsOnly
        hgenerated
        hminimal) := by
  exact data.exactifierRealized

/-- The current-side four-state assembly target on the law-native sector law is
therefore no longer detached once terminal exactification is assumed. -/
theorem fourStateAssemblyTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (canonicalGeneration : SelectedBundle.CanonicalGeneration)
    (generatedFromIntrinsicChannelAlgebra : Prop)
    (minimalCompatibleRealizationsOnly : Prop)
    (hgenerated : generatedFromIntrinsicChannelAlgebra)
    (hminimal : minimalCompatibleRealizationsOnly) :
    FourStateAssemblyTarget
      (data.constructiveSectorLaw
        canonicalGeneration
        generatedFromIntrinsicChannelAlgebra
        minimalCompatibleRealizationsOnly
        hgenerated
        hminimal) := by
  exact
    (data.fourStateReadout
      canonicalGeneration
      generatedFromIntrinsicChannelAlgebra
      minimalCompatibleRealizationsOnly
      hgenerated
      hminimal).assemblyTargetOfExactifierTarget
        (data.exactifierRealizationTarget
          canonicalGeneration
          generatedFromIntrinsicChannelAlgebra
          minimalCompatibleRealizationsOnly
          hgenerated
          hminimal)

/-- Once the law-native rigidity target and the canonical representative target
are supplied on the fixed bridge, the four-state exactifier seam is gone and no
independent carrier-classification target remains: classification is already
read off the canonical representatives. -/
theorem completionSplitTargetOfRigidityAndRepresentatives
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (hrigidity :
      CompletionRigidityTarget data.lawNativeConstructiveSectorLaw)
    (hrepresentatives :
      CanonicalRepresentativeTarget data.lawNativeConstructiveSectorLaw) :
    CompletionSplitTarget data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw := by
  exact
    ConstructiveSectorLaw.completionSplitTargetOfRigidityAndRepresentatives
      (data.lawNativeConstructiveSectorLaw)
      data.lawNativeFourStateReadout
      data.lawNativeExactifierRealizationTarget
      hrigidity
      hrepresentatives

/-- The same reduced Step 4 input also already yields the split completion-bridge
target on the law-native microscopic law. -/
theorem completionBridgeTargetOfRigidityAndRepresentatives
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (hrigidity :
      CompletionRigidityTarget data.lawNativeConstructiveSectorLaw)
    (hrepresentatives :
      CanonicalRepresentativeTarget data.lawNativeConstructiveSectorLaw) :
    NoStageCompletionBridgeTarget
      data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw := by
  exact
    ConstructiveSectorLaw.completionBridgeTargetOfRigidityAndRepresentatives
      (data.lawNativeConstructiveSectorLaw)
      data.lawNativeFourStateReadout
      data.lawNativeExactifierRealizationTarget
      hrigidity
      hrepresentatives

/-- Therefore, on a fixed selected bridge, the remaining Step 4 input below the
no-stage completion target has contracted to the law-native rigidity target and
the canonical representative target. No separate carrier-classification target
remains. -/
theorem completionTargetOfRigidityAndRepresentatives
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (hrigidity :
      CompletionRigidityTarget data.lawNativeConstructiveSectorLaw)
    (hrepresentatives :
      CanonicalRepresentativeTarget data.lawNativeConstructiveSectorLaw) :
    NoStageCompletionTarget data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw := by
  exact
    ConstructiveSectorLaw.completionTargetOfRigidityAndRepresentatives
      (data.lawNativeConstructiveSectorLaw)
      data.lawNativeFourStateReadout
      data.lawNativeExactifierRealizationTarget
      hrigidity
      hrepresentatives

/-- If the two smaller Step 4 existence targets are supplied on that same
fixed-bridge sector law, then terminal exactification already removes the
separate exactifier seam from the split completion target. -/
theorem completionSplitTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (canonicalGeneration : SelectedBundle.CanonicalGeneration)
    (generatedFromIntrinsicChannelAlgebra : Prop)
    (minimalCompatibleRealizationsOnly : Prop)
    (hgenerated : generatedFromIntrinsicChannelAlgebra)
    (hminimal : minimalCompatibleRealizationsOnly)
    (hrigidity :
      CompletionRigidityTarget
        (data.constructiveSectorLaw
          canonicalGeneration
          generatedFromIntrinsicChannelAlgebra
          minimalCompatibleRealizationsOnly
          hgenerated
          hminimal))
    (hrepresentatives :
      CanonicalRepresentativeTarget
        (data.constructiveSectorLaw
          canonicalGeneration
          generatedFromIntrinsicChannelAlgebra
          minimalCompatibleRealizationsOnly
          hgenerated
          hminimal)) :
    CompletionSplitTarget
      ((data.constructiveSectorLaw
          canonicalGeneration
          generatedFromIntrinsicChannelAlgebra
          minimalCompatibleRealizationsOnly
          hgenerated
          hminimal).toMicroscopicClosureLaw) := by
  exact
    (data.constructiveSectorLaw
      canonicalGeneration
      generatedFromIntrinsicChannelAlgebra
      minimalCompatibleRealizationsOnly
      hgenerated
      hminimal).completionSplitTargetOfSplitData
        (data.fourStateReadout
          canonicalGeneration
          generatedFromIntrinsicChannelAlgebra
          minimalCompatibleRealizationsOnly
          hgenerated
          hminimal)
        (data.exactifierRealizationTarget
          canonicalGeneration
          generatedFromIntrinsicChannelAlgebra
          minimalCompatibleRealizationsOnly
          hgenerated
          hminimal)
        hrigidity
        hrepresentatives

/-- Under the same Step 3 and reduced Step 4 hypotheses, terminal exactification
also removes the exactifier seam from the split completion-bridge target. -/
theorem completionBridgeTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (canonicalGeneration : SelectedBundle.CanonicalGeneration)
    (generatedFromIntrinsicChannelAlgebra : Prop)
    (minimalCompatibleRealizationsOnly : Prop)
    (hgenerated : generatedFromIntrinsicChannelAlgebra)
    (hminimal : minimalCompatibleRealizationsOnly)
    (hrigidity :
      CompletionRigidityTarget
        (data.constructiveSectorLaw
          canonicalGeneration
          generatedFromIntrinsicChannelAlgebra
          minimalCompatibleRealizationsOnly
          hgenerated
          hminimal))
    (hrepresentatives :
      CanonicalRepresentativeTarget
        (data.constructiveSectorLaw
          canonicalGeneration
          generatedFromIntrinsicChannelAlgebra
          minimalCompatibleRealizationsOnly
          hgenerated
          hminimal)) :
    NoStageCompletionBridgeTarget
      ((data.constructiveSectorLaw
          canonicalGeneration
          generatedFromIntrinsicChannelAlgebra
          minimalCompatibleRealizationsOnly
          hgenerated
          hminimal).toMicroscopicClosureLaw) := by
  exact
    (data.constructiveSectorLaw
      canonicalGeneration
      generatedFromIntrinsicChannelAlgebra
      minimalCompatibleRealizationsOnly
      hgenerated
      hminimal).completionBridgeTargetOfSplitData
        (data.fourStateReadout
          canonicalGeneration
          generatedFromIntrinsicChannelAlgebra
          minimalCompatibleRealizationsOnly
          hgenerated
          hminimal)
        (data.exactifierRealizationTarget
          canonicalGeneration
          generatedFromIntrinsicChannelAlgebra
          minimalCompatibleRealizationsOnly
          hgenerated
          hminimal)
        hrigidity
        hrepresentatives

/-- Under the same Step 3 and reduced Step 4 hypotheses, terminal exactification
therefore already supplies the no-stage completion target on that same
microscopic law. -/
theorem completionTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (canonicalGeneration : SelectedBundle.CanonicalGeneration)
    (generatedFromIntrinsicChannelAlgebra : Prop)
    (minimalCompatibleRealizationsOnly : Prop)
    (hgenerated : generatedFromIntrinsicChannelAlgebra)
    (hminimal : minimalCompatibleRealizationsOnly)
    (hrigidity :
      CompletionRigidityTarget
        (data.constructiveSectorLaw
          canonicalGeneration
          generatedFromIntrinsicChannelAlgebra
          minimalCompatibleRealizationsOnly
          hgenerated
          hminimal))
    (hrepresentatives :
      CanonicalRepresentativeTarget
        (data.constructiveSectorLaw
          canonicalGeneration
          generatedFromIntrinsicChannelAlgebra
          minimalCompatibleRealizationsOnly
          hgenerated
          hminimal)) :
    NoStageCompletionTarget
      ((data.constructiveSectorLaw
          canonicalGeneration
          generatedFromIntrinsicChannelAlgebra
          minimalCompatibleRealizationsOnly
          hgenerated
          hminimal).toMicroscopicClosureLaw) := by
  exact
    (data.constructiveSectorLaw
      canonicalGeneration
      generatedFromIntrinsicChannelAlgebra
      minimalCompatibleRealizationsOnly
      hgenerated
      hminimal).completionTargetOfSplitData
        (data.fourStateReadout
          canonicalGeneration
          generatedFromIntrinsicChannelAlgebra
          minimalCompatibleRealizationsOnly
          hgenerated
          hminimal)
        (data.exactifierRealizationTarget
          canonicalGeneration
          generatedFromIntrinsicChannelAlgebra
          minimalCompatibleRealizationsOnly
          hgenerated
          hminimal)
        hrigidity
        hrepresentatives

/-- On the same law-native microscopic law, one fixed no-stage completion
bridge together with the four lane-rigidity targets already forces the direct
flagship normal-form target. This is the sharpest current law-native bridge
from the public two-law surface to the recognizable flagship identities: the
remaining input is no longer the full endpoint/frontier witness bundle, but
only the four lane-specific rigidity packages on one law-native completion
bridge. -/
theorem normalFormTargetOfBridgeRigidityTargets
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (completionBridge : NoStageCompletionBridge Index Time Carrier Law)
    (sameLaw :
      completionBridge.toMicroscopicClosureLaw =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw)
    (hphase : PhaseRigidityTarget completionBridge)
    (hwave : WaveRigidityTarget completionBridge)
    (hgauge : GaugeRigidityTarget completionBridge)
    (hgeometric : GeometricRigidityTarget completionBridge) :
    NormalFormTarget data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw := by
  have hnormal :
      NormalFormTarget completionBridge.toMicroscopicClosureLaw :=
    completionBridge.normalFormTargetOfRigidityTargets
      hphase hwave hgauge hgeometric
  exact sameLaw ▸ hnormal

/-- The same data already reassemble one law-native split normal-form bridge on
that microscopic law. This makes the remaining collapsing object explicit:
once one fixed no-stage completion bridge and the four lane-rigidity targets
are present on the same completion datum, they are exactly one
`NormalFormBridge`. -/
theorem normalFormBridgeTargetOfRigidityTargets
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (completionBridge : NoStageCompletionBridge Index Time Carrier Law)
    (sameLaw :
      completionBridge.toMicroscopicClosureLaw =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw)
    (hphase : PhaseRigidityTarget completionBridge)
    (hwave : WaveRigidityTarget completionBridge)
    (hgauge : GaugeRigidityTarget completionBridge)
    (hgeometric : GeometricRigidityTarget completionBridge) :
    ∃ bridge : NormalFormBridge Index Time Carrier Law,
      bridge.completionBridge = completionBridge ∧
      bridge.toMicroscopicClosureLaw =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw := by
  rcases hphase with ⟨phase⟩
  rcases hwave with ⟨wave⟩
  rcases hgauge with ⟨gauge⟩
  rcases hgeometric with ⟨geometric⟩
  refine
    ⟨completionBridge.toNormalFormBridge phase wave gauge geometric,
      rfl, ?_⟩
  simpa [NormalFormBridge.toMicroscopicClosureLaw] using sameLaw

/-- The explicit law-native split normal-form bridge obtained from the fixed
completion bridge and the four lane-rigidity targets already carries the full
recognizable flagship surface on that microscopic law. -/
theorem normalFormBridgeFullSurfaceOfRigidityTargets
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (completionBridge : NoStageCompletionBridge Index Time Carrier Law)
    (sameLaw :
      completionBridge.toMicroscopicClosureLaw =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw)
    (hphase : PhaseRigidityTarget completionBridge)
    (hwave : WaveRigidityTarget completionBridge)
    (hgauge : GaugeRigidityTarget completionBridge)
    (hgeometric : GeometricRigidityTarget completionBridge) :
    ∃ bridge : NormalFormBridge Index Time Carrier Law,
      bridge.toMicroscopicClosureLaw =
          data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw ∧
        Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
        Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
        realized_generator_carries_bedrock_law
          bridge.toMicroscopicClosureLaw.bridge.generator ∧
        AutonomousHorizon
          bridge.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
          bridge.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
          bridge.toMicroscopicClosureLaw.bridge.generator ∧
        horizonFiberInvariant
          bridge.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
          bridge.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
          bridge.toMicroscopicClosureLaw.bridge.generator ∧
        PartIVLawCompletionStatement
          bridge.completionBridge.toLocalEventFourStateCompletionLaw.toNaturalOperatorCompletion ∧
        Nonempty
          (PhaseLane.RecognizableIdentity
            Time Carrier Law bridge.PhaseField bridge.PhaseScalar) ∧
        Nonempty
          (WaveLane.RecognizableIdentity
            Time Carrier Law bridge.WaveField bridge.WaveScalar) ∧
        Nonempty
          (GaugeLane.RecognizableIdentity
            Time Carrier Law bridge.GaugeField bridge.GaugeSource) ∧
        Nonempty
          (GeometricLane.RecognizableIdentity
            Time Carrier Law bridge.GeometricTensor bridge.GeometricScalar) := by
  rcases hphase with ⟨phase⟩
  rcases hwave with ⟨wave⟩
  rcases hgauge with ⟨gauge⟩
  rcases hgeometric with ⟨geometric⟩
  let bridge := completionBridge.toNormalFormBridge phase wave gauge geometric
  refine ⟨bridge, ?_, ?_⟩
  simpa [bridge, NormalFormBridge.toMicroscopicClosureLaw] using sameLaw
  simpa [bridge, NormalFormBridge.toMicroscopicClosureLaw] using bridge.fullSurface

/-- The same law-native completion bridge and four lane-rigidity targets
already yield the full detached normal-form surface on that microscopic law. -/
theorem fullNormalFormSurfaceOfBridgeRigidityTargets
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (completionBridge : NoStageCompletionBridge Index Time Carrier Law)
    (sameLaw :
      completionBridge.toMicroscopicClosureLaw =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw)
    (hphase : PhaseRigidityTarget completionBridge)
    (hwave : WaveRigidityTarget completionBridge)
    (hgauge : GaugeRigidityTarget completionBridge)
    (hgeometric : GeometricRigidityTarget completionBridge) :
    ∃ witness :
        NoStageCompletionWitness
          data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw,
      ∃ normalForms : FlagshipNormalForms Time Carrier Law,
        witness.completionLaw.fourStateLaw.framed.object.bridge =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
          witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
          Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
          Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
          realized_generator_carries_bedrock_law
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge.generator ∧
          AutonomousHorizon
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge.generator ∧
          horizonFiberInvariant
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge.generator ∧
          PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              normalForms.PhaseField
              normalForms.PhaseScalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              normalForms.WaveField
              normalForms.WaveScalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GaugeField
              normalForms.GaugeSource) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GeometricTensor
              normalForms.GeometricScalar) := by
  have hsurface :
      ∃ witness : NoStageCompletionWitness completionBridge.toMicroscopicClosureLaw,
        ∃ normalForms : FlagshipNormalForms Time Carrier Law,
          witness.completionLaw.fourStateLaw.framed.object.bridge =
              completionBridge.toMicroscopicClosureLaw.bridge ∧
            witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
              completionBridge.toMicroscopicClosureLaw.physicalPrinciple ∧
            Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
            Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
            realized_generator_carries_bedrock_law
              completionBridge.toMicroscopicClosureLaw.bridge.generator ∧
            AutonomousHorizon
              completionBridge.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
              completionBridge.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
              completionBridge.toMicroscopicClosureLaw.bridge.generator ∧
            horizonFiberInvariant
              completionBridge.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
              completionBridge.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
              completionBridge.toMicroscopicClosureLaw.bridge.generator ∧
            PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion ∧
            Nonempty
              (PhaseLane.RecognizableIdentity
                Time Carrier Law
                normalForms.PhaseField
                normalForms.PhaseScalar) ∧
            Nonempty
              (WaveLane.RecognizableIdentity
                Time Carrier Law
                normalForms.WaveField
                normalForms.WaveScalar) ∧
            Nonempty
              (GaugeLane.RecognizableIdentity
                Time Carrier Law
                normalForms.GaugeField
                normalForms.GaugeSource) ∧
            Nonempty
              (GeometricLane.RecognizableIdentity
                Time Carrier Law
                normalForms.GeometricTensor
                normalForms.GeometricScalar) :=
    completionBridge.fullSurfaceOfRigidityTargets
      hphase hwave hgauge hgeometric
  exact sameLaw ▸ hsurface

/-- A law-native completion bridge together with one aggregate flagship
boundary target on its own no-stage witness already recovers the endpoint-
complete strong microscopic package on that same microscopic law. This is the
current sharp strong-lane reduction: once the common completion bridge is
fixed, the remaining explicit flagship supplement is one boundary target on
that same witness, not a detached flagship package imported from above. -/
theorem strongMicroscopicLawOfBridgeBoundaryTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (completionBridge : NoStageCompletionBridge Index Time Carrier Law)
    (sameLaw :
      completionBridge.toMicroscopicClosureLaw =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw)
    (hboundary :
      FlagshipBoundaryTarget completionBridge.toNoStageCompletionWitness) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw = completionBridge.toLocalEventFourStateCompletionLaw ∧
      strong.completionLaw.toMicroscopicClosureLaw =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw := by
  rcases
      completionBridge.toNoStageCompletionWitness.flagshipSurfaceOfBoundaryTarget
        hboundary with
    ⟨endpointWitnesses, _hcompletion, _hphase, _hwave, _hgauge, _hgeometric⟩
  refine
    ⟨{ completionLaw := completionBridge.toLocalEventFourStateCompletionLaw
       endpointWitnesses := endpointWitnesses },
      rfl, ?_⟩
  simpa using sameLaw

/-- The same law-native completion bridge and aggregate flagship boundary
target already recover the strong microscopic package and therefore the
analytic flagship surface and exact physical equation field on that same
microscopic law. -/
theorem strongMicroscopicLawSurfaceOfBridgeBoundaryTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (completionBridge : NoStageCompletionBridge Index Time Carrier Law)
    (sameLaw :
      completionBridge.toMicroscopicClosureLaw =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw)
    (hboundary :
      FlagshipBoundaryTarget completionBridge.toNoStageCompletionWitness) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw = completionBridge.toLocalEventFourStateCompletionLaw ∧
      strong.completionLaw.toMicroscopicClosureLaw =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong := by
  rcases
      data.strongMicroscopicLawOfBridgeBoundaryTarget
        completionBridge sameLaw hboundary with
    ⟨strong, hcompletion, hmicroscopic⟩
  exact
    ⟨strong,
      hcompletion,
      hmicroscopic,
      LocalEventFourStateFlagshipLaw.analyticSurface strong,
      LocalEventFourStateFlagshipLaw.physicalEquationSurface strong⟩

/-- Single law-native flagship witness target on the public two-law surface.
It is the current sharp single object still needed above the law-native
constructive microscopic law in order to recover the endpoint-complete strong
microscopic package: one no-stage completion witness on that same microscopic
law, carrying one exact endpoint-witness bundle on its own selected bundle. -/
def flagshipWitnessTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  FlagshipTarget data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw

/-- One endpoint-complete law-native flagship witness package above a fixed
smaller microscopic closure law: one no-stage completion witness together with
one exact flagship endpoint-witness bundle on that same completion law. -/
abbrev FlagshipWitnessPackage
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) :=
  Σ witness : NoStageCompletionWitness law,
    FlagshipEndpointWitnesses witness.completionLaw

/-- Canonical law-native flagship witness target on the public two-law
surface. This is the uniqueness-strengthened sharp object: the law-native
microscopic law carries exactly one endpoint-complete witness package. -/
def canonicalFlagshipWitnessTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  ∃ target : FlagshipWitnessPackage law,
    ∀ other : FlagshipWitnessPackage law, other = target

/-- Canonical strong microscopic target on the public two-law surface. This is
the same uniqueness statement read through the manuscript-facing strong law:
there is one unique endpoint-complete strong microscopic law on the same bridge
and physical principle as the law-native microscopic law. -/
def canonicalStrongMicroscopicLawTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
    strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      ∀ other : StrongMicroscopicLaw Index Time Carrier Law,
        other.completionLaw.fourStateLaw.framed.object.bridge =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge →
          other.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple →
          other = strong

/-- Universal law-native frontier fill above the public two-law surface:
every no-stage completion witness on the law-native microscopic law already
carries some flagship frontier bundle on its own completion law. -/
def universalFlagshipFrontierFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  ∀ witness : NoStageCompletionWitness law,
    Nonempty (FlagshipFrontiers witness.completionLaw)

/-- Universal law-native boundary fill above the public two-law surface:
every no-stage completion witness on the law-native microscopic law already
meets the aggregate flagship boundary target on its own completion law. -/
def universalFlagshipBoundaryFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  ∀ witness : NoStageCompletionWitness law,
    FlagshipBoundaryTarget witness

/-- Universal law-native endpoint-witness fill above the public two-law
surface: every no-stage completion witness on the law-native microscopic law
already carries an aggregate endpoint-witness package on its own completion
law. -/
def universalEndpointWitnessFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  ∀ witness : NoStageCompletionWitness law,
    EndpointWitnessTarget witness

/-- Universal law-native strong microscopic extension above the public two-law
surface: every no-stage completion witness on the law-native microscopic law
already extends to some endpoint-complete strong microscopic law on that same
completion law. -/
def universalStrongMicroscopicExtensionTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  ∀ witness : NoStageCompletionWitness law,
    StrongMicroscopicExtensionTarget witness

/-- Exact two-part bottleneck behind the canonical completion target: one
unique flagship witness package together with universal law-native frontier
fill on every no-stage completion witness. -/
def canonicalFlagshipWitnessFrontierFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  data.canonicalFlagshipWitnessTarget ∧
    data.universalFlagshipFrontierFillTarget

/-- Boundary-target form of the same exact two-part bottleneck: one unique
flagship witness package together with universal law-native boundary fill on
every no-stage completion witness. -/
def canonicalFlagshipWitnessBoundaryFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  data.canonicalFlagshipWitnessTarget ∧
    data.universalFlagshipBoundaryFillTarget

/-- Strong-law form of the same exact two-part bottleneck: one unique strong
microscopic law on the same bridge and physical principle as the law-native
microscopic law, together with universal law-native boundary fill on every
completion witness. -/
def canonicalStrongMicroscopicLawBoundaryFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  data.canonicalStrongMicroscopicLawTarget ∧
    data.universalFlagshipBoundaryFillTarget

/-- Endpoint-witness form of the same exact two-part bottleneck: one unique
strong microscopic law on the same bridge and physical principle as the
law-native microscopic law, together with universal law-native aggregate
endpoint-witness fill on every completion witness. -/
def canonicalStrongMicroscopicLawEndpointFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  data.canonicalStrongMicroscopicLawTarget ∧
    data.universalEndpointWitnessFillTarget

/-- Strong-law extension form of the same exact two-part bottleneck: one
unique strong microscopic law on the same bridge and physical principle as the
law-native microscopic law, together with universal strong microscopic
extension on every law-native no-stage completion witness. -/
def canonicalStrongMicroscopicLawExtensionTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  data.canonicalStrongMicroscopicLawTarget ∧
    data.universalStrongMicroscopicExtensionTarget

/-- Completion-collapse form of the same exact two-part bottleneck: one
unique strong microscopic law on the same bridge and physical principle as the
law-native microscopic law, and every law-native no-stage completion witness
already carries exactly that same completion law. -/
def canonicalStrongMicroscopicLawCompletionCollapseTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
    strong.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        law.physicalPrinciple ∧
      (∀ other : StrongMicroscopicLaw Index Time Carrier Law,
        other.completionLaw.fourStateLaw.framed.object.bridge = law.bridge →
          other.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple →
          other = strong) ∧
      ∀ witness : NoStageCompletionWitness law,
        witness.completionLaw = strong.completionLaw

/-- Completion-witness form of the same exact two-part bottleneck: one unique
strong microscopic law on the same bridge and physical principle as the
law-native microscopic law, together with one unique law-native no-stage
completion witness. This is the same canonical-collapse statement read through
the witness object itself rather than through universal completion-law
equalities. -/
def canonicalStrongMicroscopicLawCompletionWitnessTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  data.canonicalStrongMicroscopicLawTarget ∧
    ∃ witness : NoStageCompletionWitness law,
      ∀ other : NoStageCompletionWitness law, other = witness

/-- Completion-law form of the same exact two-part bottleneck: one unique
strong microscopic law on the same bridge and physical principle as the
law-native microscopic law, together with one unique no-stage completion law
on that same selected bridge and physical principle. This is the same
canonical-collapse statement read through the public completion-law object
itself rather than through the attached witness wrapper. -/
def canonicalStrongMicroscopicLawCompletionLawTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  data.canonicalStrongMicroscopicLawTarget ∧
    ∃ completionLaw : LocalEventFourStateCompletionLaw Index Time Carrier Law,
      completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
        completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          law.physicalPrinciple ∧
        ∀ other : LocalEventFourStateCompletionLaw Index Time Carrier Law,
          other.fourStateLaw.framed.object.bridge = law.bridge →
            other.fourStateLaw.framed.object.physicalPrinciple =
              law.physicalPrinciple →
            other = completionLaw

/-- Bare unique-completion-law bottleneck on the public two-law surface: there
is one unique no-stage completion law on the same selected bridge and physical
principle as the law-native microscopic law. This is the clean completion-side
uniqueness statement before any endpoint-witness or strong-law packaging is
attached. -/
def canonicalCompletionLawTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  ∃ completionLaw : LocalEventFourStateCompletionLaw Index Time Carrier Law,
    completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
      completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        law.physicalPrinciple ∧
      ∀ other : LocalEventFourStateCompletionLaw Index Time Carrier Law,
        other.fourStateLaw.framed.object.bridge = law.bridge →
          other.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple →
          other = completionLaw

/-- Completion-law / endpoint-bundle form of the same exact bottleneck: one
unique no-stage completion law on the same selected bridge and physical
principle as the law-native microscopic law, together with one unique
aggregate flagship endpoint-witness bundle on that same completion law. Since
the strong microscopic law is exactly the completion law plus this endpoint
bundle, this is the same canonical-collapse statement with the strong-law
packaging removed. -/
def canonicalCompletionLawEndpointBundleTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  ∃ completionLaw : LocalEventFourStateCompletionLaw Index Time Carrier Law,
    completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
      completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        law.physicalPrinciple ∧
      (∀ other : LocalEventFourStateCompletionLaw Index Time Carrier Law,
        other.fourStateLaw.framed.object.bridge = law.bridge →
          other.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple →
          other = completionLaw) ∧
      ∃ endpointWitnesses : FlagshipEndpointWitnesses completionLaw,
        ∀ other : FlagshipEndpointWitnesses completionLaw,
          other = endpointWitnesses

/-- Honest boundary-form candidate law on the public two-law surface: one
unique no-stage completion law on the same selected bridge and physical
principle as the law-native microscopic law, together with aggregate flagship
boundary closure on that same law. Because the remaining flagship datum is a
proposition on the completion witness, uniqueness now reduces entirely to the
completion law itself. -/
def canonicalBoundaryMicroscopicLawTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  ∃ completionLaw : LocalEventFourStateCompletionLaw Index Time Carrier Law,
    completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
      completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        law.physicalPrinciple ∧
      (∀ other : LocalEventFourStateCompletionLaw Index Time Carrier Law,
        other.fourStateLaw.framed.object.bridge = law.bridge →
          other.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple →
          other = completionLaw) ∧
      FlagshipBoundaryTarget completionLaw.toNoStageCompletionWitness

/-- Completion-law-side universal boundary fill on the public two-law surface:
every no-stage completion law on the law-native bridge and physical principle
already satisfies the aggregate flagship boundary target on its canonical
witness. -/
def universalCompletionLawBoundaryFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  ∀ completionLaw : LocalEventFourStateCompletionLaw Index Time Carrier Law,
    completionLaw.fourStateLaw.framed.object.bridge = law.bridge →
      completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        law.physicalPrinciple →
      FlagshipBoundaryTarget completionLaw.toNoStageCompletionWitness

/-- Exact law-facing completion target on the public two-law surface: one
unique no-stage completion law on the law-native bridge and physical
principle, together with automatic aggregate flagship boundary closure on every
such completion law. Since the completion law is already unique, the universal
fill clause is equivalent to boundary closure on that unique law, but it makes
the remaining flagship datum read as an automatic law-side consequence rather
than as an extra chosen witness. -/
def canonicalCompletionLawBoundaryFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  ∃ completionLaw : LocalEventFourStateCompletionLaw Index Time Carrier Law,
    completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
      completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        law.physicalPrinciple ∧
      (∀ other : LocalEventFourStateCompletionLaw Index Time Carrier Law,
        other.fourStateLaw.framed.object.bridge = law.bridge →
          other.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple →
          other = completionLaw) ∧
      data.universalCompletionLawBoundaryFillTarget

/-- Stricter upstream route to the exact completion-law boundary bottleneck.
It asks for two genuinely law-native facts:

* every aligned no-stage completion law already collapses to the same
  law-native constructive sector law and the same fixed four-state assembly;
* the remaining Step 4 completion alignment on that one law-native sector law
  is unique, and the resulting reconstructed completion law is already
  boundary-complete.

This is stronger than the exact bottleneck, but it isolates the concrete place
where the present proof chain would close if the remaining law-native collapse
and alignment-uniqueness statements were proved. -/
def canonicalLawNativeAlignmentBoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  (∀ completionLaw : LocalEventFourStateCompletionLaw Index Time Carrier Law,
    completionLaw.fourStateLaw.framed.object.bridge = law.bridge →
      completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        law.physicalPrinciple →
      ∃ hsector :
          completionLaw.toConstructiveSectorLaw =
            data.lawNativeConstructiveSectorLaw,
        hsector ▸ completionLaw.toFourStateAssembly =
          data.lawNativeFourStateAssembly) ∧
  ∃ alignment : CompletionAlignment data.lawNativeConstructiveSectorLaw,
    (∀ other : CompletionAlignment data.lawNativeConstructiveSectorLaw,
      other = alignment) ∧
    FlagshipBoundaryTarget
      (data.lawNativeCompletionLawOfAlignment alignment).toNoStageCompletionWitness

/-- More explicit current-side route to the same collapse statement. Instead
of asking directly for sector-law/assembly collapse, it asks only that every
aligned completion law on the law-native bridge and physical principle already
matches the law-native visible current-side surface:

* the same local state bridge;
* the same canonical generation package;
* the same two remaining Step 3 clauses.

Together with one unique law-native Step 4 alignment and boundary closure on
its reconstructed completion law, this already forces the older
alignment-boundary route target. -/
def canonicalLawNativeVisibleStateBridgeTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  ∀ completionLaw : LocalEventFourStateCompletionLaw Index Time Carrier Law,
    completionLaw.fourStateLaw.framed.object.bridge = law.bridge →
      completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        law.physicalPrinciple →
      completionLaw.fourStateLaw.toLocalEventStateBridge =
          data.toLocalEventStateBridge ∧
        completionLaw.toFourStateAssembly.toLocalEventFourStateLaw.toLocalEventStateBridge =
          data.toLocalEventStateBridge

/-- Pure Step 3 packaging target behind the explicit current-side route: every
aligned completion law on the law-native bridge and physical principle already
stores exactly the same Step 3 package as the law-native terminal exactification
datum. This isolates the literal proposition-level packaging seam from the
visible current-side state-bridge comparison. -/
def canonicalLawNativeStep3PackageTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  ∀ completionLaw : LocalEventFourStateCompletionLaw Index Time Carrier Law,
    completionLaw.fourStateLaw.framed.object.bridge = law.bridge →
      completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        law.physicalPrinciple →
      completionLaw.canonicalGeneration = data.canonicalGeneration ∧
        completionLaw.generatedFromIntrinsicChannelAlgebra =
          data.intrinsicGenerationClause ∧
        completionLaw.minimalCompatibleRealizationsOnly =
          data.minimalCompatibilityClause

/-- Smaller current-side target behind the explicit law-native route: every
aligned completion law on the law-native bridge and physical principle already
has the same extracted four-state-assembly state bridge and the same three
Step 3 fields as the law-native terminal exactification datum. This is the
exact current-side surface consumed by the assembly-fill theorem, so it avoids
carrying both versions of the same visible state comparison. -/
def canonicalLawNativeCurrentSurfaceTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  ∀ completionLaw : LocalEventFourStateCompletionLaw Index Time Carrier Law,
    completionLaw.fourStateLaw.framed.object.bridge = law.bridge →
      completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        law.physicalPrinciple →
      completionLaw.toFourStateAssembly.toLocalEventFourStateLaw.toLocalEventStateBridge =
          data.toLocalEventStateBridge ∧
      completionLaw.canonicalGeneration = data.canonicalGeneration ∧
        completionLaw.generatedFromIntrinsicChannelAlgebra =
          data.intrinsicGenerationClause ∧
        completionLaw.minimalCompatibleRealizationsOnly =
          data.minimalCompatibilityClause

/-- Smaller constructive current-side collapse target behind the law-native
route: every aligned completion law on the law-native bridge and physical
principle already has the same smaller constructive microscopic law as the
law-native terminal exactification datum. This removes the larger
local-state-bridge wrapper from the current-side uniqueness statement. -/
def canonicalLawNativeMicroscopicCollapseTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  ∀ completionLaw : LocalEventFourStateCompletionLaw Index Time Carrier Law,
    completionLaw.fourStateLaw.framed.object.bridge = law.bridge →
      completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        law.physicalPrinciple →
      completionLaw.toConstructiveSectorLaw.toConstructiveMicroscopicLaw =
        data.lawNativeConstructiveMicroscopicLaw

/-- More explicit current-side route to the same collapse statement. Instead
of asking directly for sector-law/assembly collapse, it asks only that every
aligned completion law on the law-native bridge and physical principle already
matches the law-native visible current-side surface and the exact Step 3
packaging carried by the terminal exactification datum. -/
def canonicalLawNativeStateBridgeBoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  (∀ completionLaw : LocalEventFourStateCompletionLaw Index Time Carrier Law,
    completionLaw.fourStateLaw.framed.object.bridge = law.bridge →
      completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        law.physicalPrinciple →
      completionLaw.fourStateLaw.toLocalEventStateBridge =
          data.toLocalEventStateBridge ∧
        completionLaw.toFourStateAssembly.toLocalEventFourStateLaw.toLocalEventStateBridge =
          data.toLocalEventStateBridge ∧
        completionLaw.canonicalGeneration = data.canonicalGeneration ∧
        completionLaw.generatedFromIntrinsicChannelAlgebra =
          data.intrinsicGenerationClause ∧
        completionLaw.minimalCompatibleRealizationsOnly =
          data.minimalCompatibilityClause) ∧
  ∃ alignment : CompletionAlignment data.lawNativeConstructiveSectorLaw,
    (∀ other : CompletionAlignment data.lawNativeConstructiveSectorLaw,
      other = alignment) ∧
    FlagshipBoundaryTarget
      (data.lawNativeCompletionLawOfAlignment alignment).toNoStageCompletionWitness

/-- Smaller split-Step-4 form of the same stricter law-native route. The
completion-law collapse clause is unchanged, but the unique Step 4 remainder is
now expressed through the two smaller packages from which the alignment is
rebuilt: one law-native rigidity package and one canonical representative
package. Boundary closure is required only on the reconstructed law-native
completion law determined by those two pieces. -/
def canonicalLawNativePartsBoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  (∀ completionLaw : LocalEventFourStateCompletionLaw Index Time Carrier Law,
    completionLaw.fourStateLaw.framed.object.bridge = law.bridge →
      completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        law.physicalPrinciple →
      ∃ hsector :
          completionLaw.toConstructiveSectorLaw =
            data.lawNativeConstructiveSectorLaw,
        hsector ▸ completionLaw.toFourStateAssembly =
          data.lawNativeFourStateAssembly) ∧
  ∃ rigidity : CompletionRigidity data.lawNativeConstructiveSectorLaw,
    (∀ other : CompletionRigidity data.lawNativeConstructiveSectorLaw,
      other = rigidity) ∧
    ∃ representatives : CanonicalRepresentatives,
      (∀ other : CanonicalRepresentatives, other = representatives) ∧
      FlagshipBoundaryTarget
        (data.lawNativeCompletionLawOfAlignment
          (CompletionAlignment.ofParts rigidity representatives)).toNoStageCompletionWitness

/-- Smaller rigidity-split form of the same stricter law-native route. The
fixed-bridge completion-law collapse clause is unchanged, but the remaining
Step 4 uniqueness is now expressed through the actual mathematical pieces used
to build the law-native rigidity package:

* one unique endpoint-rigidity principle on the fixed intrinsic sector
  generation;
* one unique reduced endpoint-rigidity surface;
* one unique canonical representative package.

Boundary closure is again required only on the reconstructed law-native
completion law determined by those pieces. -/
def canonicalLawNativeRigidityBoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  (∀ completionLaw : LocalEventFourStateCompletionLaw Index Time Carrier Law,
    completionLaw.fourStateLaw.framed.object.bridge = law.bridge →
      completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        law.physicalPrinciple →
      ∃ hsector :
          completionLaw.toConstructiveSectorLaw =
            data.lawNativeConstructiveSectorLaw,
        hsector ▸ completionLaw.toFourStateAssembly =
          data.lawNativeFourStateAssembly) ∧
  ∃ rigidityPrinciple : EndpointRigidity.Principle Time Carrier Law,
    ∃ usesSectorGeneration :
        rigidityPrinciple.sectorGeneration =
          data.lawNativeConstructiveSectorLaw.toIntrinsicSectorGeneration,
      (∀ other : EndpointRigidity.Principle Time Carrier Law,
        other.sectorGeneration =
            data.lawNativeConstructiveSectorLaw.toIntrinsicSectorGeneration →
          other = rigidityPrinciple) ∧
      ∃ endpointRigidity : EndpointRigidity.Reduction Time Carrier Law,
        (∀ other : EndpointRigidity.Reduction Time Carrier Law,
          other = endpointRigidity) ∧
        ∃ representatives : CanonicalRepresentatives,
          (∀ other : CanonicalRepresentatives, other = representatives) ∧
          FlagshipBoundaryTarget
            (data.lawNativeCompletionLawOfAlignment
              (CompletionAlignment.ofParts
                (CompletionRigidity.ofParts
                  rigidityPrinciple
                  usesSectorGeneration
                  endpointRigidity)
                representatives)).toNoStageCompletionWitness

/-- Isolated current-side collapse clause in the stricter law-native route:
every aligned no-stage completion law on the law-native bridge and physical
principle already collapses to the same constructive sector law and the same
fixed four-state assembly. -/
def canonicalLawNativeCompletionCollapseTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  ∀ completionLaw : LocalEventFourStateCompletionLaw Index Time Carrier Law,
    completionLaw.fourStateLaw.framed.object.bridge = law.bridge →
      completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        law.physicalPrinciple →
      ∃ hsector :
          completionLaw.toConstructiveSectorLaw =
            data.lawNativeConstructiveSectorLaw,
        hsector ▸ completionLaw.toFourStateAssembly =
          data.lawNativeFourStateAssembly

/-- First current-side clause behind law-native completion collapse: every
aligned no-stage completion law on the law-native bridge and physical
principle already has the same smaller constructive sector law. This isolates
the Step 3/current-side collapse of the completion law before the four-state
assembly is compared. -/
def canonicalLawNativeSectorCollapseTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  ∀ completionLaw : LocalEventFourStateCompletionLaw Index Time Carrier Law,
    completionLaw.fourStateLaw.framed.object.bridge = law.bridge →
      completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        law.physicalPrinciple →
      completionLaw.toConstructiveSectorLaw =
        data.lawNativeConstructiveSectorLaw

/-- Second current-side clause behind law-native completion collapse: once the
smaller constructive sector law has already collapsed to the law-native one,
the current-side four-state assembly is forced on that fixed law-native sector
law. This is the exact current-side assembly uniqueness statement remaining
after the sector-law surface has been identified. -/
def canonicalLawNativeAssemblyFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  ∀ completionLaw : LocalEventFourStateCompletionLaw Index Time Carrier Law,
    completionLaw.fourStateLaw.framed.object.bridge = law.bridge →
      completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        law.physicalPrinciple →
      ∀ hsector :
          completionLaw.toConstructiveSectorLaw =
            data.lawNativeConstructiveSectorLaw,
        hsector ▸ completionLaw.toFourStateAssembly =
          data.lawNativeFourStateAssembly

/-- Isolated Step 4 remainder in the stricter law-native route: on the fixed
law-native sector law, endpoint rigidity and the canonical representative
package are unique, and the reconstructed law-native completion law is already
boundary-complete. This no longer mentions arbitrary completion laws at all. -/
def canonicalLawNativeStep4BoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  ∃ rigidityPrinciple : EndpointRigidity.Principle Time Carrier Law,
    ∃ usesSectorGeneration :
        rigidityPrinciple.sectorGeneration =
          data.lawNativeConstructiveSectorLaw.toIntrinsicSectorGeneration,
      (∀ other : EndpointRigidity.Principle Time Carrier Law,
        other.sectorGeneration =
            data.lawNativeConstructiveSectorLaw.toIntrinsicSectorGeneration →
          other = rigidityPrinciple) ∧
      ∃ endpointRigidity : EndpointRigidity.Reduction Time Carrier Law,
        (∀ other : EndpointRigidity.Reduction Time Carrier Law,
          other = endpointRigidity) ∧
        ∃ representatives : CanonicalRepresentatives,
          (∀ other : CanonicalRepresentatives, other = representatives) ∧
          FlagshipBoundaryTarget
            (data.lawNativeCompletionLawOfAlignment
              (CompletionAlignment.ofParts
                (CompletionRigidity.ofParts
                  rigidityPrinciple
                  usesSectorGeneration
                  endpointRigidity)
                representatives)).toNoStageCompletionWitness

/-- Pure fixed-assembly Step 4 form of the same law-native remainder: on the
fixed law-native sector law there is one unique completion alignment, and the
reconstructed law-native completion law is already boundary-complete. This is
the honest alignment-level surface remembered by the split bridge once the
current-side collapse clause is removed. -/
def canonicalLawNativeAlignmentBoundaryTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  ∃ alignment : CompletionAlignment data.lawNativeConstructiveSectorLaw,
    (∀ other : CompletionAlignment data.lawNativeConstructiveSectorLaw,
      other = alignment) ∧
    FlagshipBoundaryTarget
      (data.lawNativeCompletionLawOfAlignment alignment).toNoStageCompletionWitness

/-- Smaller sharp route to canonical selected completion: every aligned
completion law already carries the same extracted current-side surface as the
law-native datum, and on the fixed law-native sector law there is one unique
completion alignment with boundary closure on its reconstructed completion law.
The separate microscopic-collapse clause has been absorbed into the extracted
current-side surface. -/
def canonicalLawNativeCurrentBoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  data.canonicalLawNativeCurrentSurfaceTarget ∧
    data.canonicalLawNativeAlignmentBoundaryTarget

/-- Sharper explicit upstream route: every aligned completion law already
shares the same smaller constructive microscopic law and the same extracted
current-side surface as the law-native datum, and there is one unique
law-native Step 4 alignment with boundary closure on its reconstructed
completion law. This is smaller than the visible-state-bridge route because it
removes the full local-state-bridge wrapper from the current-side collapse
clause. -/
def canonicalLawNativeMicroscopicCurrentBoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  data.canonicalLawNativeMicroscopicCollapseTarget ∧
    data.canonicalLawNativeCurrentSurfaceTarget ∧
    data.canonicalLawNativeAlignmentBoundaryTarget

/-- Literal unique candidate-law target on the fixed law-native current-side
assembly. This is smaller than `BoundaryMicroscopicLaw`: the law-native sector
law and the law-native four-state assembly are already fixed, so the only
remaining datum is one Step 4 alignment together with aggregate boundary
closure on the reconstructed canonical witness. -/
def canonicalCompletionBoundaryLawTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  ∃ law :
      CompletionBoundaryLaw
        Index Time Carrier Law
        data.lawNativeConstructiveSectorLaw
        data.lawNativeFourStateAssembly,
    ∀ other :
        CompletionBoundaryLaw
          Index Time Carrier Law
          data.lawNativeConstructiveSectorLaw
          data.lawNativeFourStateAssembly,
      other = law

/-- Exact law-facing fixed-assembly candidate-law target on the public two-law
surface: there is one unique completion-boundary law on the law-native sector
law and law-native four-state assembly, and every alignment on that same fixed
sector law is already boundary-complete on its reconstructed canonical
witness. This is the direct candidate-law form of the fixed-assembly Step 4
remainder once the current-side collapse clause has been removed. -/
def canonicalCompletionBoundaryLawFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  data.canonicalCompletionBoundaryLawTarget ∧
    ∀ alignment : CompletionAlignment data.lawNativeConstructiveSectorLaw,
      FlagshipBoundaryTarget
        (data.lawNativeCompletionLawOfAlignment alignment).toNoStageCompletionWitness

/-- Selected-cut endpoint terminality on the public two-law surface. On the
fixed law-native sector law and four-state assembly, there is one canonical
completion-boundary law and every law-native alignment is already
boundary-complete on its reconstructed canonical witness. This isolates the
fixed-assembly completion theorem from the current-side collapse clause. -/
abbrev selectedCutEndpointTerminalityTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  data.canonicalCompletionBoundaryLawFillTarget

/-- Canonical selected completion target on the public two-law surface. This
is the exact remaining upstream theorem: every aligned completion on the
law-native bridge and physical principle collapses to the same law-native
fixed assembly, and on that fixed assembly there is one unique
completion-boundary law with automatic boundary closure across the whole
law-native alignment class. -/
def canonicalSelectedCompletionTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  data.canonicalLawNativeCompletionCollapseTarget ∧
    data.canonicalCompletionBoundaryLawFillTarget

private theorem fourStateAssembly_transport_irrel
    {Index Time Carrier Law : Type}
    {data : TerminalExactificationLaw Index Time Carrier Law}
    {completionLaw : LocalEventFourStateCompletionLaw Index Time Carrier Law}
    (hsector hsector' :
      completionLaw.toConstructiveSectorLaw =
        data.lawNativeConstructiveSectorLaw) :
    hsector ▸ completionLaw.toFourStateAssembly =
      hsector' ▸ completionLaw.toFourStateAssembly := by
  have hproof : hsector = hsector' := Subsingleton.elim _ _
  cases hproof
  rfl

/-- The older current-side completion-collapse clause already contains the
smaller sector-law collapse statement. -/
theorem canonicalLawNativeSectorCollapseTargetOfCanonicalLawNativeCompletionCollapseTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeCompletionCollapseTarget) :
    data.canonicalLawNativeSectorCollapseTarget := by
  intro completionLaw hbridge hprinciple
  rcases htarget completionLaw hbridge hprinciple with ⟨hsector, _hassembly⟩
  exact hsector

/-- The same current-side completion-collapse clause also contains the smaller
fixed-sector assembly-fill statement. Once the smaller constructive sector law
has already been identified, the four-state assembly comparison is exactly the
remaining current-side surface. -/
theorem canonicalLawNativeAssemblyFillTargetOfCanonicalLawNativeCompletionCollapseTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeCompletionCollapseTarget) :
    data.canonicalLawNativeAssemblyFillTarget := by
  intro completionLaw hbridge hprinciple hsector
  rcases htarget completionLaw hbridge hprinciple with ⟨hsector', hassembly⟩
  calc
    hsector ▸ completionLaw.toFourStateAssembly =
        hsector' ▸ completionLaw.toFourStateAssembly :=
      fourStateAssembly_transport_irrel hsector hsector'
    _ = data.lawNativeFourStateAssembly := hassembly

/-- Conversely, once current-side collapse is split into the smaller
constructive-sector collapse and the fixed-sector assembly-fill statement, the
original completion-collapse clause is recovered immediately. -/
theorem canonicalLawNativeCompletionCollapseTargetOfCanonicalLawNativeSectorCollapseTarget_and_canonicalLawNativeAssemblyFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalLawNativeSectorCollapseTarget ∧
        data.canonicalLawNativeAssemblyFillTarget) :
    data.canonicalLawNativeCompletionCollapseTarget := by
  rcases htarget with ⟨hsectorCollapse, hassemblyFill⟩
  intro completionLaw hbridge hprinciple
  have hsector :
      completionLaw.toConstructiveSectorLaw =
        data.lawNativeConstructiveSectorLaw :=
    hsectorCollapse completionLaw hbridge hprinciple
  exact ⟨hsector, hassemblyFill completionLaw hbridge hprinciple hsector⟩

/-- So the current-side completion-collapse clause itself now splits exactly
into two smaller problems: collapse of the smaller constructive sector law and
forced four-state assembly fill on that fixed law-native sector law. -/
theorem canonicalLawNativeCompletionCollapseTarget_iff_canonicalLawNativeSectorCollapseTarget_and_canonicalLawNativeAssemblyFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalLawNativeCompletionCollapseTarget ↔
      (data.canonicalLawNativeSectorCollapseTarget ∧
        data.canonicalLawNativeAssemblyFillTarget) := by
  constructor
  · intro htarget
    exact
      ⟨data.canonicalLawNativeSectorCollapseTargetOfCanonicalLawNativeCompletionCollapseTarget
          htarget,
        data.canonicalLawNativeAssemblyFillTargetOfCanonicalLawNativeCompletionCollapseTarget
          htarget⟩
  · intro htarget
    exact
      data.canonicalLawNativeCompletionCollapseTargetOfCanonicalLawNativeSectorCollapseTarget_and_canonicalLawNativeAssemblyFillTarget
        htarget

/-- The canonical selected completion target can therefore be read more
sharply as three independent clauses: smaller sector-law collapse, fixed-sector
four-state assembly fill, and the unique fixed-assembly boundary-law target. -/
theorem canonicalSelectedCompletionTarget_iff_canonicalLawNativeSectorCollapseTarget_and_canonicalLawNativeAssemblyFillTarget_and_canonicalCompletionBoundaryLawFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalSelectedCompletionTarget ↔
      (data.canonicalLawNativeSectorCollapseTarget ∧
        data.canonicalLawNativeAssemblyFillTarget ∧
        data.canonicalCompletionBoundaryLawFillTarget) := by
  constructor
  · intro htarget
    rcases htarget with ⟨hcollapse, hboundary⟩
    have hsplit :
        data.canonicalLawNativeSectorCollapseTarget ∧
          data.canonicalLawNativeAssemblyFillTarget :=
      (data.canonicalLawNativeCompletionCollapseTarget_iff_canonicalLawNativeSectorCollapseTarget_and_canonicalLawNativeAssemblyFillTarget).1
        hcollapse
    rcases hsplit with ⟨hsector, hassembly⟩
    exact ⟨hsector, hassembly, hboundary⟩
  · intro htarget
    rcases htarget with ⟨hsector, hassembly, hboundary⟩
    have hcollapse :
        data.canonicalLawNativeCompletionCollapseTarget :=
      (data.canonicalLawNativeCompletionCollapseTarget_iff_canonicalLawNativeSectorCollapseTarget_and_canonicalLawNativeAssemblyFillTarget).2
        ⟨hsector, hassembly⟩
    exact ⟨hcollapse, hboundary⟩

/-- The visible current-side state-bridge clause together with literal Step 3
packaging coherence already forces the smaller constructive sector law on every
aligned completion law. This isolates the exact Step 3 current-side collapse
argument needed upstream. -/
theorem canonicalLawNativeSectorCollapseTargetOfCanonicalLawNativeVisibleStateBridgeTarget_and_canonicalLawNativeStep3PackageTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalLawNativeVisibleStateBridgeTarget ∧
        data.canonicalLawNativeStep3PackageTarget) :
    data.canonicalLawNativeSectorCollapseTarget := by
  rcases htarget with ⟨hvisible, hstep3⟩
  intro completionLaw hbridge hprinciple
  rcases hvisible completionLaw hbridge hprinciple with ⟨hstateBridge, _hassemblyStateBridge⟩
  rcases hstep3 completionLaw hbridge hprinciple with
    ⟨hgeneration, hintrinsic, hminimal⟩
  exact
    data.lawNativeSectorCollapseOfStateBridgeAndStep3Data
      completionLaw
      hstateBridge
      hgeneration
      hintrinsic
      hminimal

/-- Sector-law collapse already forces equality of the smaller constructive
microscopic law on every aligned completion law. So once the smaller Step 3
package has collapsed, the microscopic law collapses automatically as well. -/
theorem canonicalLawNativeMicroscopicCollapseTargetOfCanonicalLawNativeSectorCollapseTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeSectorCollapseTarget) :
    data.canonicalLawNativeMicroscopicCollapseTarget := by
  intro completionLaw hbridge hprinciple
  calc
    completionLaw.toConstructiveSectorLaw.toConstructiveMicroscopicLaw =
        data.lawNativeConstructiveSectorLaw.toConstructiveMicroscopicLaw := by
      exact congrArg ConstructiveSectorLaw.toConstructiveMicroscopicLaw
        (htarget completionLaw hbridge hprinciple)
    _ = data.lawNativeConstructiveMicroscopicLaw := by
      exact data.lawNativeConstructiveSectorLaw_toConstructiveMicroscopicLaw

/-- The larger visible current-side route already gives the smaller extracted
current-side surface: the extracted assembly state bridge together with the
three explicit Step 3 fields. This removes the redundant larger
local-state-bridge equality from the current-side collapse package. -/
theorem canonicalLawNativeCurrentSurfaceTargetOfCanonicalLawNativeVisibleStateBridgeTarget_and_canonicalLawNativeStep3PackageTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalLawNativeVisibleStateBridgeTarget ∧
        data.canonicalLawNativeStep3PackageTarget) :
    data.canonicalLawNativeCurrentSurfaceTarget := by
  rcases htarget with ⟨hvisible, hstep3⟩
  intro completionLaw hbridge hprinciple
  rcases hvisible completionLaw hbridge hprinciple with
    ⟨_hstateBridge, hassemblyStateBridge⟩
  rcases hstep3 completionLaw hbridge hprinciple with
    ⟨hgeneration, hintrinsic, hminimal⟩
  exact ⟨hassemblyStateBridge, hgeneration, hintrinsic, hminimal⟩

/-- The extracted current-side surface alone already forces the smaller
constructive sector law on every aligned completion law. The extracted
assembly state bridge remembers the smaller constructive microscopic law, so
no separate microscopic-collapse clause is needed. -/
theorem canonicalLawNativeSectorCollapseTargetOfCanonicalLawNativeCurrentSurfaceTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeCurrentSurfaceTarget) :
    data.canonicalLawNativeSectorCollapseTarget := by
  intro completionLaw hbridge hprinciple
  rcases htarget completionLaw hbridge hprinciple with
    ⟨hassemblyStateBridge, hgeneration, hintrinsic, hminimal⟩
  exact
    data.lawNativeSectorCollapseOfExtractedStateBridgeAndStep3Data
      completionLaw
      hassemblyStateBridge
      hgeneration
      hintrinsic
      hminimal

/-- Therefore the larger visible-state-bridge route already implies the
smaller constructive-microscopic collapse target. This records the honest
content of the old route after removing the larger bridge wrapper. -/
theorem canonicalLawNativeMicroscopicCollapseTargetOfCanonicalLawNativeVisibleStateBridgeTarget_and_canonicalLawNativeStep3PackageTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalLawNativeVisibleStateBridgeTarget ∧
        data.canonicalLawNativeStep3PackageTarget) :
    data.canonicalLawNativeMicroscopicCollapseTarget := by
  exact
    data.canonicalLawNativeMicroscopicCollapseTargetOfCanonicalLawNativeSectorCollapseTarget
      (data.canonicalLawNativeSectorCollapseTargetOfCanonicalLawNativeVisibleStateBridgeTarget_and_canonicalLawNativeStep3PackageTarget
        htarget)

/-- Once the visible current-side state-bridge clause is known and the smaller
constructive sector law has already collapsed, the fixed four-state assembly is
forced as well. The remaining current-side comparison is exactly the extracted
assembly state bridge. -/
theorem canonicalLawNativeAssemblyFillTargetOfCanonicalLawNativeVisibleStateBridgeTarget_and_canonicalLawNativeSectorCollapseTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalLawNativeVisibleStateBridgeTarget ∧
        data.canonicalLawNativeSectorCollapseTarget) :
    data.canonicalLawNativeAssemblyFillTarget := by
  rcases htarget with ⟨hvisible, hsectorCollapse⟩
  intro completionLaw hbridge hprinciple hsector
  have hsector' :
      completionLaw.toConstructiveSectorLaw =
        data.lawNativeConstructiveSectorLaw :=
    hsectorCollapse completionLaw hbridge hprinciple
  rcases hvisible completionLaw hbridge hprinciple with
    ⟨_hstateBridge, hassemblyStateBridge⟩
  calc
    hsector ▸ completionLaw.toFourStateAssembly =
        hsector' ▸ completionLaw.toFourStateAssembly :=
      fourStateAssembly_transport_irrel hsector hsector'
    _ = data.lawNativeFourStateAssembly :=
      data.lawNativeAssemblyFillOfExtractedStateBridge
        completionLaw
        hsector'
        hassemblyStateBridge

/-- Therefore the two explicit current-side clauses already force the whole
current-side completion-collapse statement. No further current-side datum
remains beyond visible state-bridge rigidity and literal Step 3 coherence. -/
theorem canonicalLawNativeCompletionCollapseTargetOfCanonicalLawNativeVisibleStateBridgeTarget_and_canonicalLawNativeStep3PackageTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalLawNativeVisibleStateBridgeTarget ∧
        data.canonicalLawNativeStep3PackageTarget) :
    data.canonicalLawNativeCompletionCollapseTarget := by
  have hsector :
      data.canonicalLawNativeSectorCollapseTarget :=
    data.canonicalLawNativeSectorCollapseTargetOfCanonicalLawNativeVisibleStateBridgeTarget_and_canonicalLawNativeStep3PackageTarget
      htarget
  have hassembly :
      data.canonicalLawNativeAssemblyFillTarget :=
    data.canonicalLawNativeAssemblyFillTargetOfCanonicalLawNativeVisibleStateBridgeTarget_and_canonicalLawNativeSectorCollapseTarget
      ⟨htarget.1, hsector⟩
  exact
    data.canonicalLawNativeCompletionCollapseTargetOfCanonicalLawNativeSectorCollapseTarget_and_canonicalLawNativeAssemblyFillTarget
      ⟨hsector, hassembly⟩

/-- The exact current-side completion collapse theorem only needs the smaller
constructive microscopic collapse target together with the extracted
current-side surface. Once those are in hand, the law-native sector law and
the fixed four-state assembly are both forced. -/
theorem canonicalLawNativeCompletionCollapseTargetOfCanonicalLawNativeMicroscopicCollapseTarget_and_canonicalLawNativeCurrentSurfaceTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalLawNativeMicroscopicCollapseTarget ∧
        data.canonicalLawNativeCurrentSurfaceTarget) :
    data.canonicalLawNativeCompletionCollapseTarget := by
  rcases htarget with ⟨hmicroscopic, hcurrent⟩
  have hsector : data.canonicalLawNativeSectorCollapseTarget := by
    intro completionLaw hbridge hprinciple
    have hmicroscopicLaw :=
      hmicroscopic completionLaw hbridge hprinciple
    rcases hcurrent completionLaw hbridge hprinciple with
      ⟨_hassemblyStateBridge, hgeneration, hintrinsic, hminimal⟩
    exact
      data.lawNativeSectorCollapseOfMicroscopicLawAndStep3Data
        completionLaw
        hmicroscopicLaw
        hgeneration
        hintrinsic
        hminimal
  have hassembly : data.canonicalLawNativeAssemblyFillTarget := by
    intro completionLaw hbridge hprinciple hsector
    rcases hcurrent completionLaw hbridge hprinciple with
      ⟨hassemblyStateBridge, _hgeneration, _hintrinsic, _hminimal⟩
    exact
      data.lawNativeAssemblyFillOfExtractedStateBridge
        completionLaw
        hsector
        hassemblyStateBridge
  exact
    data.canonicalLawNativeCompletionCollapseTargetOfCanonicalLawNativeSectorCollapseTarget_and_canonicalLawNativeAssemblyFillTarget
      ⟨hsector, hassembly⟩

/-- In fact the extracted current-side surface already forces the whole
current-side completion collapse target by itself. The separate microscopic
collapse clause is redundant once the extracted assembly state bridge and the
three explicit Step 3 fields are already known. -/
theorem canonicalLawNativeCompletionCollapseTargetOfCanonicalLawNativeCurrentSurfaceTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeCurrentSurfaceTarget) :
    data.canonicalLawNativeCompletionCollapseTarget := by
  have hsector : data.canonicalLawNativeSectorCollapseTarget :=
    data.canonicalLawNativeSectorCollapseTargetOfCanonicalLawNativeCurrentSurfaceTarget
      htarget
  have hassembly : data.canonicalLawNativeAssemblyFillTarget := by
    intro completionLaw hbridge hprinciple hsectorEq
    rcases htarget completionLaw hbridge hprinciple with
      ⟨hassemblyStateBridge, _hgeneration, _hintrinsic, _hminimal⟩
    exact
      data.lawNativeAssemblyFillOfExtractedStateBridge
        completionLaw
        hsectorEq
        hassemblyStateBridge
  exact
    data.canonicalLawNativeCompletionCollapseTargetOfCanonicalLawNativeSectorCollapseTarget_and_canonicalLawNativeAssemblyFillTarget
      ⟨hsector, hassembly⟩

/-- The canonical selected completion target therefore already follows from the
two explicit current-side clauses together with the fixed-assembly
completion-boundary law target. This is the sharpest route that separates the
remaining upstream work into current-side rigidity and Step 4 boundary-law
uniqueness. -/
theorem canonicalSelectedCompletionTargetOfCanonicalLawNativeVisibleStateBridgeTarget_and_canonicalLawNativeStep3PackageTarget_and_canonicalCompletionBoundaryLawFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalLawNativeVisibleStateBridgeTarget ∧
        data.canonicalLawNativeStep3PackageTarget ∧
        data.canonicalCompletionBoundaryLawFillTarget) :
    data.canonicalSelectedCompletionTarget := by
  rcases htarget with ⟨hvisible, hrest⟩
  rcases hrest with ⟨hstep3, hboundary⟩
  have hcollapse :
      data.canonicalLawNativeCompletionCollapseTarget :=
    data.canonicalLawNativeCompletionCollapseTargetOfCanonicalLawNativeVisibleStateBridgeTarget_and_canonicalLawNativeStep3PackageTarget
      ⟨hvisible, hstep3⟩
  exact ⟨hcollapse, hboundary⟩

/-- The low-level Step 4 remainder already rebuilds exactly one alignment on
the fixed law-native sector law whose reconstructed completion law is
boundary-complete. -/
theorem canonicalLawNativeAlignmentBoundaryTargetOfCanonicalLawNativeStep4BoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeStep4BoundaryRouteTarget) :
    data.canonicalLawNativeAlignmentBoundaryTarget := by
  rcases htarget with
    ⟨rigidityPrinciple, usesSectorGeneration, huniquePrinciple,
      endpointRigidity, huniqueEndpointRigidity,
      representatives, huniqueRepresentatives, hboundary⟩
  let rigidity : CompletionRigidity data.lawNativeConstructiveSectorLaw :=
    CompletionRigidity.ofParts
      rigidityPrinciple
      usesSectorGeneration
      endpointRigidity
  have huniqueRigidity :
      ∀ other : CompletionRigidity data.lawNativeConstructiveSectorLaw,
        other = rigidity := by
    intro other
    have hprinciple :
        other.rigidityPrinciple = rigidityPrinciple :=
      huniquePrinciple other.rigidityPrinciple other.usesSectorGeneration
    have hendpoint :
        other.endpointRigidity = endpointRigidity :=
      huniqueEndpointRigidity other.endpointRigidity
    exact CompletionRigidity.eq_of_parts_eq hprinciple hendpoint
  let alignment : CompletionAlignment data.lawNativeConstructiveSectorLaw :=
    CompletionAlignment.ofParts rigidity representatives
  have huniqueAlignment :
      ∀ other : CompletionAlignment data.lawNativeConstructiveSectorLaw,
        other = alignment := by
    intro other
    have hrigidity :
        other.toCompletionRigidity = rigidity :=
      huniqueRigidity other.toCompletionRigidity
    have hrepresentatives :
        other.toCanonicalRepresentatives = representatives :=
      huniqueRepresentatives other.toCanonicalRepresentatives
    calc
      other =
          CompletionAlignment.ofParts
            other.toCompletionRigidity
            other.toCanonicalRepresentatives := by
              symm
              exact CompletionAlignment.ofParts_eq other
      _ = CompletionAlignment.ofParts rigidity representatives := by
            simp [hrigidity, hrepresentatives]
      _ = alignment := rfl
  exact ⟨alignment, huniqueAlignment, by simpa [alignment, rigidity] using hboundary⟩

/-- Conversely, one unique law-native alignment already determines the exact
smaller Step 4 remainder: the alignment remembers exactly one rigidity
principle on the fixed intrinsic sector generation, one reduced endpoint-
rigidity surface, and one canonical representative package. -/
theorem canonicalLawNativeStep4BoundaryRouteTargetOfCanonicalLawNativeAlignmentBoundaryTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeAlignmentBoundaryTarget) :
    data.canonicalLawNativeStep4BoundaryRouteTarget := by
  rcases htarget with ⟨alignment, huniqueAlignment, hboundary⟩
  let rigidity : CompletionRigidity data.lawNativeConstructiveSectorLaw :=
    alignment.toCompletionRigidity
  let rigidityPrinciple := rigidity.rigidityPrinciple
  let usesSectorGeneration := rigidity.usesSectorGeneration
  let endpointRigidity := rigidity.endpointRigidity
  let representatives : CanonicalRepresentatives :=
    alignment.toCanonicalRepresentatives
  refine
    ⟨rigidityPrinciple, usesSectorGeneration, ?_,
      endpointRigidity, ?_, representatives, ?_, ?_⟩
  · intro other hotherSectorGeneration
    let otherRigidity : CompletionRigidity data.lawNativeConstructiveSectorLaw :=
      CompletionRigidity.ofParts
        other
        hotherSectorGeneration
        endpointRigidity
    have halignment :
        CompletionAlignment.ofParts otherRigidity representatives = alignment :=
      huniqueAlignment (CompletionAlignment.ofParts otherRigidity representatives)
    have hsameRigidity :
        otherRigidity = rigidity := by
      calc
        otherRigidity =
            (CompletionAlignment.ofParts otherRigidity representatives).toCompletionRigidity := by
              symm
              exact CompletionAlignment.ofParts_toCompletionRigidity
                otherRigidity representatives
        _ = alignment.toCompletionRigidity := by
              exact congrArg CompletionAlignment.toCompletionRigidity halignment
        _ = rigidity := rfl
    have hsamePrinciple :
        otherRigidity.rigidityPrinciple = rigidity.rigidityPrinciple := by
      exact congrArg CompletionRigidity.rigidityPrinciple hsameRigidity
    simpa [rigidityPrinciple, otherRigidity] using hsamePrinciple
  · intro other
    let otherRigidity : CompletionRigidity data.lawNativeConstructiveSectorLaw :=
      CompletionRigidity.ofParts
        rigidityPrinciple
        usesSectorGeneration
        other
    have halignment :
        CompletionAlignment.ofParts otherRigidity representatives = alignment :=
      huniqueAlignment (CompletionAlignment.ofParts otherRigidity representatives)
    have hsameRigidity :
        otherRigidity = rigidity := by
      calc
        otherRigidity =
            (CompletionAlignment.ofParts otherRigidity representatives).toCompletionRigidity := by
              symm
              exact CompletionAlignment.ofParts_toCompletionRigidity
                otherRigidity representatives
        _ = alignment.toCompletionRigidity := by
              exact congrArg CompletionAlignment.toCompletionRigidity halignment
        _ = rigidity := rfl
    have hsameEndpoint :
        otherRigidity.endpointRigidity = rigidity.endpointRigidity := by
      exact congrArg CompletionRigidity.endpointRigidity hsameRigidity
    simpa [endpointRigidity, otherRigidity] using hsameEndpoint
  · intro other
    have halignment :
        CompletionAlignment.ofParts rigidity other = alignment :=
      huniqueAlignment (CompletionAlignment.ofParts rigidity other)
    have hsameRepresentatives :
        (CompletionAlignment.ofParts rigidity other).toCanonicalRepresentatives =
          alignment.toCanonicalRepresentatives := by
      exact congrArg CompletionAlignment.toCanonicalRepresentatives halignment
    calc
      other =
          (CompletionAlignment.ofParts rigidity other).toCanonicalRepresentatives := by
            symm
            exact CompletionAlignment.ofParts_toCanonicalRepresentatives rigidity other
      _ = alignment.toCanonicalRepresentatives := hsameRepresentatives
      _ = representatives := rfl
  · have hsameAlignment :
        CompletionAlignment.ofParts rigidity representatives = alignment :=
      CompletionAlignment.ofParts_eq alignment
    simpa [rigidity, rigidityPrinciple, usesSectorGeneration, endpointRigidity,
      representatives, hsameAlignment] using hboundary

/-- So the fixed-assembly Step 4 remainder is exactly the same as one unique
law-native alignment together with aggregate boundary closure on the
reconstructed completion law. -/
theorem canonicalLawNativeStep4BoundaryRouteTarget_iff_canonicalLawNativeAlignmentBoundaryTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalLawNativeStep4BoundaryRouteTarget ↔
      data.canonicalLawNativeAlignmentBoundaryTarget := by
  constructor
  · intro htarget
    exact
      data.canonicalLawNativeAlignmentBoundaryTargetOfCanonicalLawNativeStep4BoundaryRouteTarget
        htarget
  · intro htarget
    exact
      data.canonicalLawNativeStep4BoundaryRouteTargetOfCanonicalLawNativeAlignmentBoundaryTarget
        htarget

/-- One unique law-native alignment already yields one unique fixed-assembly
completion-boundary law. -/
theorem canonicalCompletionBoundaryLawTargetOfCanonicalLawNativeAlignmentBoundaryTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeAlignmentBoundaryTarget) :
    data.canonicalCompletionBoundaryLawTarget := by
  rcases htarget with ⟨alignment, huniqueAlignment, hboundary⟩
  let law :
      CompletionBoundaryLaw
        Index Time Carrier Law
        data.lawNativeConstructiveSectorLaw
        data.lawNativeFourStateAssembly :=
    { alignment := alignment
      boundary := hboundary }
  refine ⟨law, ?_⟩
  intro other
  exact CompletionBoundaryLaw.eq_of_alignment_eq (huniqueAlignment other.alignment)

/-- The same unique-alignment target already yields the sharper fixed-assembly
candidate-law form: one unique completion-boundary law together with automatic
boundary closure on every alignment of the law-native sector law. -/
theorem canonicalCompletionBoundaryLawFillTargetOfCanonicalLawNativeAlignmentBoundaryTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeAlignmentBoundaryTarget) :
    data.canonicalCompletionBoundaryLawFillTarget := by
  rcases htarget with ⟨alignment, huniqueAlignment, hboundary⟩
  refine ⟨?_, ?_⟩
  · exact
      data.canonicalCompletionBoundaryLawTargetOfCanonicalLawNativeAlignmentBoundaryTarget
        ⟨alignment, huniqueAlignment, hboundary⟩
  · intro other
    cases huniqueAlignment other
    exact hboundary

/-- Conversely, the unique fixed-assembly candidate law together with
automatic boundary closure on every alignment already rebuilds the unique
law-native alignment target. -/
theorem canonicalLawNativeAlignmentBoundaryTargetOfCanonicalCompletionBoundaryLawFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionBoundaryLawFillTarget) :
    data.canonicalLawNativeAlignmentBoundaryTarget := by
  rcases htarget with ⟨hlaw, hfill⟩
  rcases hlaw with ⟨law, huniqueLaw⟩
  refine ⟨law.alignment, ?_, hfill law.alignment⟩
  intro other
  let otherLaw :
      CompletionBoundaryLaw
        Index Time Carrier Law
        data.lawNativeConstructiveSectorLaw
        data.lawNativeFourStateAssembly :=
    { alignment := other
      boundary := hfill other }
  exact congrArg CompletionBoundaryLaw.alignment (huniqueLaw otherLaw)

/-- So the fixed-assembly Step 4 remainder is also exactly the same as one
unique candidate law on the law-native assembly together with automatic
boundary closure on every law-native alignment. -/
theorem canonicalCompletionBoundaryLawFillTarget_iff_canonicalLawNativeAlignmentBoundaryTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalCompletionBoundaryLawFillTarget ↔
      data.canonicalLawNativeAlignmentBoundaryTarget := by
  constructor
  · intro htarget
    exact
      data.canonicalLawNativeAlignmentBoundaryTargetOfCanonicalCompletionBoundaryLawFillTarget
        htarget
  · intro htarget
    exact
      data.canonicalCompletionBoundaryLawFillTargetOfCanonicalLawNativeAlignmentBoundaryTarget
        htarget

/-- Selected-cut endpoint terminality is exactly the fixed-assembly alignment
surface: one unique law-native alignment together with boundary closure on its
reconstructed completion law. -/
theorem selectedCutEndpointTerminalityTarget_iff_canonicalLawNativeAlignmentBoundaryTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.selectedCutEndpointTerminalityTarget ↔
      data.canonicalLawNativeAlignmentBoundaryTarget := by
  exact
    data.canonicalCompletionBoundaryLawFillTarget_iff_canonicalLawNativeAlignmentBoundaryTarget

/-- Therefore the fixed-assembly Step 4 remainder alone already yields the
sharper law-facing target: one unique completion-boundary law on the
law-native assembly together with automatic boundary closure on every
law-native alignment. -/
theorem canonicalCompletionBoundaryLawFillTargetOfCanonicalLawNativeStep4BoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeStep4BoundaryRouteTarget) :
    data.canonicalCompletionBoundaryLawFillTarget := by
  exact
    (data.canonicalCompletionBoundaryLawFillTarget_iff_canonicalLawNativeAlignmentBoundaryTarget).2
      (data.canonicalLawNativeAlignmentBoundaryTargetOfCanonicalLawNativeStep4BoundaryRouteTarget
        htarget)

/-- The fixed-assembly Step 4 remainder already yields selected-cut endpoint
terminality. -/
theorem selectedCutEndpointTerminalityTargetOfCanonicalLawNativeStep4BoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeStep4BoundaryRouteTarget) :
    data.selectedCutEndpointTerminalityTarget := by
  exact
    data.canonicalCompletionBoundaryLawFillTargetOfCanonicalLawNativeStep4BoundaryRouteTarget
      htarget

/-- The canonical selected completion target already follows from the smaller
constructive-microscopic current-side route together with one unique
law-native Step 4 alignment. This is the current sharpest strict route that no
longer mentions equality of the larger local-state-bridge object. -/
theorem canonicalSelectedCompletionTargetOfCanonicalLawNativeMicroscopicCurrentBoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeMicroscopicCurrentBoundaryRouteTarget) :
    data.canonicalSelectedCompletionTarget := by
  rcases htarget with ⟨hmicroscopic, hcurrent, halignment⟩
  have hcollapse :
      data.canonicalLawNativeCompletionCollapseTarget :=
    data.canonicalLawNativeCompletionCollapseTargetOfCanonicalLawNativeMicroscopicCollapseTarget_and_canonicalLawNativeCurrentSurfaceTarget
      ⟨hmicroscopic, hcurrent⟩
  have hboundary :
      data.canonicalCompletionBoundaryLawFillTarget :=
    (data.canonicalCompletionBoundaryLawFillTarget_iff_canonicalLawNativeAlignmentBoundaryTarget).2
      halignment
  exact ⟨hcollapse, hboundary⟩

/-- The even smaller extracted-current route already yields the canonical
selected completion target. Once the extracted four-state-assembly state
bridge and the three explicit Step 3 fields are fixed on every aligned
completion law, the separate microscopic-collapse clause is no longer needed.
-/
theorem canonicalSelectedCompletionTargetOfCanonicalLawNativeCurrentBoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeCurrentBoundaryRouteTarget) :
    data.canonicalSelectedCompletionTarget := by
  rcases htarget with ⟨hcurrent, halignment⟩
  have hcollapse :
      data.canonicalLawNativeCompletionCollapseTarget :=
    data.canonicalLawNativeCompletionCollapseTargetOfCanonicalLawNativeCurrentSurfaceTarget
      hcurrent
  have hboundary :
      data.canonicalCompletionBoundaryLawFillTarget :=
    (data.canonicalCompletionBoundaryLawFillTarget_iff_canonicalLawNativeAlignmentBoundaryTarget).2
      halignment
  exact ⟨hcollapse, hboundary⟩

/-- The exact bottleneck already follows from the genuinely remaining split:
the extracted current-side surface on every aligned completion law, together
with the fixed-assembly boundary-law fill theorem. This is the cleanest honest
route once the separate microscopic-collapse clause has been removed. -/
theorem canonicalSelectedCompletionTargetOfCanonicalLawNativeCurrentSurfaceTarget_and_canonicalCompletionBoundaryLawFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalLawNativeCurrentSurfaceTarget ∧
        data.canonicalCompletionBoundaryLawFillTarget) :
    data.canonicalSelectedCompletionTarget := by
  rcases htarget with ⟨hcurrent, hboundary⟩
  have hcollapse :
      data.canonicalLawNativeCompletionCollapseTarget :=
    data.canonicalLawNativeCompletionCollapseTargetOfCanonicalLawNativeCurrentSurfaceTarget
      hcurrent
  exact ⟨hcollapse, hboundary⟩

/-- Once the no-stage completion law itself is unique on the law-native bridge
and physical principle, the extracted current-side surface is automatic: every
aligned completion law must already equal the canonical law-native completion
law reconstructed from any law-native boundary alignment, so its extracted
four-state bridge and Step 3 fields are forced. -/
theorem canonicalLawNativeCurrentSurfaceTargetOfCanonicalCompletionLawTarget_and_canonicalCompletionBoundaryLawFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalCompletionLawTarget ∧
        data.canonicalCompletionBoundaryLawFillTarget) :
    data.canonicalLawNativeCurrentSurfaceTarget := by
  rcases htarget with ⟨hcompletionLaw, hfill⟩
  rcases hcompletionLaw with ⟨completionLaw, hbridge₀, hprinciple₀, hunique₀⟩
  have halignmentTarget :
      data.canonicalLawNativeAlignmentBoundaryTarget :=
    (data.canonicalCompletionBoundaryLawFillTarget_iff_canonicalLawNativeAlignmentBoundaryTarget).1
      hfill
  rcases halignmentTarget with ⟨alignment, _huniqueAlignment, _hboundary⟩
  have hcanonical :
      data.lawNativeCompletionLawOfAlignment alignment = completionLaw :=
    hunique₀
      (data.lawNativeCompletionLawOfAlignment alignment)
      (data.lawNativeCompletionLawOfAlignment_sameBridge alignment)
      (data.lawNativeCompletionLawOfAlignment_samePhysicalPrinciple alignment)
  intro other hbridge hprinciple
  have hother :
      other = completionLaw :=
    hunique₀ other hbridge hprinciple
  have hother' :
      other = data.lawNativeCompletionLawOfAlignment alignment :=
    hother.trans hcanonical.symm
  cases hother'
  have hsurface :=
    (data.lawNativeCompletionLawOfAlignment alignment).completionBridgeSurface
  simp [TerminalExactificationLaw.lawNativeCompletionLawOfAlignment] at hsurface
  rcases hsurface with ⟨hsector, hassembly, _halignment⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hassembly] using data.lawNativeFourStateAssembly_toLocalEventStateBridge
  · simpa [hsector] using data.lawNativeConstructiveSectorLaw_canonicalGeneration
  · simpa [hsector] using
      data.lawNativeConstructiveSectorLaw_generatedFromIntrinsicChannelAlgebra
  · simpa [hsector] using
      data.lawNativeConstructiveSectorLaw_minimalCompatibleRealizationsOnly

/-- The same closed-completion principle already forces the smaller current-side
collapse target without invoking the proposition-level extracted-current
packaging. A unique aligned completion law must equal the completion law
reconstructed from the distinguished fixed-assembly candidate law, so both the
law-native constructive sector law and the law-native four-state assembly are
forced directly. -/
theorem canonicalLawNativeCompletionCollapseTargetOfCanonicalCompletionLawTarget_and_canonicalCompletionBoundaryLawFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalCompletionLawTarget ∧
        data.canonicalCompletionBoundaryLawFillTarget) :
    data.canonicalLawNativeCompletionCollapseTarget := by
  rcases htarget with ⟨hcompletionLaw, hboundaryFill⟩
  rcases hcompletionLaw with ⟨completionLaw, _hbridge₀, _hprinciple₀, hunique₀⟩
  rcases hboundaryFill with ⟨hboundaryLaw, _hboundaryAll⟩
  rcases hboundaryLaw with ⟨boundaryLaw, _huniqueBoundaryLaw⟩
  let alignment := boundaryLaw.alignment
  have hcanonical :
      data.lawNativeCompletionLawOfAlignment alignment = completionLaw :=
    hunique₀
      (data.lawNativeCompletionLawOfAlignment alignment)
      (data.lawNativeCompletionLawOfAlignment_sameBridge alignment)
      (data.lawNativeCompletionLawOfAlignment_samePhysicalPrinciple alignment)
  have hsectorCollapse :
      data.canonicalLawNativeSectorCollapseTarget := by
    intro other hbridge hprinciple
    have hother :
        other = completionLaw :=
      hunique₀ other hbridge hprinciple
    have hother' :
        other = data.lawNativeCompletionLawOfAlignment alignment :=
      hother.trans hcanonical.symm
    cases hother'
    exact lawNativeCompletionLawOfAlignment_sector data alignment
  have hassemblyFill :
      data.canonicalLawNativeAssemblyFillTarget := by
    intro other hbridge hprinciple hsector
    have hother :
        other = completionLaw :=
      hunique₀ other hbridge hprinciple
    have hother' :
        other = data.lawNativeCompletionLawOfAlignment alignment :=
      hother.trans hcanonical.symm
    cases hother'
    cases hsector
    exact lawNativeCompletionLawOfAlignment_assembly data alignment
  exact
    data.canonicalLawNativeCompletionCollapseTargetOfCanonicalLawNativeSectorCollapseTarget_and_canonicalLawNativeAssemblyFillTarget
      ⟨hsectorCollapse, hassemblyFill⟩

/-- So the exact remaining bottleneck already follows from a cleaner closed
completion principle: one unique no-stage completion law on the law-native
bridge and physical principle, together with the fixed-assembly boundary-law
fill theorem. -/
theorem canonicalSelectedCompletionTargetOfCanonicalCompletionLawTarget_and_canonicalCompletionBoundaryLawFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalCompletionLawTarget ∧
        data.canonicalCompletionBoundaryLawFillTarget) :
    data.canonicalSelectedCompletionTarget := by
  exact
    ⟨data.canonicalLawNativeCompletionCollapseTargetOfCanonicalCompletionLawTarget_and_canonicalCompletionBoundaryLawFillTarget
        htarget,
      htarget.2⟩

/-- The fixed-assembly alignment theorem is already enough to supply the
boundary-fill half of the same closed-completion principle. Therefore one
unique completion law together with one unique law-native alignment already
forces the exact canonical selected completion target. -/
theorem canonicalSelectedCompletionTargetOfCanonicalCompletionLawTarget_and_canonicalLawNativeAlignmentBoundaryTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalCompletionLawTarget ∧
        data.canonicalLawNativeAlignmentBoundaryTarget) :
    data.canonicalSelectedCompletionTarget := by
  rcases htarget with ⟨hcompletionLaw, halignment⟩
  have hboundaryFill :
      data.canonicalCompletionBoundaryLawFillTarget :=
    (data.canonicalCompletionBoundaryLawFillTarget_iff_canonicalLawNativeAlignmentBoundaryTarget).2
      halignment
  exact
    data.canonicalSelectedCompletionTargetOfCanonicalCompletionLawTarget_and_canonicalCompletionBoundaryLawFillTarget
      ⟨hcompletionLaw, hboundaryFill⟩

/-- Public endpoint-terminality language is already sufficient for the same
closed-completion consequence. One unique completion law together with
selected-cut endpoint terminality forces canonical selected completion. -/
theorem canonicalSelectedCompletionTargetOfCanonicalCompletionLawTarget_and_selectedCutEndpointTerminalityTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalCompletionLawTarget ∧
        data.selectedCutEndpointTerminalityTarget) :
    data.canonicalSelectedCompletionTarget := by
  rcases htarget with ⟨hcompletionLaw, hterminality⟩
  exact
    data.canonicalSelectedCompletionTargetOfCanonicalCompletionLawTarget_and_canonicalLawNativeAlignmentBoundaryTarget
      ⟨hcompletionLaw,
        (data.selectedCutEndpointTerminalityTarget_iff_canonicalLawNativeAlignmentBoundaryTarget).1
          hterminality⟩

/-- Replacing the fixed-assembly alignment theorem by the equivalent lower-
level Step 4 boundary route does not change the same closed-completion
consequence. -/
theorem canonicalSelectedCompletionTargetOfCanonicalCompletionLawTarget_and_canonicalLawNativeStep4BoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalCompletionLawTarget ∧
        data.canonicalLawNativeStep4BoundaryRouteTarget) :
    data.canonicalSelectedCompletionTarget := by
  rcases htarget with ⟨hcompletionLaw, hstep4⟩
  exact
    data.canonicalSelectedCompletionTargetOfCanonicalCompletionLawTarget_and_canonicalLawNativeAlignmentBoundaryTarget
      ⟨hcompletionLaw,
        data.canonicalLawNativeAlignmentBoundaryTargetOfCanonicalLawNativeStep4BoundaryRouteTarget
          hstep4⟩

/-- The same closed-completion route is also available from the stronger
strong-microscopic packaging: if the public two-law surface already yields one
unique no-stage completion law on the law-native bridge and physical
principle, then the fixed-assembly boundary-law fill theorem closes the exact
canonical selected completion target. -/
theorem canonicalSelectedCompletionTargetOfCanonicalStrongMicroscopicLawCompletionLawTarget_and_canonicalCompletionBoundaryLawFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalStrongMicroscopicLawCompletionLawTarget ∧
        data.canonicalCompletionBoundaryLawFillTarget) :
    data.canonicalSelectedCompletionTarget := by
  rcases htarget with ⟨hcompletionLaw, hfill⟩
  exact
    data.canonicalSelectedCompletionTargetOfCanonicalCompletionLawTarget_and_canonicalCompletionBoundaryLawFillTarget
      ⟨hcompletionLaw.2, hfill⟩

/-- Literal object-level uniqueness form of the same candidate-law surface:
there is one unique boundary-form microscopic law object on the law-native
bridge and physical principle. This is weaker than the exact bottleneck
because it packages only the unique candidate law object itself, not the
universal boundary-fill clause on every aligned completion law. It is the
honest uniqueness corollary of the exact target. -/
def canonicalBoundaryMicroscopicLawObjectTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  ∃ boundaryLaw : BoundaryMicroscopicLaw Index Time Carrier Law,
    boundaryLaw.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
      boundaryLaw.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        law.physicalPrinciple ∧
      ∀ other : BoundaryMicroscopicLaw Index Time Carrier Law,
        other.completionLaw.fourStateLaw.framed.object.bridge = law.bridge →
          other.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple →
          other = boundaryLaw

/-- Exact object-level form of the current candidate-law bottleneck: one
unique boundary microscopic law object on the law-native bridge and physical
principle, together with automatic aggregate flagship boundary closure on every
aligned completion law. This is the same content as the completion-law-side
boundary-fill target, read through the literal candidate-law object rather
than only through its underlying completion law. -/
def canonicalBoundaryMicroscopicLawObjectFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  data.canonicalBoundaryMicroscopicLawObjectTarget ∧
    data.universalCompletionLawBoundaryFillTarget

/-- Sequential form of the same canonical witness bottleneck. It isolates the
two genuine uniqueness subproblems above the law-native microscopic law:
first, the no-stage completion witness itself must be unique; second, on that
same witness, the aggregate flagship endpoint-witness bundle must be unique. -/
def canonicalCompletionWitnessBundleTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  ∃ witness : NoStageCompletionWitness law,
    (∀ other : NoStageCompletionWitness law, other = witness) ∧
    ∃ endpointWitnesses : FlagshipEndpointWitnesses witness.completionLaw,
      ∀ other : FlagshipEndpointWitnesses witness.completionLaw,
        other = endpointWitnesses

/-- Frontier-bundle form of the same canonical witness bottleneck. It isolates
one unique law-native no-stage completion witness together with one unique
aggregate flagship frontier bundle on that same completion law. -/
def canonicalCompletionWitnessFrontierBundleTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  ∃ witness : NoStageCompletionWitness law,
    (∀ other : NoStageCompletionWitness law, other = witness) ∧
    ∃ frontiers : FlagshipFrontiers witness.completionLaw,
      ∀ other : FlagshipFrontiers witness.completionLaw,
        other = frontiers

/-- Canonical frontier-readout target on one fixed no-stage completion witness:
each flagship lane carries one unique frontier on that same completion law.
This is a smaller common readout surface than the full endpoint-witness data. -/
def CanonicalFrontierLaneReadoutTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (witness : NoStageCompletionWitness law) : Prop :=
  ∃ phase : PhaseFrontier witness.completionLaw,
    (∀ other : PhaseFrontier witness.completionLaw, other = phase) ∧
    ∃ wave : WaveFrontier witness.completionLaw,
      (∀ other : WaveFrontier witness.completionLaw, other = wave) ∧
      ∃ gauge : GaugeFrontier witness.completionLaw,
        (∀ other : GaugeFrontier witness.completionLaw, other = gauge) ∧
        ∃ geometric : GeometricFrontier witness.completionLaw,
          ∀ other : GeometricFrontier witness.completionLaw,
            other = geometric

/-- Further sequential form of the same canonical witness bottleneck. It
isolates one unique law-native no-stage completion witness together with one
unique frontier readout on each of the four flagship lanes of that same
completion law. -/
def canonicalCompletionWitnessFrontierTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  ∃ witness : NoStageCompletionWitness law,
    (∀ other : NoStageCompletionWitness law, other = witness) ∧
    CanonicalFrontierLaneReadoutTarget witness

/-- Canonical endpoint-readout target on one fixed no-stage completion witness:
each flagship lane carries one unique endpoint witness on that same completion
law. This is the lane-wise unpacking of a canonical aggregate endpoint bundle. -/
def CanonicalEndpointLaneReadoutTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (witness : NoStageCompletionWitness law) : Prop :=
  ∃ phase : PhaseEndpointWitness witness.completionLaw,
    (∀ other : PhaseEndpointWitness witness.completionLaw, other = phase) ∧
    ∃ wave : WaveEndpointWitness witness.completionLaw,
      (∀ other : WaveEndpointWitness witness.completionLaw, other = wave) ∧
      ∃ gauge : GaugeEndpointWitness witness.completionLaw,
        (∀ other : GaugeEndpointWitness witness.completionLaw, other = gauge) ∧
        ∃ geometric : GeometricEndpointWitness witness.completionLaw,
          ∀ other : GeometricEndpointWitness witness.completionLaw,
            other = geometric

/-- Further sequential form of the same canonical witness bottleneck. It
isolates one unique law-native no-stage completion witness together with one
unique endpoint readout on each of the four flagship lanes of that same
completion law. -/
def canonicalCompletionWitnessLaneTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
  ∃ witness : NoStageCompletionWitness law,
    (∀ other : NoStageCompletionWitness law, other = witness) ∧
    CanonicalEndpointLaneReadoutTarget witness

/-- Bridge-level refinement of the same law-native flagship witness target on
the public two-law surface. It keeps the split completion bridge explicit, and
asks that its own no-stage witness already carry the endpoint-witness bundle. -/
def flagshipWitnessBridgeTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  ∃ bridge : NoStageCompletionBridge Index Time Carrier Law,
    bridge.toMicroscopicClosureLaw =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw ∧
      EndpointWitnessTarget bridge.toNoStageCompletionWitness

/-- Single law-native flagship frontier-bridge target on the public two-law
surface. It is the current sharp single object still needed above the law-
native constructive microscopic law in order to recover the endpoint-complete
strong microscopic package. -/
def flagshipFrontierBridgeTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  ∃ bridge : NoStageCompletionBridge Index Time Carrier Law,
    bridge.toMicroscopicClosureLaw =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw ∧
      Nonempty (FlagshipFrontiers bridge.toLocalEventFourStateCompletionLaw)

/-- Single law-native flagship completion-bridge target on the public two-law
surface. It is the current sharp single object still needed above the law-
native constructive microscopic law in order to recover the endpoint-complete
strong microscopic package. -/
def flagshipCompletionBridgeTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) : Prop :=
  ∃ bridge : NoStageCompletionBridge Index Time Carrier Law,
    bridge.toMicroscopicClosureLaw =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw ∧
      FlagshipBoundaryTarget bridge.toNoStageCompletionWitness

/-- A law-native flagship witness bridge is stronger than the frontier-bridge
target: one exact endpoint-witness bundle on the bridge's own no-stage witness
already reassembles the four frontiers on that same selected bundle. -/
theorem flagshipWitnessTargetOfWitnessBridgeTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.flagshipWitnessBridgeTarget) :
    data.flagshipWitnessTarget := by
  rcases htarget with ⟨bridge, sameLaw, hendpoint⟩
  dsimp [TerminalExactificationLaw.flagshipWitnessTarget]
  have htarget' : FlagshipTarget bridge.toMicroscopicClosureLaw :=
    ⟨bridge.toNoStageCompletionWitness, hendpoint⟩
  exact sameLaw ▸ htarget'

/-- The canonical law-native flagship witness target is, in particular, an
existence-level flagship witness target on the same law-native microscopic
law. -/
theorem flagshipWitnessTargetOfCanonicalFlagshipWitnessTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalFlagshipWitnessTarget) :
    data.flagshipWitnessTarget := by
  rcases htarget with ⟨target, _hunique⟩
  rcases target with ⟨witness, endpointWitnesses⟩
  exact ⟨witness, ⟨endpointWitnesses⟩⟩

/-- The sequential uniqueness bottleneck already implies the single canonical
law-native flagship witness target. -/
theorem canonicalFlagshipWitnessTargetOfCanonicalCompletionWitnessBundleTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionWitnessBundleTarget) :
    data.canonicalFlagshipWitnessTarget := by
  rcases htarget with ⟨witness, hwitness, endpointWitnesses, hendpoint⟩
  refine ⟨⟨witness, endpointWitnesses⟩, ?_⟩
  intro other
  rcases other with ⟨otherWitness, otherEndpointWitnesses⟩
  have hsameWitness : otherWitness = witness := hwitness otherWitness
  cases hsameWitness
  have hsameEndpoint : otherEndpointWitnesses = endpointWitnesses :=
    hendpoint otherEndpointWitnesses
  cases hsameEndpoint
  rfl

/-- The converse upgrade from the unique flagship witness package to the
sequential canonical-completion bottleneck needs one additional law-native fill
principle: every no-stage completion witness on the same microscopic law must
already carry some frontier bundle on its own completion law. Once that fill
surface is available, uniqueness of one flagship witness package upgrades to
the exact unique completion-witness / frontier-bundle target. -/
theorem canonicalCompletionWitnessFrontierBundleTargetOfCanonicalFlagshipWitnessTargetAndUniversalFrontierFill
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalFlagshipWitnessTarget)
    (hfill :
      ∀ witness :
        NoStageCompletionWitness
          data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw,
        Nonempty (FlagshipFrontiers witness.completionLaw)) :
    data.canonicalCompletionWitnessFrontierBundleTarget := by
  rcases htarget with ⟨⟨witness, endpointWitnesses⟩, hunique⟩
  refine ⟨witness, ?_, endpointWitnesses.toFrontiers, ?_⟩
  · intro otherWitness
    rcases hfill otherWitness with ⟨otherFrontiers⟩
    have hpack :
        ((⟨otherWitness, otherFrontiers.toEndpointWitnesses⟩ :
          FlagshipWitnessPackage
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw)) =
          ⟨witness, endpointWitnesses⟩ :=
      hunique ⟨otherWitness, otherFrontiers.toEndpointWitnesses⟩
    exact congrArg Sigma.fst hpack
  · intro otherFrontiers
    have hpack :
        ((⟨witness, otherFrontiers.toEndpointWitnesses⟩ :
          FlagshipWitnessPackage
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw)) =
          ⟨witness, endpointWitnesses⟩ :=
      hunique ⟨witness, otherFrontiers.toEndpointWitnesses⟩
    have hsameEndpoint : otherFrontiers.toEndpointWitnesses = endpointWitnesses := by
      cases hpack
      rfl
    have hsameFrontiers :
        otherFrontiers.toEndpointWitnesses.toFrontiers =
          endpointWitnesses.toFrontiers :=
      congrArg FlagshipEndpointWitnesses.toFrontiers hsameEndpoint
    simpa using
      (FlagshipFrontiers.toEndpointWitnesses_toFrontiers otherFrontiers).trans
        hsameFrontiers

/-- The same universal frontier-fill surface upgrades the unique flagship
witness package directly to the sequential endpoint-bundle bottleneck. -/
theorem canonicalCompletionWitnessBundleTargetOfCanonicalFlagshipWitnessTargetAndUniversalFrontierFill
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalFlagshipWitnessTarget)
    (hfill :
      ∀ witness :
        NoStageCompletionWitness
          data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw,
        Nonempty (FlagshipFrontiers witness.completionLaw)) :
    data.canonicalCompletionWitnessBundleTarget := by
  have hfrontier :
      data.canonicalCompletionWitnessFrontierBundleTarget :=
    data.canonicalCompletionWitnessFrontierBundleTargetOfCanonicalFlagshipWitnessTargetAndUniversalFrontierFill
      htarget hfill
  rcases hfrontier with ⟨witness, hwitness, frontiers, hfrontiers⟩
  refine ⟨witness, hwitness, frontiers.toEndpointWitnesses, ?_⟩
  intro other
  have hsameFrontiers : other.toFrontiers = frontiers :=
    hfrontiers other.toFrontiers
  have hsameEndpoints :
      other.toFrontiers.toEndpointWitnesses =
        frontiers.toEndpointWitnesses :=
    congrArg FlagshipFrontiers.toEndpointWitnesses hsameFrontiers
  simpa using
    (FlagshipEndpointWitnesses.toFrontiers_toEndpointWitnesses other).trans
      hsameEndpoints

/-- One unique aggregate frontier bundle on one unique law-native no-stage
completion witness automatically fills every other no-stage completion witness:
witness uniqueness transports the same frontier bundle across the entire
law-native completion class. -/
theorem universalFlagshipFrontierFillTargetOfCanonicalCompletionWitnessFrontierBundleTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionWitnessFrontierBundleTarget) :
    data.universalFlagshipFrontierFillTarget := by
  rcases htarget with ⟨witness, hwitness, frontiers, _hfrontiers⟩
  dsimp [TerminalExactificationLaw.universalFlagshipFrontierFillTarget]
  intro other
  have hsame : other = witness := hwitness other
  cases hsame
  exact ⟨frontiers⟩

/-- Universal law-native frontier fill is exactly the same as universal
law-native boundary fill: on each no-stage completion witness, carrying some
aggregate frontier bundle is equivalent to meeting the aggregate boundary
target. -/
theorem universalFlagshipBoundaryFillTarget_iff_universalFlagshipFrontierFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.universalFlagshipBoundaryFillTarget ↔
      data.universalFlagshipFrontierFillTarget := by
  constructor
  · intro htarget
    dsimp [TerminalExactificationLaw.universalFlagshipBoundaryFillTarget,
      TerminalExactificationLaw.universalFlagshipFrontierFillTarget] at *
    intro witness
    exact
      (witness.flagshipBoundaryTarget_iff_nonempty_frontiers).1
        (htarget witness)
  · intro htarget
    dsimp [TerminalExactificationLaw.universalFlagshipBoundaryFillTarget,
      TerminalExactificationLaw.universalFlagshipFrontierFillTarget] at *
    intro witness
    exact
      (witness.flagshipBoundaryTarget_iff_nonempty_frontiers).2
        (htarget witness)

/-- Universal law-native boundary fill is exactly the same as universal
law-native endpoint-witness fill: on each no-stage completion witness, the
aggregate frontier-side boundary target is equivalent to carrying an aggregate
endpoint-witness package on that same completion law. -/
theorem universalFlagshipBoundaryFillTarget_iff_universalEndpointWitnessFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.universalFlagshipBoundaryFillTarget ↔
      data.universalEndpointWitnessFillTarget := by
  constructor
  · intro htarget
    dsimp [TerminalExactificationLaw.universalFlagshipBoundaryFillTarget,
      TerminalExactificationLaw.universalEndpointWitnessFillTarget] at *
    intro witness
    exact
      (witness.endpointWitnessTarget_iff_flagshipBoundaryTarget).2
        (htarget witness)
  · intro htarget
    dsimp [TerminalExactificationLaw.universalFlagshipBoundaryFillTarget,
      TerminalExactificationLaw.universalEndpointWitnessFillTarget] at *
    intro witness
    exact
      (witness.endpointWitnessTarget_iff_flagshipBoundaryTarget).1
        (htarget witness)

/-- Universal law-native endpoint-witness fill is exactly the same as
universal law-native strong microscopic extension: on each no-stage completion
witness, carrying an aggregate endpoint-witness package is equivalent to
extending that same completion law to an endpoint-complete strong microscopic
law. -/
theorem universalEndpointWitnessFillTarget_iff_universalStrongMicroscopicExtensionTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.universalEndpointWitnessFillTarget ↔
      data.universalStrongMicroscopicExtensionTarget := by
  constructor
  · intro htarget
    dsimp [TerminalExactificationLaw.universalEndpointWitnessFillTarget,
      TerminalExactificationLaw.universalStrongMicroscopicExtensionTarget] at *
    intro witness
    exact
      (witness.endpointWitnessTarget_iff_strongMicroscopicExtensionTarget).1
        (htarget witness)
  · intro htarget
    dsimp [TerminalExactificationLaw.universalEndpointWitnessFillTarget,
      TerminalExactificationLaw.universalStrongMicroscopicExtensionTarget] at *
    intro witness
    exact
      (witness.endpointWitnessTarget_iff_strongMicroscopicExtensionTarget).2
        (htarget witness)

/-- The exact canonical completion frontier-bundle target already packages the
two deeper ingredients separately: one unique flagship witness package and the
universal law-native frontier-fill surface on every completion witness. -/
theorem canonicalFlagshipWitnessFrontierFillTargetOfCanonicalCompletionWitnessFrontierBundleTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionWitnessFrontierBundleTarget) :
    data.canonicalFlagshipWitnessFrontierFillTarget := by
  rcases htarget with ⟨witness, hwitness, frontiers, hfrontiers⟩
  refine
    ⟨?_, ?_⟩
  · refine ⟨⟨witness, frontiers.toEndpointWitnesses⟩, ?_⟩
    intro other
    rcases other with ⟨otherWitness, otherEndpointWitnesses⟩
    have hsameWitness : otherWitness = witness := hwitness otherWitness
    cases hsameWitness
    have hsameFrontiers :
        otherEndpointWitnesses.toFrontiers = frontiers :=
      hfrontiers otherEndpointWitnesses.toFrontiers
    have hsameEndpoints :
        otherEndpointWitnesses.toFrontiers.toEndpointWitnesses =
          frontiers.toEndpointWitnesses :=
      congrArg FlagshipFrontiers.toEndpointWitnesses hsameFrontiers
    simpa using
      (FlagshipEndpointWitnesses.toFrontiers_toEndpointWitnesses
        otherEndpointWitnesses).trans
        hsameEndpoints
  · exact
      data.universalFlagshipFrontierFillTargetOfCanonicalCompletionWitnessFrontierBundleTarget
        ⟨witness, hwitness, frontiers, hfrontiers⟩

/-- Replacing universal frontier fill by universal boundary fill does not
change the exact two-part bottleneck. -/
theorem canonicalFlagshipWitnessBoundaryFillTarget_iff_canonicalFlagshipWitnessFrontierFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalFlagshipWitnessBoundaryFillTarget ↔
      data.canonicalFlagshipWitnessFrontierFillTarget := by
  constructor
  · intro htarget
    rcases htarget with ⟨hcanonical, hboundary⟩
    refine ⟨hcanonical, ?_⟩
    exact
      (data.universalFlagshipBoundaryFillTarget_iff_universalFlagshipFrontierFillTarget).1
        hboundary
  · intro htarget
    rcases htarget with ⟨hcanonical, hfrontier⟩
    refine ⟨hcanonical, ?_⟩
    exact
      (data.universalFlagshipBoundaryFillTarget_iff_universalFlagshipFrontierFillTarget).2
        hfrontier

/-- Conversely, the unique flagship witness package together with universal
law-native frontier fill is already exactly enough to recover the canonical
completion frontier-bundle target. -/
theorem canonicalCompletionWitnessFrontierBundleTargetOfCanonicalFlagshipWitnessFrontierFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalFlagshipWitnessFrontierFillTarget) :
    data.canonicalCompletionWitnessFrontierBundleTarget := by
  rcases htarget with ⟨hcanonical, hfill⟩
  exact
    data.canonicalCompletionWitnessFrontierBundleTargetOfCanonicalFlagshipWitnessTargetAndUniversalFrontierFill
      hcanonical
      hfill

/-- The unique flagship witness package together with universal law-native
boundary fill is already exactly enough to recover the canonical completion
frontier-bundle target. -/
theorem canonicalCompletionWitnessFrontierBundleTargetOfCanonicalFlagshipWitnessBoundaryFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalFlagshipWitnessBoundaryFillTarget) :
    data.canonicalCompletionWitnessFrontierBundleTarget := by
  exact
    data.canonicalCompletionWitnessFrontierBundleTargetOfCanonicalFlagshipWitnessFrontierFillTarget
      ((data.canonicalFlagshipWitnessBoundaryFillTarget_iff_canonicalFlagshipWitnessFrontierFillTarget).1
        htarget)

/-- Unique lane-wise endpoint readouts on one unique law-native no-stage
completion witness already force the unique aggregate flagship witness package.
-/
theorem canonicalCompletionWitnessBundleTargetOfCanonicalCompletionWitnessLaneTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionWitnessLaneTarget) :
    data.canonicalCompletionWitnessBundleTarget := by
  rcases htarget with ⟨witness, hwitness, hlanes⟩
  rcases hlanes with
    ⟨phase, hphase, wave, hwave, gauge, hgauge, geometric, hgeometric⟩
  refine
    ⟨witness, hwitness, ?_, ?_⟩
  · exact
      { phase := phase
        wave := wave
        gauge := gauge
        geometric := geometric }
  · intro other
    cases other with
    | mk otherPhase otherWave otherGauge otherGeometric =>
        have hsamePhase : otherPhase = phase := hphase otherPhase
        have hsameWave : otherWave = wave := hwave otherWave
        have hsameGauge : otherGauge = gauge := hgauge otherGauge
        have hsameGeometric : otherGeometric = geometric := hgeometric otherGeometric
        cases hsamePhase
        cases hsameWave
        cases hsameGauge
        cases hsameGeometric
        rfl

/-- The unique aggregate endpoint-witness bundle on one unique law-native
no-stage completion witness is equivalent data to a unique aggregate frontier
bundle on that same witness. -/
theorem canonicalCompletionWitnessFrontierBundleTargetOfCanonicalCompletionWitnessBundleTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionWitnessBundleTarget) :
    data.canonicalCompletionWitnessFrontierBundleTarget := by
  rcases htarget with ⟨witness, hwitness, endpointWitnesses, hendpoint⟩
  refine ⟨witness, hwitness, endpointWitnesses.toFrontiers, ?_⟩
  intro other
  have hsameEndpoint : other.toEndpointWitnesses = endpointWitnesses :=
    hendpoint other.toEndpointWitnesses
  have hsameFrontiers :
      other.toEndpointWitnesses.toFrontiers = endpointWitnesses.toFrontiers :=
    congrArg FlagshipEndpointWitnesses.toFrontiers hsameEndpoint
  simpa using
    (FlagshipFrontiers.toEndpointWitnesses_toFrontiers other).trans hsameFrontiers

/-- Unique lane-wise endpoint readouts on one unique law-native no-stage
completion witness already force the single canonical law-native flagship
witness target. -/
theorem canonicalFlagshipWitnessTargetOfCanonicalCompletionWitnessLaneTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionWitnessLaneTarget) :
    data.canonicalFlagshipWitnessTarget := by
  exact
    data.canonicalFlagshipWitnessTargetOfCanonicalCompletionWitnessBundleTarget
      (data.canonicalCompletionWitnessBundleTargetOfCanonicalCompletionWitnessLaneTarget
        htarget)

/-- A law-native flagship witness bridge is stronger than the frontier-bridge
target: one exact endpoint-witness bundle on the bridge's own no-stage witness
already reassembles the four frontiers on that same selected bundle. -/
theorem flagshipFrontierBridgeTargetOfWitnessBridgeTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.flagshipWitnessBridgeTarget) :
    data.flagshipFrontierBridgeTarget := by
  rcases htarget with ⟨bridge, sameLaw, hendpoint⟩
  rcases hendpoint with ⟨endpointWitnesses⟩
  exact ⟨bridge, sameLaw, ⟨endpointWitnesses.toFrontiers⟩⟩

/-- A law-native flagship frontier bridge is stronger than the single
completion-bridge target: the four actual frontiers on the bridge's own
selected bundle package into the aggregate flagship boundary target on the
same no-stage witness. -/
theorem flagshipCompletionBridgeTargetOfFrontierBridgeTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.flagshipFrontierBridgeTarget) :
    data.flagshipCompletionBridgeTarget := by
  rcases htarget with ⟨bridge, sameLaw, hfrontiers⟩
  rcases hfrontiers with ⟨frontiers⟩
  refine ⟨bridge, sameLaw, ?_⟩
  exact
    bridge.toNoStageCompletionWitness.flagshipBoundaryTargetOfFrontierTargets
      ⟨frontiers.phase⟩
      ⟨frontiers.wave⟩
      ⟨frontiers.gauge⟩
      ⟨frontiers.geometric⟩

/-- A law-native flagship witness bridge is stronger than the single
completion-bridge target: one exact endpoint-witness bundle on the bridge's
own no-stage witness already determines the aggregate flagship boundary target
on that same witness. -/
theorem flagshipCompletionBridgeTargetOfWitnessBridgeTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.flagshipWitnessBridgeTarget) :
    data.flagshipCompletionBridgeTarget := by
  exact
    data.flagshipCompletionBridgeTargetOfFrontierBridgeTarget
      (data.flagshipFrontierBridgeTargetOfWitnessBridgeTarget htarget)

/-- The fixed-assembly alignment theorem already yields one concrete
boundary-complete completion bridge on the law-native microscopic law. -/
theorem flagshipCompletionBridgeTargetOfCanonicalLawNativeAlignmentBoundaryTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeAlignmentBoundaryTarget) :
    data.flagshipCompletionBridgeTarget := by
  rcases htarget with ⟨alignment, _huniqueAlignment, hboundary⟩
  let bridge : NoStageCompletionBridge Index Time Carrier Law :=
    data.lawNativeFourStateAssembly.toNoStageCompletionBridge alignment
  refine ⟨bridge, rfl, ?_⟩
  simpa [bridge, TerminalExactificationLaw.lawNativeCompletionLawOfAlignment,
    NoStageCompletionBridge.toNoStageCompletionWitness,
    LocalEventFourStateCompletionLaw.toNoStageCompletionWitness] using hboundary

/-- The lower-level Step 4 boundary route already yields one concrete
boundary-complete completion bridge on the law-native microscopic law. -/
theorem flagshipCompletionBridgeTargetOfCanonicalLawNativeStep4BoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeStep4BoundaryRouteTarget) :
    data.flagshipCompletionBridgeTarget := by
  exact
    data.flagshipCompletionBridgeTargetOfCanonicalLawNativeAlignmentBoundaryTarget
      (data.canonicalLawNativeAlignmentBoundaryTargetOfCanonicalLawNativeStep4BoundaryRouteTarget
        htarget)

/-- Selected-cut endpoint terminality already yields one concrete
boundary-complete completion bridge on the law-native microscopic law. This is
the same bridge remembered by the fixed-assembly alignment theorem, stated in
the public endpoint-terminality language. -/
theorem flagshipCompletionBridgeTargetOfSelectedCutEndpointTerminalityTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.selectedCutEndpointTerminalityTarget) :
    data.flagshipCompletionBridgeTarget := by
  exact
    data.flagshipCompletionBridgeTargetOfCanonicalLawNativeAlignmentBoundaryTarget
      ((data.selectedCutEndpointTerminalityTarget_iff_canonicalLawNativeAlignmentBoundaryTarget).1
        htarget)

/-- The single law-native flagship completion-bridge target already recovers
the endpoint-complete strong microscopic package on the public two-law
surface. -/
theorem strongMicroscopicLawOfFlagshipCompletionBridgeTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.flagshipCompletionBridgeTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.toMicroscopicClosureLaw =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw := by
  rcases htarget with ⟨bridge, sameLaw, hboundary⟩
  rcases
      data.strongMicroscopicLawOfBridgeBoundaryTarget
        bridge sameLaw hboundary with
    ⟨strong, _hcompletion, hmicroscopic⟩
  exact ⟨strong, hmicroscopic⟩

/-- The stronger law-native flagship frontier bridge target already recovers
the endpoint-complete strong microscopic package on the public two-law
surface. -/
theorem strongMicroscopicLawOfFlagshipFrontierBridgeTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.flagshipFrontierBridgeTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.toMicroscopicClosureLaw =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw := by
  exact
    data.strongMicroscopicLawOfFlagshipCompletionBridgeTarget
      (data.flagshipCompletionBridgeTargetOfFrontierBridgeTarget htarget)

/-- The still stronger law-native flagship witness bridge target already
recovers the endpoint-complete strong microscopic package on the public two-law
surface. -/
theorem strongMicroscopicLawOfFlagshipWitnessTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.flagshipWitnessTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple := by
  have hsurface :=
    MicroscopicClosureLaw.flagshipWitnessSurface
      data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
      htarget
  rcases hsurface with
    ⟨witness, endpointWitnesses, hbridge, hprinciple, _hcompletion, _hphase,
      _hwave, _hgauge, _hgeometric⟩
  exact
    ⟨{ completionLaw := witness.completionLaw
       endpointWitnesses := endpointWitnesses },
      hbridge,
      hprinciple⟩

/-- The canonical law-native flagship witness target already recovers one
unique endpoint-complete strong microscopic package on the same bridge and
physical principle as the law-native microscopic law. -/
theorem strongMicroscopicLawOfCanonicalFlagshipWitnessTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalFlagshipWitnessTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      ∀ other : StrongMicroscopicLaw Index Time Carrier Law,
        other.completionLaw.fourStateLaw.framed.object.bridge =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge →
          other.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple →
          other = strong := by
  rcases htarget with ⟨target, hunique⟩
  rcases target with ⟨witness, endpointWitnesses⟩
  refine
    ⟨{ completionLaw := witness.completionLaw
       endpointWitnesses := endpointWitnesses },
      witness.sameBridge,
      witness.samePhysicalPrinciple,
      ?_⟩
  intro other hbridge hprinciple
  cases other with
  | mk otherCompletion otherEndpointWitnesses =>
      show
        ({ completionLaw := otherCompletion
           endpointWitnesses := otherEndpointWitnesses } :
          StrongMicroscopicLaw Index Time Carrier Law) =
        { completionLaw := witness.completionLaw
          endpointWitnesses := endpointWitnesses }
      let otherWitness :
          NoStageCompletionWitness
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw :=
        { completionLaw := otherCompletion
          sameBridge := hbridge
          samePhysicalPrinciple := hprinciple }
      have hpack :
          ((⟨otherWitness,
              otherEndpointWitnesses⟩ :
            FlagshipWitnessPackage
              data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw)) =
          ⟨witness, endpointWitnesses⟩ :=
        hunique ⟨otherWitness, otherEndpointWitnesses⟩
      have hwitness : otherWitness = witness := by
        exact congrArg Sigma.fst hpack
      have hcompletion : otherCompletion = witness.completionLaw := by
        simpa [otherWitness] using
          congrArg NoStageCompletionWitness.completionLaw hwitness
      cases hcompletion
      have hendpoint : otherEndpointWitnesses = endpointWitnesses := by
        cases hwitness
        injection hpack with hendpoint
      cases hendpoint
      rfl

/-- The unique flagship witness package already packages exactly as one unique
strong microscopic law on the same bridge and physical principle. -/
theorem canonicalStrongMicroscopicLawTargetOfCanonicalFlagshipWitnessTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalFlagshipWitnessTarget) :
    data.canonicalStrongMicroscopicLawTarget := by
  exact
    data.strongMicroscopicLawOfCanonicalFlagshipWitnessTarget
      htarget

/-- Conversely, one unique strong microscopic law on the same bridge and
physical principle already determines one unique flagship witness package on
the law-native microscopic law. -/
theorem canonicalFlagshipWitnessTargetOfCanonicalStrongMicroscopicLawTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalStrongMicroscopicLawTarget) :
    data.canonicalFlagshipWitnessTarget := by
  rcases htarget with ⟨strong, hbridge, hprinciple, hunique⟩
  let witness :
      NoStageCompletionWitness
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw :=
    { completionLaw := strong.completionLaw
      sameBridge := hbridge
      samePhysicalPrinciple := hprinciple }
  refine
    ⟨⟨witness, strong.endpointWitnesses⟩, ?_⟩
  intro other
  rcases other with ⟨otherWitness, otherEndpointWitnesses⟩
  cases otherWitness with
  | mk otherCompletion otherBridge otherPrinciple =>
      let otherStrong : StrongMicroscopicLaw Index Time Carrier Law :=
        { completionLaw := otherCompletion
          endpointWitnesses := otherEndpointWitnesses }
      have hsameStrong : otherStrong = strong :=
        hunique otherStrong otherBridge otherPrinciple
      dsimp [otherStrong, witness] at hsameStrong ⊢
      cases hsameStrong
      have hsameBridge : otherBridge = hbridge := Subsingleton.elim _ _
      have hsamePrinciple : otherPrinciple = hprinciple := Subsingleton.elim _ _
      cases hsameBridge
      cases hsamePrinciple
      rfl

/-- The unique flagship witness package is exactly the same data as one unique
strong microscopic law on the same bridge and physical principle. -/
theorem canonicalFlagshipWitnessTarget_iff_canonicalStrongMicroscopicLawTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalFlagshipWitnessTarget ↔
      data.canonicalStrongMicroscopicLawTarget := by
  constructor
  · exact data.canonicalStrongMicroscopicLawTargetOfCanonicalFlagshipWitnessTarget
  · exact data.canonicalFlagshipWitnessTargetOfCanonicalStrongMicroscopicLawTarget

/-- The sequential uniqueness bottleneck already recovers one unique
endpoint-complete strong microscopic package on the same bridge and physical
principle as the law-native microscopic law. -/
theorem strongMicroscopicLawOfCanonicalCompletionWitnessBundleTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionWitnessBundleTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      ∀ other : StrongMicroscopicLaw Index Time Carrier Law,
        other.completionLaw.fourStateLaw.framed.object.bridge =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge →
          other.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple →
          other = strong := by
  exact
    data.strongMicroscopicLawOfCanonicalFlagshipWitnessTarget
      (data.canonicalFlagshipWitnessTargetOfCanonicalCompletionWitnessBundleTarget
        htarget)

/-- Unique lane-wise endpoint readouts on one unique law-native no-stage
completion witness already recover one unique endpoint-complete strong
microscopic package on the same bridge and physical principle as the law-native
microscopic law. -/
theorem strongMicroscopicLawOfCanonicalCompletionWitnessLaneTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionWitnessLaneTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      ∀ other : StrongMicroscopicLaw Index Time Carrier Law,
        other.completionLaw.fourStateLaw.framed.object.bridge =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge →
          other.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple →
          other = strong := by
  exact
    data.strongMicroscopicLawOfCanonicalCompletionWitnessBundleTarget
      (data.canonicalCompletionWitnessBundleTargetOfCanonicalCompletionWitnessLaneTarget
        htarget)

/-- The still stronger law-native flagship witness bridge target already
recovers the endpoint-complete strong microscopic package on the public two-law
surface. -/
theorem strongMicroscopicLawOfFlagshipWitnessBridgeTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.flagshipWitnessBridgeTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.toMicroscopicClosureLaw =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw := by
  rcases htarget with ⟨bridge, sameLaw, hendpoint⟩
  rcases hendpoint with ⟨endpointWitnesses⟩
  refine
    ⟨{ completionLaw := bridge.toLocalEventFourStateCompletionLaw
       endpointWitnesses := endpointWitnesses },
      ?_⟩
  simpa using sameLaw

/-- The same single law-native flagship completion-bridge target already
recovers the strong microscopic package together with its analytic flagship
surface and exact physical equation field. -/
theorem strongMicroscopicLawSurfaceOfFlagshipCompletionBridgeTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.flagshipCompletionBridgeTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.toMicroscopicClosureLaw =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong := by
  rcases
      data.strongMicroscopicLawOfFlagshipCompletionBridgeTarget
        htarget with
    ⟨strong, hstrong⟩
  exact
    ⟨strong,
      hstrong,
      LocalEventFourStateFlagshipLaw.analyticSurface strong,
      LocalEventFourStateFlagshipLaw.physicalEquationSurface strong⟩

/-- The same stronger law-native flagship frontier bridge target already
recovers the strong microscopic package together with its analytic flagship
surface and exact physical equation field. -/
theorem strongMicroscopicLawSurfaceOfFlagshipFrontierBridgeTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.flagshipFrontierBridgeTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.toMicroscopicClosureLaw =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong := by
  exact
    data.strongMicroscopicLawSurfaceOfFlagshipCompletionBridgeTarget
      (data.flagshipCompletionBridgeTargetOfFrontierBridgeTarget htarget)

/-- The same strongest law-native flagship witness bridge target already
recovers the strong microscopic package together with its analytic flagship
surface and exact physical equation field. -/
theorem strongMicroscopicLawSurfaceOfFlagshipWitnessTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.flagshipWitnessTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong := by
  rcases
      data.strongMicroscopicLawOfFlagshipWitnessTarget
        htarget with
    ⟨strong, hbridge, hprinciple⟩
  exact
    ⟨strong,
      hbridge,
      hprinciple,
      LocalEventFourStateFlagshipLaw.analyticSurface strong,
      LocalEventFourStateFlagshipLaw.physicalEquationSurface strong⟩

/-- The canonical law-native flagship witness target already recovers one
unique endpoint-complete strong microscopic package together with its analytic
flagship surface and exact physical equation field. -/
theorem strongMicroscopicLawSurfaceOfCanonicalFlagshipWitnessTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalFlagshipWitnessTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong ∧
      ∀ other : StrongMicroscopicLaw Index Time Carrier Law,
        other.completionLaw.fourStateLaw.framed.object.bridge =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge →
          other.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple →
          other = strong := by
  rcases
      data.strongMicroscopicLawOfCanonicalFlagshipWitnessTarget
        htarget with
    ⟨strong, hbridge, hprinciple, hunique⟩
  exact
    ⟨strong,
      hbridge,
      hprinciple,
      LocalEventFourStateFlagshipLaw.analyticSurface strong,
      LocalEventFourStateFlagshipLaw.physicalEquationSurface strong,
      hunique⟩

/-- The same sequential uniqueness bottleneck already recovers one unique
endpoint-complete strong microscopic package together with its analytic
flagship surface and exact physical equation field. -/
theorem strongMicroscopicLawSurfaceOfCanonicalCompletionWitnessBundleTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionWitnessBundleTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong ∧
      ∀ other : StrongMicroscopicLaw Index Time Carrier Law,
        other.completionLaw.fourStateLaw.framed.object.bridge =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge →
          other.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple →
          other = strong := by
  exact
    data.strongMicroscopicLawSurfaceOfCanonicalFlagshipWitnessTarget
      (data.canonicalFlagshipWitnessTargetOfCanonicalCompletionWitnessBundleTarget
        htarget)

/-- The same unique lane-wise endpoint readouts on one unique law-native
no-stage completion witness already recover one unique endpoint-complete strong
microscopic package together with its analytic flagship surface and exact
physical equation field. -/
theorem strongMicroscopicLawSurfaceOfCanonicalCompletionWitnessLaneTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionWitnessLaneTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong ∧
      ∀ other : StrongMicroscopicLaw Index Time Carrier Law,
        other.completionLaw.fourStateLaw.framed.object.bridge =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge →
          other.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple →
          other = strong := by
  exact
    data.strongMicroscopicLawSurfaceOfCanonicalCompletionWitnessBundleTarget
      (data.canonicalCompletionWitnessBundleTargetOfCanonicalCompletionWitnessLaneTarget
        htarget)

/-- One unique aggregate frontier bundle on one unique law-native no-stage
completion witness already forces the unique frontier readout on each
individual flagship lane. -/
theorem canonicalCompletionWitnessFrontierTargetOfCanonicalCompletionWitnessFrontierBundleTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionWitnessFrontierBundleTarget) :
    data.canonicalCompletionWitnessFrontierTarget := by
  rcases htarget with ⟨witness, hwitness, frontiers, hfrontiers⟩
  refine ⟨witness, hwitness, ?_⟩
  refine
    ⟨frontiers.phase, ?_,
      frontiers.wave, ?_,
      frontiers.gauge, ?_,
      frontiers.geometric, ?_⟩
  · intro other
    let trial : FlagshipFrontiers witness.completionLaw :=
      { phase := other
        wave := frontiers.wave
        gauge := frontiers.gauge
        geometric := frontiers.geometric }
    have hsame : trial = frontiers := hfrontiers trial
    exact congrArg FlagshipFrontiers.phase hsame
  · intro other
    let trial : FlagshipFrontiers witness.completionLaw :=
      { phase := frontiers.phase
        wave := other
        gauge := frontiers.gauge
        geometric := frontiers.geometric }
    have hsame : trial = frontiers := hfrontiers trial
    exact congrArg FlagshipFrontiers.wave hsame
  · intro other
    let trial : FlagshipFrontiers witness.completionLaw :=
      { phase := frontiers.phase
        wave := frontiers.wave
        gauge := other
        geometric := frontiers.geometric }
    have hsame : trial = frontiers := hfrontiers trial
    exact congrArg FlagshipFrontiers.gauge hsame
  · intro other
    let trial : FlagshipFrontiers witness.completionLaw :=
      { phase := frontiers.phase
        wave := frontiers.wave
        gauge := frontiers.gauge
        geometric := other }
    have hsame : trial = frontiers := hfrontiers trial
    exact congrArg FlagshipFrontiers.geometric hsame

/-- Unique frontier readouts on one unique law-native no-stage completion
witness already force the unique lane-wise endpoint-witness target. The
frontier layer is smaller, but the witness packages are read off it
deterministically. -/
theorem canonicalCompletionWitnessLaneTargetOfCanonicalCompletionWitnessFrontierTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionWitnessFrontierTarget) :
    data.canonicalCompletionWitnessLaneTarget := by
  rcases htarget with ⟨witness, hwitness, hfrontiers⟩
  rcases hfrontiers with
    ⟨phase, hphase, wave, hwave, gauge, hgauge, geometric, hgeometric⟩
  refine ⟨witness, hwitness, ?_⟩
  refine
    ⟨phase.toEndpointWitness, ?_,
      wave.toEndpointWitness, ?_,
      gauge.toEndpointWitness, ?_,
      geometric.toEndpointWitness, ?_⟩
  · intro other
    have hsame : other.toFrontier = phase := hphase other.toFrontier
    simpa using congrArg PhaseFrontier.toEndpointWitness hsame
  · intro other
    have hsame : other.toFrontier = wave := hwave other.toFrontier
    simpa using congrArg WaveFrontier.toEndpointWitness hsame
  · intro other
    have hsame : other.toFrontier = gauge := hgauge other.toFrontier
    simpa using congrArg GaugeFrontier.toEndpointWitness hsame
  · intro other
    have hsame : other.toFrontier = geometric := hgeometric other.toFrontier
    simpa using congrArg GeometricFrontier.toEndpointWitness hsame

/-- Unique frontier readouts on one unique law-native no-stage completion
witness already force the unique aggregate endpoint-witness bundle. -/
theorem canonicalCompletionWitnessBundleTargetOfCanonicalCompletionWitnessFrontierTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionWitnessFrontierTarget) :
    data.canonicalCompletionWitnessBundleTarget := by
  exact
    data.canonicalCompletionWitnessBundleTargetOfCanonicalCompletionWitnessLaneTarget
      (data.canonicalCompletionWitnessLaneTargetOfCanonicalCompletionWitnessFrontierTarget
        htarget)

/-- The unique aggregate frontier bundle on one unique law-native no-stage
completion witness is therefore exactly equivalent to the unique aggregate
endpoint-witness bundle on that same witness. -/
theorem canonicalCompletionWitnessBundleTargetOfCanonicalCompletionWitnessFrontierBundleTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionWitnessFrontierBundleTarget) :
    data.canonicalCompletionWitnessBundleTarget := by
  exact
    data.canonicalCompletionWitnessBundleTargetOfCanonicalCompletionWitnessFrontierTarget
      (data.canonicalCompletionWitnessFrontierTargetOfCanonicalCompletionWitnessFrontierBundleTarget
        htarget)

/-- The two aggregate uniqueness formulations are interchangeable: the exact
endpoint-witness bundle and the coarser frontier bundle encode the same
canonical completion datum on one unique law-native no-stage witness. -/
theorem canonicalCompletionWitnessBundleTarget_iff_canonicalCompletionWitnessFrontierBundleTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalCompletionWitnessBundleTarget ↔
      data.canonicalCompletionWitnessFrontierBundleTarget := by
  constructor
  · exact
      data.canonicalCompletionWitnessFrontierBundleTargetOfCanonicalCompletionWitnessBundleTarget
  · exact
      data.canonicalCompletionWitnessBundleTargetOfCanonicalCompletionWitnessFrontierBundleTarget

/-- The exact canonical completion frontier-bundle bottleneck is equivalent to
the conjunction of the unique flagship witness package and universal law-native
frontier fill on every no-stage completion witness. -/
theorem canonicalCompletionWitnessFrontierBundleTarget_iff_canonicalFlagshipWitnessFrontierFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalCompletionWitnessFrontierBundleTarget ↔
      data.canonicalFlagshipWitnessFrontierFillTarget := by
  constructor
  · exact
      data.canonicalFlagshipWitnessFrontierFillTargetOfCanonicalCompletionWitnessFrontierBundleTarget
  · exact
      data.canonicalCompletionWitnessFrontierBundleTargetOfCanonicalFlagshipWitnessFrontierFillTarget

/-- The endpoint-bundle form of the exact canonical completion bottleneck is
equivalently the conjunction of the unique flagship witness package and the
universal law-native frontier-fill surface. -/
theorem canonicalCompletionWitnessBundleTarget_iff_canonicalFlagshipWitnessFrontierFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalCompletionWitnessBundleTarget ↔
      data.canonicalFlagshipWitnessFrontierFillTarget := by
  constructor
  · intro htarget
    exact
      data.canonicalFlagshipWitnessFrontierFillTargetOfCanonicalCompletionWitnessFrontierBundleTarget
        (data.canonicalCompletionWitnessFrontierBundleTargetOfCanonicalCompletionWitnessBundleTarget
          htarget)
  · intro htarget
    exact
      data.canonicalCompletionWitnessBundleTargetOfCanonicalCompletionWitnessFrontierBundleTarget
        (data.canonicalCompletionWitnessFrontierBundleTargetOfCanonicalFlagshipWitnessFrontierFillTarget
          htarget)

/-- The exact canonical completion frontier-bundle bottleneck is equivalently
the conjunction of the unique flagship witness package and universal law-native
boundary fill on every no-stage completion witness. -/
theorem canonicalCompletionWitnessFrontierBundleTarget_iff_canonicalFlagshipWitnessBoundaryFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalCompletionWitnessFrontierBundleTarget ↔
      data.canonicalFlagshipWitnessBoundaryFillTarget := by
  constructor
  · intro htarget
    exact
      (data.canonicalFlagshipWitnessBoundaryFillTarget_iff_canonicalFlagshipWitnessFrontierFillTarget).2
        (data.canonicalFlagshipWitnessFrontierFillTargetOfCanonicalCompletionWitnessFrontierBundleTarget
          htarget)
  · intro htarget
    exact
      data.canonicalCompletionWitnessFrontierBundleTargetOfCanonicalFlagshipWitnessBoundaryFillTarget
        htarget

/-- The endpoint-bundle form of the exact canonical completion bottleneck is
equivalently the conjunction of the unique flagship witness package and the
universal law-native boundary-fill surface. -/
theorem canonicalCompletionWitnessBundleTarget_iff_canonicalFlagshipWitnessBoundaryFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalCompletionWitnessBundleTarget ↔
      data.canonicalFlagshipWitnessBoundaryFillTarget := by
  constructor
  · intro htarget
    exact
      (data.canonicalFlagshipWitnessBoundaryFillTarget_iff_canonicalFlagshipWitnessFrontierFillTarget).2
        ((data.canonicalCompletionWitnessBundleTarget_iff_canonicalFlagshipWitnessFrontierFillTarget).1
          htarget)
  · intro htarget
    exact
      (data.canonicalCompletionWitnessBundleTarget_iff_canonicalFlagshipWitnessFrontierFillTarget).2
        ((data.canonicalFlagshipWitnessBoundaryFillTarget_iff_canonicalFlagshipWitnessFrontierFillTarget).1
          htarget)

/-- Replacing the unique flagship witness package by the equivalent unique
strong microscopic law does not change the exact boundary-form bottleneck. -/
theorem canonicalStrongMicroscopicLawBoundaryFillTarget_iff_canonicalFlagshipWitnessBoundaryFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalStrongMicroscopicLawBoundaryFillTarget ↔
      data.canonicalFlagshipWitnessBoundaryFillTarget := by
  constructor
  · intro htarget
    rcases htarget with ⟨hstrong, hboundary⟩
    refine ⟨?_, hboundary⟩
    exact
      (data.canonicalFlagshipWitnessTarget_iff_canonicalStrongMicroscopicLawTarget).2
        hstrong
  · intro htarget
    rcases htarget with ⟨hwitness, hboundary⟩
    refine ⟨?_, hboundary⟩
    exact
      (data.canonicalFlagshipWitnessTarget_iff_canonicalStrongMicroscopicLawTarget).1
        hwitness

/-- The exact canonical completion frontier-bundle bottleneck is equivalently
the conjunction of one unique strong microscopic law and universal
law-native boundary fill. -/
theorem canonicalCompletionWitnessFrontierBundleTarget_iff_canonicalStrongMicroscopicLawBoundaryFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalCompletionWitnessFrontierBundleTarget ↔
      data.canonicalStrongMicroscopicLawBoundaryFillTarget := by
  constructor
  · intro htarget
    exact
      (data.canonicalStrongMicroscopicLawBoundaryFillTarget_iff_canonicalFlagshipWitnessBoundaryFillTarget).2
        ((data.canonicalCompletionWitnessFrontierBundleTarget_iff_canonicalFlagshipWitnessBoundaryFillTarget).1
          htarget)
  · intro htarget
    exact
      (data.canonicalCompletionWitnessFrontierBundleTarget_iff_canonicalFlagshipWitnessBoundaryFillTarget).2
        ((data.canonicalStrongMicroscopicLawBoundaryFillTarget_iff_canonicalFlagshipWitnessBoundaryFillTarget).1
          htarget)

/-- The endpoint-bundle form of the exact canonical completion bottleneck is
equivalently the conjunction of one unique strong microscopic law and the
universal law-native boundary-fill surface. -/
theorem canonicalCompletionWitnessBundleTarget_iff_canonicalStrongMicroscopicLawBoundaryFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalCompletionWitnessBundleTarget ↔
      data.canonicalStrongMicroscopicLawBoundaryFillTarget := by
  constructor
  · intro htarget
    exact
      (data.canonicalStrongMicroscopicLawBoundaryFillTarget_iff_canonicalFlagshipWitnessBoundaryFillTarget).2
        ((data.canonicalCompletionWitnessBundleTarget_iff_canonicalFlagshipWitnessBoundaryFillTarget).1
          htarget)
  · intro htarget
    exact
      (data.canonicalCompletionWitnessBundleTarget_iff_canonicalFlagshipWitnessBoundaryFillTarget).2
        ((data.canonicalStrongMicroscopicLawBoundaryFillTarget_iff_canonicalFlagshipWitnessBoundaryFillTarget).1
          htarget)

/-- Replacing universal boundary fill by the equivalent universal
endpoint-witness fill does not change the exact strong-law bottleneck. -/
theorem canonicalStrongMicroscopicLawEndpointFillTarget_iff_canonicalStrongMicroscopicLawBoundaryFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalStrongMicroscopicLawEndpointFillTarget ↔
      data.canonicalStrongMicroscopicLawBoundaryFillTarget := by
  constructor
  · intro htarget
    rcases htarget with ⟨hstrong, hendpoint⟩
    refine ⟨hstrong, ?_⟩
    exact
      (data.universalFlagshipBoundaryFillTarget_iff_universalEndpointWitnessFillTarget).2
        hendpoint
  · intro htarget
    rcases htarget with ⟨hstrong, hboundary⟩
    refine ⟨hstrong, ?_⟩
    exact
      (data.universalFlagshipBoundaryFillTarget_iff_universalEndpointWitnessFillTarget).1
        hboundary

/-- The exact canonical completion frontier-bundle bottleneck is equivalently
the conjunction of one unique strong microscopic law and universal
law-native endpoint-witness fill. -/
theorem canonicalCompletionWitnessFrontierBundleTarget_iff_canonicalStrongMicroscopicLawEndpointFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalCompletionWitnessFrontierBundleTarget ↔
      data.canonicalStrongMicroscopicLawEndpointFillTarget := by
  constructor
  · intro htarget
    exact
      (data.canonicalStrongMicroscopicLawEndpointFillTarget_iff_canonicalStrongMicroscopicLawBoundaryFillTarget).2
        ((data.canonicalCompletionWitnessFrontierBundleTarget_iff_canonicalStrongMicroscopicLawBoundaryFillTarget).1
          htarget)
  · intro htarget
    exact
      (data.canonicalCompletionWitnessFrontierBundleTarget_iff_canonicalStrongMicroscopicLawBoundaryFillTarget).2
        ((data.canonicalStrongMicroscopicLawEndpointFillTarget_iff_canonicalStrongMicroscopicLawBoundaryFillTarget).1
          htarget)

/-- The endpoint-bundle form of the exact canonical completion bottleneck is
equivalently the conjunction of one unique strong microscopic law and the
universal law-native endpoint-witness fill surface. -/
theorem canonicalCompletionWitnessBundleTarget_iff_canonicalStrongMicroscopicLawEndpointFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalCompletionWitnessBundleTarget ↔
      data.canonicalStrongMicroscopicLawEndpointFillTarget := by
  constructor
  · intro htarget
    exact
      (data.canonicalStrongMicroscopicLawEndpointFillTarget_iff_canonicalStrongMicroscopicLawBoundaryFillTarget).2
        ((data.canonicalCompletionWitnessBundleTarget_iff_canonicalStrongMicroscopicLawBoundaryFillTarget).1
          htarget)
  · intro htarget
    exact
      (data.canonicalCompletionWitnessBundleTarget_iff_canonicalStrongMicroscopicLawBoundaryFillTarget).2
        ((data.canonicalStrongMicroscopicLawEndpointFillTarget_iff_canonicalStrongMicroscopicLawBoundaryFillTarget).1
          htarget)

/-- Replacing universal endpoint-witness fill by the equivalent universal
strong microscopic extension does not change the exact strong-law bottleneck.
-/
theorem canonicalStrongMicroscopicLawExtensionTarget_iff_canonicalStrongMicroscopicLawEndpointFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalStrongMicroscopicLawExtensionTarget ↔
      data.canonicalStrongMicroscopicLawEndpointFillTarget := by
  constructor
  · intro htarget
    rcases htarget with ⟨hstrong, hext⟩
    refine ⟨hstrong, ?_⟩
    exact
      (data.universalEndpointWitnessFillTarget_iff_universalStrongMicroscopicExtensionTarget).2
        hext
  · intro htarget
    rcases htarget with ⟨hstrong, hendpoint⟩
    refine ⟨hstrong, ?_⟩
    exact
      (data.universalEndpointWitnessFillTarget_iff_universalStrongMicroscopicExtensionTarget).1
        hendpoint

/-- The exact canonical completion frontier-bundle bottleneck is equivalently
the conjunction of one unique strong microscopic law and universal law-native
strong microscopic extension on every no-stage completion witness. -/
theorem canonicalCompletionWitnessFrontierBundleTarget_iff_canonicalStrongMicroscopicLawExtensionTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalCompletionWitnessFrontierBundleTarget ↔
      data.canonicalStrongMicroscopicLawExtensionTarget := by
  constructor
  · intro htarget
    exact
      (data.canonicalStrongMicroscopicLawExtensionTarget_iff_canonicalStrongMicroscopicLawEndpointFillTarget).2
        ((data.canonicalCompletionWitnessFrontierBundleTarget_iff_canonicalStrongMicroscopicLawEndpointFillTarget).1
          htarget)
  · intro htarget
    exact
      (data.canonicalCompletionWitnessFrontierBundleTarget_iff_canonicalStrongMicroscopicLawEndpointFillTarget).2
        ((data.canonicalStrongMicroscopicLawExtensionTarget_iff_canonicalStrongMicroscopicLawEndpointFillTarget).1
          htarget)

/-- The endpoint-bundle form of the exact canonical completion bottleneck is
equivalently the conjunction of one unique strong microscopic law and universal
law-native strong microscopic extension on every no-stage completion witness.
-/
theorem canonicalCompletionWitnessBundleTarget_iff_canonicalStrongMicroscopicLawExtensionTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalCompletionWitnessBundleTarget ↔
      data.canonicalStrongMicroscopicLawExtensionTarget := by
  constructor
  · intro htarget
    exact
      (data.canonicalStrongMicroscopicLawExtensionTarget_iff_canonicalStrongMicroscopicLawEndpointFillTarget).2
        ((data.canonicalCompletionWitnessBundleTarget_iff_canonicalStrongMicroscopicLawEndpointFillTarget).1
          htarget)
  · intro htarget
    exact
      (data.canonicalCompletionWitnessBundleTarget_iff_canonicalStrongMicroscopicLawEndpointFillTarget).2
        ((data.canonicalStrongMicroscopicLawExtensionTarget_iff_canonicalStrongMicroscopicLawEndpointFillTarget).1
          htarget)

/-- Replacing universal strong microscopic extension by the equivalent
universal completion-law collapse onto the unique strong law does not change
the exact strong-law bottleneck. -/
theorem canonicalStrongMicroscopicLawCompletionCollapseTarget_iff_canonicalStrongMicroscopicLawExtensionTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalStrongMicroscopicLawCompletionCollapseTarget ↔
      data.canonicalStrongMicroscopicLawExtensionTarget := by
  constructor
  · intro htarget
    rcases htarget with ⟨strong, hbridge, hprinciple, hunique, hcollapse⟩
    refine ⟨⟨strong, hbridge, hprinciple, hunique⟩, ?_⟩
    dsimp [TerminalExactificationLaw.universalStrongMicroscopicExtensionTarget]
    intro witness
    exact ⟨strong, (hcollapse witness).symm⟩
  · intro htarget
    rcases htarget with ⟨hstrong, hext⟩
    rcases hstrong with ⟨strong, hbridge, hprinciple, hunique⟩
    refine ⟨strong, hbridge, hprinciple, hunique, ?_⟩
    intro witness
    rcases hext witness with ⟨other, hcompletion⟩
    have hotherBridge :
        other.completionLaw.fourStateLaw.framed.object.bridge =
          data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge := by
      rw [hcompletion]
      exact witness.sameBridge
    have hotherPrinciple :
        other.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple := by
      rw [hcompletion]
      exact witness.samePhysicalPrinciple
    have hsame : other = strong := hunique other hotherBridge hotherPrinciple
    have hsameCompletion : strong.completionLaw = witness.completionLaw := by
      simpa [hsame] using hcompletion
    exact hsameCompletion.symm

/-- Replacing universal completion-law collapse by uniqueness of the
law-native no-stage completion witness does not change the exact strong-law
bottleneck. -/
theorem canonicalStrongMicroscopicLawCompletionWitnessTarget_iff_canonicalStrongMicroscopicLawCompletionCollapseTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalStrongMicroscopicLawCompletionWitnessTarget ↔
      data.canonicalStrongMicroscopicLawCompletionCollapseTarget := by
  constructor
  · intro htarget
    rcases htarget with ⟨hstrong, witness, huniqueWitness⟩
    rcases hstrong with ⟨strong, hbridge, hprinciple, huniqueStrong⟩
    refine ⟨strong, hbridge, hprinciple, huniqueStrong, ?_⟩
    intro other
    have hotherWitness : other = witness := huniqueWitness other
    have hotherCompletion :
        other.completionLaw = witness.completionLaw := by
      exact congrArg NoStageCompletionWitness.completionLaw hotherWitness
    let strongWitness :
        NoStageCompletionWitness
          data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw :=
      { completionLaw := strong.completionLaw
        sameBridge := hbridge
        samePhysicalPrinciple := hprinciple }
    have hstrongWitness : strongWitness = witness := huniqueWitness strongWitness
    have hstrongCompletion :
        strong.completionLaw = witness.completionLaw := by
      exact congrArg NoStageCompletionWitness.completionLaw hstrongWitness
    exact hotherCompletion.trans hstrongCompletion.symm
  · intro htarget
    rcases htarget with ⟨strong, hbridge, hprinciple, huniqueStrong, hcollapse⟩
    let witness :
        NoStageCompletionWitness
          data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw :=
      { completionLaw := strong.completionLaw
        sameBridge := hbridge
        samePhysicalPrinciple := hprinciple }
    refine ⟨⟨strong, hbridge, hprinciple, huniqueStrong⟩, witness, ?_⟩
    intro other
    exact
      NoStageCompletionWitness.eq_of_completionLaw_eq
        (by simpa [witness] using hcollapse other)

/-- Replacing uniqueness of the law-native no-stage completion witness by
uniqueness of the underlying no-stage completion law on the same selected
bridge and physical principle does not change the exact strong-law bottleneck.
-/
theorem canonicalStrongMicroscopicLawCompletionLawTarget_iff_canonicalStrongMicroscopicLawCompletionWitnessTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalStrongMicroscopicLawCompletionLawTarget ↔
      data.canonicalStrongMicroscopicLawCompletionWitnessTarget := by
  constructor
  · intro htarget
    rcases htarget with ⟨hstrong, completionLaw, hbridge, hprinciple, huniqueLaw⟩
    let witness :
        NoStageCompletionWitness
          data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw :=
      { completionLaw := completionLaw
        sameBridge := hbridge
        samePhysicalPrinciple := hprinciple }
    refine ⟨hstrong, witness, ?_⟩
    intro other
    have hcompletion : other.completionLaw = completionLaw :=
      huniqueLaw other.completionLaw other.sameBridge other.samePhysicalPrinciple
    exact NoStageCompletionWitness.eq_of_completionLaw_eq hcompletion
  · intro htarget
    rcases htarget with ⟨hstrong, witness, huniqueWitness⟩
    refine ⟨hstrong, witness.completionLaw, witness.sameBridge, witness.samePhysicalPrinciple, ?_⟩
    intro other hbridge hprinciple
    let otherWitness :
        NoStageCompletionWitness
          data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw :=
      { completionLaw := other
        sameBridge := hbridge
        samePhysicalPrinciple := hprinciple }
    have hwitness : otherWitness = witness := huniqueWitness otherWitness
    exact congrArg NoStageCompletionWitness.completionLaw hwitness

/-- Once the no-stage completion law itself is unique on the law-native
bridge/principle, uniqueness of the strong microscopic package is exactly the
same as uniqueness of the aggregate endpoint-witness bundle carried by that
completion law. -/
theorem canonicalCompletionLawEndpointBundleTarget_iff_canonicalStrongMicroscopicLawCompletionLawTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalCompletionLawEndpointBundleTarget ↔
      data.canonicalStrongMicroscopicLawCompletionLawTarget := by
  constructor
  · intro htarget
    rcases htarget with
      ⟨completionLaw, hbridge, hprinciple, huniqueLaw, endpointWitnesses,
        hendpoint⟩
    let strongLaw : StrongMicroscopicLaw Index Time Carrier Law :=
      { completionLaw := completionLaw
        endpointWitnesses := endpointWitnesses }
    refine ⟨?_, completionLaw, hbridge, hprinciple, huniqueLaw⟩
    refine ⟨strongLaw, ?_, ?_, ?_⟩
    · simpa [strongLaw]
    · simpa [strongLaw]
    intro other hotherBridge hotherPrinciple
    cases other with
    | mk otherCompletion otherEndpointWitnesses =>
        have hsameCompletion : otherCompletion = completionLaw :=
          huniqueLaw otherCompletion hotherBridge hotherPrinciple
        cases hsameCompletion
        have hsameEndpoint : otherEndpointWitnesses = endpointWitnesses :=
          hendpoint otherEndpointWitnesses
        cases hsameEndpoint
        rfl
  · intro htarget
    rcases htarget with
      ⟨⟨strong, hstrongBridge, hstrongPrinciple, huniqueStrong⟩,
        completionLaw, hbridge, hprinciple, huniqueLaw⟩
    cases strong with
    | mk strongCompletion strongEndpointWitnesses =>
        have hsameCompletion : strongCompletion = completionLaw :=
          huniqueLaw strongCompletion hstrongBridge hstrongPrinciple
        cases hsameCompletion
        refine
          ⟨completionLaw,
            hbridge,
            hprinciple,
            huniqueLaw,
            strongEndpointWitnesses,
            ?_⟩
        intro otherEndpointWitnesses
        have hsame :
            ({ completionLaw := completionLaw
               endpointWitnesses := otherEndpointWitnesses } :
              StrongMicroscopicLaw Index Time Carrier Law) =
              ({ completionLaw := completionLaw
                 endpointWitnesses := strongEndpointWitnesses } :
                StrongMicroscopicLaw Index Time Carrier Law) :=
          huniqueStrong
            { completionLaw := completionLaw
              endpointWitnesses := otherEndpointWitnesses }
            hbridge hprinciple
        cases hsame
        rfl

/-- The stronger endpoint-bundle bottleneck already yields the more honest
boundary-form candidate law target on the same unique completion law. -/
theorem canonicalBoundaryMicroscopicLawTargetOfCanonicalCompletionLawEndpointBundleTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionLawEndpointBundleTarget) :
    data.canonicalBoundaryMicroscopicLawTarget := by
  rcases htarget with
    ⟨completionLaw, hbridge, hprinciple, huniqueLaw, endpointWitnesses, _hendpoint⟩
  refine ⟨completionLaw, hbridge, hprinciple, huniqueLaw, ?_⟩
  exact
    completionLaw.toNoStageCompletionWitness.flagshipBoundaryTargetOfEndpointWitnessTarget
      ⟨endpointWitnesses⟩

/-- The exact canonical completion frontier-bundle bottleneck is equivalently
the conjunction of one unique strong microscopic law and universal completion-
law collapse onto that same strong law. -/
theorem canonicalCompletionWitnessFrontierBundleTarget_iff_canonicalStrongMicroscopicLawCompletionCollapseTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalCompletionWitnessFrontierBundleTarget ↔
      data.canonicalStrongMicroscopicLawCompletionCollapseTarget := by
  constructor
  · intro htarget
    exact
      (data.canonicalStrongMicroscopicLawCompletionCollapseTarget_iff_canonicalStrongMicroscopicLawExtensionTarget).2
        ((data.canonicalCompletionWitnessFrontierBundleTarget_iff_canonicalStrongMicroscopicLawExtensionTarget).1
          htarget)
  · intro htarget
    exact
      (data.canonicalCompletionWitnessFrontierBundleTarget_iff_canonicalStrongMicroscopicLawExtensionTarget).2
        ((data.canonicalStrongMicroscopicLawCompletionCollapseTarget_iff_canonicalStrongMicroscopicLawExtensionTarget).1
          htarget)

/-- The endpoint-bundle form of the exact canonical completion bottleneck is
equivalently the conjunction of one unique strong microscopic law and universal
completion-law collapse onto that same strong law. -/
theorem canonicalCompletionWitnessBundleTarget_iff_canonicalStrongMicroscopicLawCompletionCollapseTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalCompletionWitnessBundleTarget ↔
      data.canonicalStrongMicroscopicLawCompletionCollapseTarget := by
  constructor
  · intro htarget
    exact
      (data.canonicalStrongMicroscopicLawCompletionCollapseTarget_iff_canonicalStrongMicroscopicLawExtensionTarget).2
        ((data.canonicalCompletionWitnessBundleTarget_iff_canonicalStrongMicroscopicLawExtensionTarget).1
          htarget)
  · intro htarget
    exact
      (data.canonicalCompletionWitnessBundleTarget_iff_canonicalStrongMicroscopicLawExtensionTarget).2
        ((data.canonicalStrongMicroscopicLawCompletionCollapseTarget_iff_canonicalStrongMicroscopicLawExtensionTarget).1
          htarget)

/-- The exact canonical completion frontier-bundle bottleneck is equivalently
the conjunction of one unique strong microscopic law and one unique law-native
no-stage completion witness. -/
theorem canonicalCompletionWitnessFrontierBundleTarget_iff_canonicalStrongMicroscopicLawCompletionWitnessTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalCompletionWitnessFrontierBundleTarget ↔
      data.canonicalStrongMicroscopicLawCompletionWitnessTarget := by
  constructor
  · intro htarget
    exact
      (data.canonicalStrongMicroscopicLawCompletionWitnessTarget_iff_canonicalStrongMicroscopicLawCompletionCollapseTarget).2
        ((data.canonicalCompletionWitnessFrontierBundleTarget_iff_canonicalStrongMicroscopicLawCompletionCollapseTarget).1
          htarget)
  · intro htarget
    exact
      (data.canonicalCompletionWitnessFrontierBundleTarget_iff_canonicalStrongMicroscopicLawCompletionCollapseTarget).2
        ((data.canonicalStrongMicroscopicLawCompletionWitnessTarget_iff_canonicalStrongMicroscopicLawCompletionCollapseTarget).1
          htarget)

/-- The endpoint-bundle form of the exact canonical completion bottleneck is
equivalently the conjunction of one unique strong microscopic law and one
unique law-native no-stage completion witness. -/
theorem canonicalCompletionWitnessBundleTarget_iff_canonicalStrongMicroscopicLawCompletionWitnessTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalCompletionWitnessBundleTarget ↔
      data.canonicalStrongMicroscopicLawCompletionWitnessTarget := by
  constructor
  · intro htarget
    exact
      (data.canonicalStrongMicroscopicLawCompletionWitnessTarget_iff_canonicalStrongMicroscopicLawCompletionCollapseTarget).2
        ((data.canonicalCompletionWitnessBundleTarget_iff_canonicalStrongMicroscopicLawCompletionCollapseTarget).1
          htarget)
  · intro htarget
    exact
      (data.canonicalCompletionWitnessBundleTarget_iff_canonicalStrongMicroscopicLawCompletionCollapseTarget).2
        ((data.canonicalStrongMicroscopicLawCompletionWitnessTarget_iff_canonicalStrongMicroscopicLawCompletionCollapseTarget).1
          htarget)

/-- The exact canonical completion frontier-bundle bottleneck is equivalently
the conjunction of one unique strong microscopic law and one unique no-stage
completion law on the same selected bridge and physical principle. -/
theorem canonicalCompletionWitnessFrontierBundleTarget_iff_canonicalStrongMicroscopicLawCompletionLawTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalCompletionWitnessFrontierBundleTarget ↔
      data.canonicalStrongMicroscopicLawCompletionLawTarget := by
  constructor
  · intro htarget
    exact
      (data.canonicalStrongMicroscopicLawCompletionLawTarget_iff_canonicalStrongMicroscopicLawCompletionWitnessTarget).2
        ((data.canonicalCompletionWitnessFrontierBundleTarget_iff_canonicalStrongMicroscopicLawCompletionWitnessTarget).1
          htarget)
  · intro htarget
    exact
      (data.canonicalCompletionWitnessFrontierBundleTarget_iff_canonicalStrongMicroscopicLawCompletionWitnessTarget).2
        ((data.canonicalStrongMicroscopicLawCompletionLawTarget_iff_canonicalStrongMicroscopicLawCompletionWitnessTarget).1
          htarget)

/-- The endpoint-bundle form of the exact canonical completion bottleneck is
equivalently the conjunction of one unique strong microscopic law and one
unique no-stage completion law on the same selected bridge and physical
principle. -/
theorem canonicalCompletionWitnessBundleTarget_iff_canonicalStrongMicroscopicLawCompletionLawTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalCompletionWitnessBundleTarget ↔
      data.canonicalStrongMicroscopicLawCompletionLawTarget := by
  constructor
  · intro htarget
    exact
      (data.canonicalStrongMicroscopicLawCompletionLawTarget_iff_canonicalStrongMicroscopicLawCompletionWitnessTarget).2
        ((data.canonicalCompletionWitnessBundleTarget_iff_canonicalStrongMicroscopicLawCompletionWitnessTarget).1
          htarget)
  · intro htarget
    exact
      (data.canonicalCompletionWitnessBundleTarget_iff_canonicalStrongMicroscopicLawCompletionWitnessTarget).2
        ((data.canonicalStrongMicroscopicLawCompletionLawTarget_iff_canonicalStrongMicroscopicLawCompletionWitnessTarget).1
          htarget)

/-- Unique frontier readouts on one unique law-native no-stage completion
witness already force the canonical law-native flagship witness target. -/
theorem canonicalFlagshipWitnessTargetOfCanonicalCompletionWitnessFrontierTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionWitnessFrontierTarget) :
    data.canonicalFlagshipWitnessTarget := by
  exact
    data.canonicalFlagshipWitnessTargetOfCanonicalCompletionWitnessBundleTarget
      (data.canonicalCompletionWitnessBundleTargetOfCanonicalCompletionWitnessFrontierTarget
        htarget)

/-- Unique frontier readouts on one unique law-native no-stage completion
witness already recover one unique endpoint-complete strong microscopic
package on the same bridge and physical principle as the law-native
microscopic law. -/
theorem strongMicroscopicLawOfCanonicalCompletionWitnessFrontierTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionWitnessFrontierTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      ∀ other : StrongMicroscopicLaw Index Time Carrier Law,
        other.completionLaw.fourStateLaw.framed.object.bridge =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge →
          other.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple →
          other = strong := by
  exact
    data.strongMicroscopicLawOfCanonicalCompletionWitnessLaneTarget
      (data.canonicalCompletionWitnessLaneTargetOfCanonicalCompletionWitnessFrontierTarget
        htarget)

/-- Unique frontier readouts on one unique law-native no-stage completion
witness already recover one unique endpoint-complete strong microscopic
package together with its analytic flagship surface and exact physical
equation field. -/
theorem strongMicroscopicLawSurfaceOfCanonicalCompletionWitnessFrontierTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionWitnessFrontierTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong ∧
      ∀ other : StrongMicroscopicLaw Index Time Carrier Law,
        other.completionLaw.fourStateLaw.framed.object.bridge =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge →
          other.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple →
          other = strong := by
  exact
    data.strongMicroscopicLawSurfaceOfCanonicalCompletionWitnessLaneTarget
      (data.canonicalCompletionWitnessLaneTargetOfCanonicalCompletionWitnessFrontierTarget
        htarget)

/-- One unique aggregate frontier bundle on one unique law-native no-stage
completion witness already forces the canonical law-native flagship witness
target. -/
theorem canonicalFlagshipWitnessTargetOfCanonicalCompletionWitnessFrontierBundleTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionWitnessFrontierBundleTarget) :
    data.canonicalFlagshipWitnessTarget := by
  exact
    data.canonicalFlagshipWitnessTargetOfCanonicalCompletionWitnessFrontierTarget
      (data.canonicalCompletionWitnessFrontierTargetOfCanonicalCompletionWitnessFrontierBundleTarget
        htarget)

/-- One unique aggregate frontier bundle on one unique law-native no-stage
completion witness already recovers one unique endpoint-complete strong
microscopic package on the same bridge and physical principle as the law-native
microscopic law. -/
theorem strongMicroscopicLawOfCanonicalCompletionWitnessFrontierBundleTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionWitnessFrontierBundleTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      ∀ other : StrongMicroscopicLaw Index Time Carrier Law,
        other.completionLaw.fourStateLaw.framed.object.bridge =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge →
          other.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple →
          other = strong := by
  exact
    data.strongMicroscopicLawOfCanonicalCompletionWitnessFrontierTarget
      (data.canonicalCompletionWitnessFrontierTargetOfCanonicalCompletionWitnessFrontierBundleTarget
        htarget)

/-- One unique aggregate frontier bundle on one unique law-native no-stage
completion witness already recovers one unique endpoint-complete strong
microscopic package together with its analytic flagship surface and exact
physical equation field. -/
theorem strongMicroscopicLawSurfaceOfCanonicalCompletionWitnessFrontierBundleTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionWitnessFrontierBundleTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong ∧
      ∀ other : StrongMicroscopicLaw Index Time Carrier Law,
        other.completionLaw.fourStateLaw.framed.object.bridge =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge →
          other.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple →
          other = strong := by
  exact
    data.strongMicroscopicLawSurfaceOfCanonicalCompletionWitnessFrontierTarget
      (data.canonicalCompletionWitnessFrontierTargetOfCanonicalCompletionWitnessFrontierBundleTarget
        htarget)

/-- So once every law-native no-stage completion witness is frontier-fillable
on its own completion law, the unique flagship witness package already closes
the exact canonical completion bottleneck and recovers the unique strong
microscopic package with its analytic and equation surfaces. -/
theorem strongMicroscopicLawSurfaceOfCanonicalFlagshipWitnessTargetAndUniversalFrontierFill
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalFlagshipWitnessTarget)
    (hfill :
      ∀ witness :
        NoStageCompletionWitness
          data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw,
        Nonempty (FlagshipFrontiers witness.completionLaw)) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong ∧
      ∀ other : StrongMicroscopicLaw Index Time Carrier Law,
        other.completionLaw.fourStateLaw.framed.object.bridge =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge →
          other.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple →
          other = strong := by
  exact
    data.strongMicroscopicLawSurfaceOfCanonicalCompletionWitnessFrontierBundleTarget
      (data.canonicalCompletionWitnessFrontierBundleTargetOfCanonicalFlagshipWitnessTargetAndUniversalFrontierFill
        htarget hfill)

/-- So the exact two-part bottleneck already recovers the unique strong
microscopic package together with its analytic flagship surface and exact
physical equation field. -/
theorem strongMicroscopicLawSurfaceOfCanonicalFlagshipWitnessFrontierFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalFlagshipWitnessFrontierFillTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong ∧
      ∀ other : StrongMicroscopicLaw Index Time Carrier Law,
        other.completionLaw.fourStateLaw.framed.object.bridge =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge →
          other.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple →
          other = strong := by
  exact
    data.strongMicroscopicLawSurfaceOfCanonicalCompletionWitnessFrontierBundleTarget
      (data.canonicalCompletionWitnessFrontierBundleTargetOfCanonicalFlagshipWitnessFrontierFillTarget
        htarget)

/-- Replacing universal frontier fill by universal boundary fill does not
change the final strong-law consequence of the exact two-part bottleneck. -/
theorem strongMicroscopicLawSurfaceOfCanonicalFlagshipWitnessBoundaryFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalFlagshipWitnessBoundaryFillTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong ∧
      ∀ other : StrongMicroscopicLaw Index Time Carrier Law,
        other.completionLaw.fourStateLaw.framed.object.bridge =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge →
          other.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple →
          other = strong := by
  exact
    data.strongMicroscopicLawSurfaceOfCanonicalFlagshipWitnessFrontierFillTarget
      ((data.canonicalFlagshipWitnessBoundaryFillTarget_iff_canonicalFlagshipWitnessFrontierFillTarget).1
        htarget)

/-- The same exact boundary-form bottleneck can be read directly through the
unique strong microscopic law surface. Once one unique strong microscopic law
exists on the same bridge and physical principle and the completion class is
universally boundary-filled, the analytic flagship surface and exact physical
equation field already follow. -/
theorem strongMicroscopicLawSurfaceOfCanonicalStrongMicroscopicLawBoundaryFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalStrongMicroscopicLawBoundaryFillTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong ∧
      ∀ other : StrongMicroscopicLaw Index Time Carrier Law,
        other.completionLaw.fourStateLaw.framed.object.bridge =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge →
          other.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple →
          other = strong := by
  exact
    data.strongMicroscopicLawSurfaceOfCanonicalFlagshipWitnessBoundaryFillTarget
      ((data.canonicalStrongMicroscopicLawBoundaryFillTarget_iff_canonicalFlagshipWitnessBoundaryFillTarget).1
        htarget)

/-- The equivalent endpoint-witness form of the exact canonical completion
bottleneck already recovers one unique strong microscopic package together with
its analytic flagship surface and exact physical equation field. -/
theorem strongMicroscopicLawSurfaceOfCanonicalStrongMicroscopicLawEndpointFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalStrongMicroscopicLawEndpointFillTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong ∧
      ∀ other : StrongMicroscopicLaw Index Time Carrier Law,
        other.completionLaw.fourStateLaw.framed.object.bridge =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge →
          other.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple →
          other = strong := by
  exact
    data.strongMicroscopicLawSurfaceOfCanonicalStrongMicroscopicLawBoundaryFillTarget
      ((data.canonicalStrongMicroscopicLawEndpointFillTarget_iff_canonicalStrongMicroscopicLawBoundaryFillTarget).1
        htarget)

/-- The equivalent strong-extension form of the exact canonical completion
bottleneck already recovers one unique strong microscopic package together with
its analytic flagship surface and exact physical equation field. -/
theorem strongMicroscopicLawSurfaceOfCanonicalStrongMicroscopicLawExtensionTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalStrongMicroscopicLawExtensionTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong ∧
      ∀ other : StrongMicroscopicLaw Index Time Carrier Law,
        other.completionLaw.fourStateLaw.framed.object.bridge =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge →
          other.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple →
          other = strong := by
  exact
    data.strongMicroscopicLawSurfaceOfCanonicalStrongMicroscopicLawEndpointFillTarget
      ((data.canonicalStrongMicroscopicLawExtensionTarget_iff_canonicalStrongMicroscopicLawEndpointFillTarget).1
        htarget)

/-- The equivalent completion-collapse form of the exact canonical completion
bottleneck already recovers one unique strong microscopic package together
with its analytic flagship surface and exact physical equation field. -/
theorem strongMicroscopicLawSurfaceOfCanonicalStrongMicroscopicLawCompletionCollapseTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalStrongMicroscopicLawCompletionCollapseTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong ∧
      ∀ other : StrongMicroscopicLaw Index Time Carrier Law,
        other.completionLaw.fourStateLaw.framed.object.bridge =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge →
          other.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple →
          other = strong := by
  exact
    data.strongMicroscopicLawSurfaceOfCanonicalStrongMicroscopicLawExtensionTarget
      ((data.canonicalStrongMicroscopicLawCompletionCollapseTarget_iff_canonicalStrongMicroscopicLawExtensionTarget).1
        htarget)

/-- The equivalent unique-completion-witness form of the exact canonical
completion bottleneck already recovers one unique strong microscopic package
together with its analytic flagship surface and exact physical equation field.
-/
theorem strongMicroscopicLawSurfaceOfCanonicalStrongMicroscopicLawCompletionWitnessTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalStrongMicroscopicLawCompletionWitnessTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong ∧
      ∀ other : StrongMicroscopicLaw Index Time Carrier Law,
        other.completionLaw.fourStateLaw.framed.object.bridge =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge →
          other.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple →
          other = strong := by
  exact
    data.strongMicroscopicLawSurfaceOfCanonicalStrongMicroscopicLawCompletionCollapseTarget
      ((data.canonicalStrongMicroscopicLawCompletionWitnessTarget_iff_canonicalStrongMicroscopicLawCompletionCollapseTarget).1
        htarget)

/-- The equivalent unique-completion-law form of the exact canonical
completion bottleneck already recovers one unique strong microscopic package
together with its analytic flagship surface and exact physical equation field.
-/
theorem strongMicroscopicLawSurfaceOfCanonicalStrongMicroscopicLawCompletionLawTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalStrongMicroscopicLawCompletionLawTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong ∧
      ∀ other : StrongMicroscopicLaw Index Time Carrier Law,
        other.completionLaw.fourStateLaw.framed.object.bridge =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge →
          other.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple →
          other = strong := by
  exact
    data.strongMicroscopicLawSurfaceOfCanonicalStrongMicroscopicLawCompletionWitnessTarget
      ((data.canonicalStrongMicroscopicLawCompletionLawTarget_iff_canonicalStrongMicroscopicLawCompletionWitnessTarget).1
        htarget)

/-- The equivalent unique-completion-law / endpoint-bundle form of the exact
canonical completion bottleneck already recovers one unique strong microscopic
package together with its analytic flagship surface and exact physical
equation field. -/
theorem strongMicroscopicLawSurfaceOfCanonicalCompletionLawEndpointBundleTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionLawEndpointBundleTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong ∧
      ∀ other : StrongMicroscopicLaw Index Time Carrier Law,
        other.completionLaw.fourStateLaw.framed.object.bridge =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge →
          other.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple →
          other = strong := by
  exact
    data.strongMicroscopicLawSurfaceOfCanonicalStrongMicroscopicLawCompletionLawTarget
      ((data.canonicalCompletionLawEndpointBundleTarget_iff_canonicalStrongMicroscopicLawCompletionLawTarget).1
        htarget)

/-- The stronger endpoint-bundle bottleneck therefore already yields the more
honest boundary-form candidate law target. -/
theorem canonicalBoundaryMicroscopicLawTargetOfCanonicalStrongMicroscopicLawCompletionLawTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalStrongMicroscopicLawCompletionLawTarget) :
    data.canonicalBoundaryMicroscopicLawTarget := by
  exact
    data.canonicalBoundaryMicroscopicLawTargetOfCanonicalCompletionLawEndpointBundleTarget
      ((data.canonicalCompletionLawEndpointBundleTarget_iff_canonicalStrongMicroscopicLawCompletionLawTarget).2
        htarget)

/-- One unique no-stage completion law on the law-native bridge and physical
principle, together with one endpoint-complete flagship witness on that same
microscopic law, already yields the honest boundary-form candidate law target.
The flagship witness itself need not be unique: completion-law uniqueness
transports its boundary closure onto the unique completion law. -/
theorem canonicalBoundaryMicroscopicLawTargetOfCanonicalCompletionLawTarget_and_flagshipWitnessTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalCompletionLawTarget ∧
        data.flagshipWitnessTarget) :
    data.canonicalBoundaryMicroscopicLawTarget := by
  rcases htarget with ⟨hcompletionLaw, hflagship⟩
  rcases hcompletionLaw with ⟨completionLaw, hbridge₀, hprinciple₀, huniqueLaw⟩
  have hsurface :=
    MicroscopicClosureLaw.flagshipWitnessSurface
      data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
      hflagship
  rcases hsurface with
    ⟨witness, endpointWitnesses, hbridge, hprinciple, _hcompletion,
      _hphase, _hwave, _hgauge, _hgeometric⟩
  have hsameCompletion : witness.completionLaw = completionLaw :=
    huniqueLaw witness.completionLaw hbridge hprinciple
  have hboundary :
      FlagshipBoundaryTarget completionLaw.toNoStageCompletionWitness := by
    cases hsameCompletion
    exact
      witness.completionLaw.toNoStageCompletionWitness.flagshipBoundaryTargetOfEndpointWitnessTarget
        ⟨endpointWitnesses⟩
  exact ⟨completionLaw, hbridge₀, hprinciple₀, huniqueLaw, hboundary⟩

/-- One unique no-stage completion law on the law-native bridge and physical
principle, together with one boundary-complete completion bridge on that same
microscopic law, already yields the honest boundary-form candidate law target.
Completion-law uniqueness transports the boundary closure of that one bridge
onto the unique completion law. -/
theorem canonicalBoundaryMicroscopicLawTargetOfCanonicalCompletionLawTarget_and_flagshipCompletionBridgeTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalCompletionLawTarget ∧
        data.flagshipCompletionBridgeTarget) :
    data.canonicalBoundaryMicroscopicLawTarget := by
  rcases htarget with ⟨hcompletionLaw, hflagshipBridge⟩
  rcases hcompletionLaw with ⟨completionLaw, hbridge₀, hprinciple₀, huniqueLaw⟩
  rcases hflagshipBridge with ⟨bridge, sameLaw, hboundaryBridge⟩
  have hbridge :
      bridge.toLocalEventFourStateCompletionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge := by
    calc
      bridge.toLocalEventFourStateCompletionLaw.fourStateLaw.framed.object.bridge =
          bridge.toMicroscopicClosureLaw.bridge := by
        rfl
      _ = data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge := by
        exact congrArg MicroscopicClosureLaw.bridge sameLaw
  have hprinciple :
      bridge.toLocalEventFourStateCompletionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple := by
    calc
      bridge.toLocalEventFourStateCompletionLaw.fourStateLaw.framed.object.physicalPrinciple =
          bridge.toMicroscopicClosureLaw.physicalPrinciple := by
        rfl
      _ = data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple := by
        exact congrArg MicroscopicClosureLaw.physicalPrinciple sameLaw
  have hsameCompletion :
      bridge.toLocalEventFourStateCompletionLaw = completionLaw :=
    huniqueLaw bridge.toLocalEventFourStateCompletionLaw hbridge hprinciple
  have hboundary :
      FlagshipBoundaryTarget completionLaw.toNoStageCompletionWitness := by
    cases hsameCompletion
    simpa [NoStageCompletionBridge.toNoStageCompletionWitness,
      LocalEventFourStateCompletionLaw.toNoStageCompletionWitness] using
      hboundaryBridge
  exact ⟨completionLaw, hbridge₀, hprinciple₀, huniqueLaw, hboundary⟩

/-- The same honest boundary-form candidate law already follows from one
unique completion law together with selected-cut endpoint terminality. The
endpoint-terminality surface supplies one boundary-complete law-native bridge,
and completion-law uniqueness transports that boundary closure onto the unique
completion law. -/
theorem canonicalBoundaryMicroscopicLawTargetOfCanonicalCompletionLawTarget_and_selectedCutEndpointTerminalityTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalCompletionLawTarget ∧
        data.selectedCutEndpointTerminalityTarget) :
    data.canonicalBoundaryMicroscopicLawTarget := by
  rcases htarget with ⟨hcompletionLaw, hterminality⟩
  exact
    data.canonicalBoundaryMicroscopicLawTargetOfCanonicalCompletionLawTarget_and_flagshipCompletionBridgeTarget
      ⟨hcompletionLaw,
        data.flagshipCompletionBridgeTargetOfSelectedCutEndpointTerminalityTarget
          hterminality⟩

/-- The honest boundary-form candidate-law target is equivalently one unique
no-stage completion law on the law-native bridge and physical principle
together with one endpoint-complete flagship witness on that same microscopic
law. Boundary closure on the unique completion law and existence of one
endpoint-complete witness are the same information once completion-law
uniqueness is known. -/
theorem canonicalBoundaryMicroscopicLawTarget_iff_canonicalCompletionLawTarget_and_flagshipWitnessTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalBoundaryMicroscopicLawTarget ↔
      (data.canonicalCompletionLawTarget ∧
        data.flagshipWitnessTarget) := by
  constructor
  · intro htarget
    rcases htarget with
      ⟨completionLaw, hbridge, hprinciple, huniqueLaw, hboundary⟩
    let law := data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw
    have hfrontier : FlagshipFrontierTarget law := by
      refine
        ⟨{ completionLaw := completionLaw
           sameBridge := hbridge
           samePhysicalPrinciple := hprinciple }, ?_⟩
      simpa using hboundary
    exact
      ⟨⟨completionLaw, hbridge, hprinciple, huniqueLaw⟩,
        law.flagshipTargetOfFrontierTarget hfrontier⟩
  · intro htarget
    exact
      data.canonicalBoundaryMicroscopicLawTargetOfCanonicalCompletionLawTarget_and_flagshipWitnessTarget
        htarget

/-- The honest boundary-form candidate law is exactly equivalent to the more
law-facing completion-side formulation: one unique no-stage completion law on
the law-native bridge and physical principle, with aggregate flagship boundary
closure automatic on every such completion law. Because the completion law is
already unique, the universal fill clause collapses to boundary closure on the
same unique law and loses no information. -/
theorem canonicalCompletionLawBoundaryFillTarget_iff_canonicalBoundaryMicroscopicLawTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalCompletionLawBoundaryFillTarget ↔
      data.canonicalBoundaryMicroscopicLawTarget := by
  constructor
  · intro htarget
    rcases htarget with
      ⟨completionLaw, hbridge, hprinciple, huniqueLaw, hfill⟩
    exact
      ⟨completionLaw,
        hbridge,
        hprinciple,
        huniqueLaw,
        hfill completionLaw hbridge hprinciple⟩
  · intro htarget
    rcases htarget with
      ⟨completionLaw, hbridge, hprinciple, huniqueLaw, hboundary⟩
    refine ⟨completionLaw, hbridge, hprinciple, huniqueLaw, ?_⟩
    intro other hotherBridge hotherPrinciple
    have hsame : other = completionLaw :=
      huniqueLaw other hotherBridge hotherPrinciple
    cases hsame
    exact hboundary

/-- One unique no-stage completion law on the law-native bridge and physical
principle, together with one endpoint-complete flagship witness on the same
microscopic law, already forces automatic aggregate flagship boundary closure
on every aligned completion law. -/
theorem canonicalCompletionLawBoundaryFillTargetOfCanonicalCompletionLawTarget_and_flagshipWitnessTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalCompletionLawTarget ∧
        data.flagshipWitnessTarget) :
    data.canonicalCompletionLawBoundaryFillTarget := by
  exact
    (data.canonicalCompletionLawBoundaryFillTarget_iff_canonicalBoundaryMicroscopicLawTarget).2
      (data.canonicalBoundaryMicroscopicLawTargetOfCanonicalCompletionLawTarget_and_flagshipWitnessTarget
        htarget)

/-- The same law-side universal boundary-fill theorem already follows from one
unique completion law together with one boundary-complete completion bridge on
the same microscopic law. No endpoint-bundle packaging is needed here. -/
theorem canonicalCompletionLawBoundaryFillTargetOfCanonicalCompletionLawTarget_and_flagshipCompletionBridgeTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalCompletionLawTarget ∧
        data.flagshipCompletionBridgeTarget) :
    data.canonicalCompletionLawBoundaryFillTarget := by
  exact
    (data.canonicalCompletionLawBoundaryFillTarget_iff_canonicalBoundaryMicroscopicLawTarget).2
      (data.canonicalBoundaryMicroscopicLawTargetOfCanonicalCompletionLawTarget_and_flagshipCompletionBridgeTarget
        htarget)

/-- The fixed-assembly alignment theorem therefore already upgrades one unique
completion law to law-side universal boundary fill. -/
theorem canonicalCompletionLawBoundaryFillTargetOfCanonicalCompletionLawTarget_and_canonicalLawNativeAlignmentBoundaryTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalCompletionLawTarget ∧
        data.canonicalLawNativeAlignmentBoundaryTarget) :
    data.canonicalCompletionLawBoundaryFillTarget := by
  rcases htarget with ⟨hcompletionLaw, halignment⟩
  exact
    data.canonicalCompletionLawBoundaryFillTargetOfCanonicalCompletionLawTarget_and_flagshipCompletionBridgeTarget
      ⟨hcompletionLaw,
        data.flagshipCompletionBridgeTargetOfCanonicalLawNativeAlignmentBoundaryTarget
          halignment⟩

/-- The same law-side universal boundary-fill theorem may be read directly in
public endpoint-terminality language: one unique completion law together with
selected-cut endpoint terminality already forces boundary closure on every
aligned completion law. -/
theorem canonicalCompletionLawBoundaryFillTargetOfCanonicalCompletionLawTarget_and_selectedCutEndpointTerminalityTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalCompletionLawTarget ∧
        data.selectedCutEndpointTerminalityTarget) :
    data.canonicalCompletionLawBoundaryFillTarget := by
  rcases htarget with ⟨hcompletionLaw, hterminality⟩
  exact
    data.canonicalCompletionLawBoundaryFillTargetOfCanonicalCompletionLawTarget_and_flagshipCompletionBridgeTarget
      ⟨hcompletionLaw,
        data.flagshipCompletionBridgeTargetOfSelectedCutEndpointTerminalityTarget
          hterminality⟩

/-- The law-facing boundary-fill target is equivalently one unique no-stage
completion law on the law-native bridge and physical principle together with
one endpoint-complete flagship witness on the same microscopic law. Once the
completion law is unique, a single endpoint-complete witness already forces
boundary closure on every aligned completion law. -/
theorem canonicalCompletionLawBoundaryFillTarget_iff_canonicalCompletionLawTarget_and_flagshipWitnessTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalCompletionLawBoundaryFillTarget ↔
      (data.canonicalCompletionLawTarget ∧
        data.flagshipWitnessTarget) := by
  constructor
  · intro htarget
    exact
      (data.canonicalBoundaryMicroscopicLawTarget_iff_canonicalCompletionLawTarget_and_flagshipWitnessTarget).1
        ((data.canonicalCompletionLawBoundaryFillTarget_iff_canonicalBoundaryMicroscopicLawTarget).1
          htarget)
  · intro htarget
    exact
      data.canonicalCompletionLawBoundaryFillTargetOfCanonicalCompletionLawTarget_and_flagshipWitnessTarget
        htarget

/-- Once the smaller constructive sector law has already collapsed to the
law-native one, the law-side completion-boundary fill theorem already yields
the fixed-assembly candidate-law target. The unique aligned completion law
therefore determines one law-native Step 4 alignment, and law-side boundary
fill applies to every reconstructed law-native completion law. -/
theorem canonicalCompletionBoundaryLawFillTargetOfCanonicalLawNativeSectorCollapseTarget_and_canonicalCompletionLawBoundaryFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalLawNativeSectorCollapseTarget ∧
        data.canonicalCompletionLawBoundaryFillTarget) :
    data.canonicalCompletionBoundaryLawFillTarget := by
  rcases htarget with ⟨hsectorCollapse, hlawFill⟩
  rcases hlawFill with ⟨completionLaw, hbridge, hprinciple, huniqueLaw, hboundaryAll⟩
  have hsector :
      completionLaw.toConstructiveSectorLaw =
        data.lawNativeConstructiveSectorLaw :=
    hsectorCollapse completionLaw hbridge hprinciple
  let alignment : CompletionAlignment data.lawNativeConstructiveSectorLaw :=
    hsector ▸ completionLaw.toCompletionAlignment
  have hcanonical :
      data.lawNativeCompletionLawOfAlignment alignment = completionLaw := by
    exact
      huniqueLaw
        (data.lawNativeCompletionLawOfAlignment alignment)
        (data.lawNativeCompletionLawOfAlignment_sameBridge alignment)
        (data.lawNativeCompletionLawOfAlignment_samePhysicalPrinciple alignment)
  have hboundary :
      FlagshipBoundaryTarget
        (data.lawNativeCompletionLawOfAlignment alignment).toNoStageCompletionWitness := by
    exact
      hboundaryAll
        (data.lawNativeCompletionLawOfAlignment alignment)
        (data.lawNativeCompletionLawOfAlignment_sameBridge alignment)
        (data.lawNativeCompletionLawOfAlignment_samePhysicalPrinciple alignment)
  let law :
      CompletionBoundaryLaw
        Index Time Carrier Law
        data.lawNativeConstructiveSectorLaw
        data.lawNativeFourStateAssembly :=
    { alignment := alignment
      boundary := hboundary }
  refine ⟨?_, ?_⟩
  · refine ⟨law, ?_⟩
    intro other
    have hotherCompletion :
        other.toCompletionLaw = completionLaw := by
      exact
        huniqueLaw
          other.toCompletionLaw
          (by
            simpa [CompletionBoundaryLaw.toCompletionLaw,
              TerminalExactificationLaw.lawNativeCompletionLawOfAlignment] using
              data.lawNativeCompletionLawOfAlignment_sameBridge other.alignment)
          (by
            simpa [CompletionBoundaryLaw.toCompletionLaw,
              TerminalExactificationLaw.lawNativeCompletionLawOfAlignment] using
              data.lawNativeCompletionLawOfAlignment_samePhysicalPrinciple other.alignment)
    have hlawCompletion :
        law.toCompletionLaw = completionLaw := by
      simpa [law, CompletionBoundaryLaw.toCompletionLaw,
        TerminalExactificationLaw.lawNativeCompletionLawOfAlignment] using hcanonical
    have hsameCompletion :
        other.toCompletionLaw = law.toCompletionLaw :=
      hotherCompletion.trans hlawCompletion.symm
    have hbridgeEq :
        other.toCompletionLaw.toNoStageCompletionBridge =
          law.toCompletionLaw.toNoStageCompletionBridge :=
      congrArg LocalEventFourStateCompletionLaw.toNoStageCompletionBridge hsameCompletion
    have hcompletionEq :
        other.alignment.toNaturalOperatorCompletion =
          law.alignment.toNaturalOperatorCompletion := by
      have hcompletionEq' :
          other.toCompletionLaw.toNoStageCompletionBridge.completion =
            law.toCompletionLaw.toNoStageCompletionBridge.completion :=
        congrArg NoStageCompletionBridge.completion hbridgeEq
      simpa [CompletionBoundaryLaw.toCompletionLaw,
        law,
        TerminalExactificationLaw.lawNativeCompletionLawOfAlignment,
        LocalEventFourStateCompletionLaw.toNoStageCompletionBridge,
        FourStateAssembly.toNoStageCompletionBridge] using hcompletionEq'
    exact
      CompletionBoundaryLaw.eq_of_alignment_eq
        (CompletionAlignment.eq_of_toNaturalOperatorCompletion_eq hcompletionEq)
  · intro other
    exact
      hboundaryAll
        (data.lawNativeCompletionLawOfAlignment other)
        (data.lawNativeCompletionLawOfAlignment_sameBridge other)
        (data.lawNativeCompletionLawOfAlignment_samePhysicalPrinciple other)

/-- The smaller law-native sector-collapse theorem is enough to convert the
law-side boundary-fill principle into selected-cut endpoint terminality. The
four-state assembly fill then follows automatically from the now-forced
fixed-assembly candidate law. -/
theorem canonicalSelectedCompletionTargetOfCanonicalLawNativeSectorCollapseTarget_and_canonicalCompletionLawBoundaryFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalLawNativeSectorCollapseTarget ∧
        data.canonicalCompletionLawBoundaryFillTarget) :
    data.canonicalSelectedCompletionTarget := by
  rcases htarget with ⟨hsectorCollapse, hlawFill⟩
  have hboundaryFill :
      data.canonicalCompletionBoundaryLawFillTarget :=
    data.canonicalCompletionBoundaryLawFillTargetOfCanonicalLawNativeSectorCollapseTarget_and_canonicalCompletionLawBoundaryFillTarget
      ⟨hsectorCollapse, hlawFill⟩
  rcases hlawFill with ⟨completionLaw, hbridge, hprinciple, huniqueLaw, _hboundaryAll⟩
  have hcompletionLaw :
      data.canonicalCompletionLawTarget := by
    exact ⟨completionLaw, hbridge, hprinciple, huniqueLaw⟩
  have hcollapse :
      data.canonicalLawNativeCompletionCollapseTarget :=
    data.canonicalLawNativeCompletionCollapseTargetOfCanonicalCompletionLawTarget_and_canonicalCompletionBoundaryLawFillTarget
      ⟨hcompletionLaw, hboundaryFill⟩
  exact ⟨hcollapse, hboundaryFill⟩

/-- The same selected-completion theorem already follows from the smaller
combination of current-side sector collapse, one unique completion law, and
the fixed-assembly alignment theorem. The alignment theorem supplies a single
boundary-complete bridge on the law-native microscopic law, and completion-law
uniqueness upgrades that single bridge to law-side universal boundary fill. -/
theorem canonicalSelectedCompletionTargetOfCanonicalLawNativeSectorCollapseTarget_and_canonicalCompletionLawTarget_and_canonicalLawNativeAlignmentBoundaryTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalLawNativeSectorCollapseTarget ∧
        data.canonicalCompletionLawTarget ∧
        data.canonicalLawNativeAlignmentBoundaryTarget) :
    data.canonicalSelectedCompletionTarget := by
  rcases htarget with ⟨hsectorCollapse, hrest⟩
  rcases hrest with ⟨hcompletionLaw, halignment⟩
  have hboundaryFill :
      data.canonicalCompletionLawBoundaryFillTarget :=
    data.canonicalCompletionLawBoundaryFillTargetOfCanonicalCompletionLawTarget_and_canonicalLawNativeAlignmentBoundaryTarget
      ⟨hcompletionLaw, halignment⟩
  exact
    data.canonicalSelectedCompletionTargetOfCanonicalLawNativeSectorCollapseTarget_and_canonicalCompletionLawBoundaryFillTarget
      ⟨hsectorCollapse, hboundaryFill⟩

/-- Replacing the alignment theorem by the equivalent lower-level Step 4 route
does not change the same selected-completion consequence. -/
theorem canonicalSelectedCompletionTargetOfCanonicalLawNativeSectorCollapseTarget_and_canonicalCompletionLawTarget_and_canonicalLawNativeStep4BoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalLawNativeSectorCollapseTarget ∧
        data.canonicalCompletionLawTarget ∧
        data.canonicalLawNativeStep4BoundaryRouteTarget) :
    data.canonicalSelectedCompletionTarget := by
  rcases htarget with ⟨hsectorCollapse, hrest⟩
  rcases hrest with ⟨hcompletionLaw, hstep4⟩
  exact
    data.canonicalSelectedCompletionTargetOfCanonicalLawNativeSectorCollapseTarget_and_canonicalCompletionLawTarget_and_canonicalLawNativeAlignmentBoundaryTarget
      ⟨hsectorCollapse,
        hcompletionLaw,
        data.canonicalLawNativeAlignmentBoundaryTargetOfCanonicalLawNativeStep4BoundaryRouteTarget
          hstep4⟩

/-- The larger completion-collapse clause is therefore stronger than needed
for the same descent: once the completion law is unique and boundary-complete
on the law-native bridge, only the smaller law-native sector collapse is still
required to recover the selected-cut endpoint theorem. -/
theorem canonicalCompletionBoundaryLawFillTargetOfCanonicalLawNativeCompletionCollapseTarget_and_canonicalCompletionLawBoundaryFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalLawNativeCompletionCollapseTarget ∧
        data.canonicalCompletionLawBoundaryFillTarget) :
    data.canonicalCompletionBoundaryLawFillTarget := by
  rcases htarget with ⟨hcollapse, hlawFill⟩
  exact
    data.canonicalCompletionBoundaryLawFillTargetOfCanonicalLawNativeSectorCollapseTarget_and_canonicalCompletionLawBoundaryFillTarget
      ⟨data.canonicalLawNativeSectorCollapseTargetOfCanonicalLawNativeCompletionCollapseTarget
          hcollapse,
        hlawFill⟩

/-- Splitting the stricter law-native route into the two smaller Step 4
packages loses no information: a unique rigidity package and a unique
canonical representative package rebuild the same unique alignment. -/
theorem canonicalLawNativeAlignmentBoundaryRouteTargetOfCanonicalLawNativeStateBridgeBoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeStateBridgeBoundaryRouteTarget) :
    data.canonicalLawNativeAlignmentBoundaryRouteTarget := by
  rcases htarget with ⟨hcurrentSurface, alignment, huniqueAlignment, hboundary⟩
  refine ⟨?_, alignment, huniqueAlignment, hboundary⟩
  intro completionLaw hbridge hprinciple
  rcases hcurrentSurface completionLaw hbridge hprinciple with
    ⟨hstateBridge, hassemblyStateBridge, hgeneration, hintrinsic, hminimal⟩
  have hsector :
      completionLaw.toConstructiveSectorLaw =
        data.lawNativeConstructiveSectorLaw :=
    data.lawNativeSectorCollapseOfStateBridgeAndStep3Data
      completionLaw
      hstateBridge
      hgeneration
      hintrinsic
      hminimal
  exact
    ⟨hsector,
      data.lawNativeAssemblyFillOfExtractedStateBridge
        completionLaw
        hsector
        hassemblyStateBridge⟩

/-- Splitting the stricter law-native route into the two smaller Step 4
packages loses no information: a unique rigidity package and a unique
canonical representative package rebuild the same unique alignment. -/
theorem canonicalLawNativeAlignmentBoundaryRouteTargetOfCanonicalLawNativePartsBoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativePartsBoundaryRouteTarget) :
    data.canonicalLawNativeAlignmentBoundaryRouteTarget := by
  rcases htarget with
    ⟨hcollapse, rigidity, huniqueRigidity,
      representatives, huniqueRepresentatives, hboundary⟩
  let alignment : CompletionAlignment data.lawNativeConstructiveSectorLaw :=
    CompletionAlignment.ofParts rigidity representatives
  refine ⟨hcollapse, alignment, ?_, ?_⟩
  · intro other
    have hrigidity :
        other.toCompletionRigidity = rigidity :=
      huniqueRigidity other.toCompletionRigidity
    have hrepresentatives :
        other.toCanonicalRepresentatives = representatives :=
      huniqueRepresentatives other.toCanonicalRepresentatives
    calc
      other =
          CompletionAlignment.ofParts
            other.toCompletionRigidity
            other.toCanonicalRepresentatives := by
              symm
              exact CompletionAlignment.ofParts_eq other
      _ = CompletionAlignment.ofParts rigidity representatives := by
            simp [hrigidity, hrepresentatives]
      _ = alignment := rfl
  · simpa [alignment] using hboundary

/-- Conversely, the stricter law-native route already determines its smaller
Step 4 pieces uniquely: the alignment remembers exactly one rigidity package
and one canonical representative package. -/
theorem canonicalLawNativePartsBoundaryRouteTargetOfCanonicalLawNativeAlignmentBoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeAlignmentBoundaryRouteTarget) :
    data.canonicalLawNativePartsBoundaryRouteTarget := by
  rcases htarget with ⟨hcollapse, alignment, huniqueAlignment, hboundary⟩
  let rigidity : CompletionRigidity data.lawNativeConstructiveSectorLaw :=
    alignment.toCompletionRigidity
  let representatives : CanonicalRepresentatives :=
    alignment.toCanonicalRepresentatives
  refine ⟨hcollapse, rigidity, ?_, representatives, ?_, ?_⟩
  · intro other
    have halignment :
        CompletionAlignment.ofParts other representatives = alignment :=
      huniqueAlignment (CompletionAlignment.ofParts other representatives)
    have hrigiditySurface :
        (CompletionAlignment.ofParts other representatives).toCompletionRigidity =
          alignment.toCompletionRigidity :=
      congrArg CompletionAlignment.toCompletionRigidity halignment
    calc
      other =
          (CompletionAlignment.ofParts other representatives).toCompletionRigidity := by
            symm
            exact CompletionAlignment.ofParts_toCompletionRigidity other representatives
      _ = alignment.toCompletionRigidity := hrigiditySurface
      _ = rigidity := rfl
  · intro other
    have halignment :
        CompletionAlignment.ofParts rigidity other = alignment :=
      huniqueAlignment (CompletionAlignment.ofParts rigidity other)
    have hrepresentativeSurface :
        (CompletionAlignment.ofParts rigidity other).toCanonicalRepresentatives =
          alignment.toCanonicalRepresentatives :=
      congrArg CompletionAlignment.toCanonicalRepresentatives halignment
    calc
      other =
          (CompletionAlignment.ofParts rigidity other).toCanonicalRepresentatives := by
            symm
            exact CompletionAlignment.ofParts_toCanonicalRepresentatives rigidity other
      _ = alignment.toCanonicalRepresentatives := hrepresentativeSurface
      _ = representatives := rfl
  · simpa [rigidity, representatives] using hboundary

/-- Thus the stricter law-native route can be read either through one unique
alignment or through its exact smaller Step 4 parts. -/
theorem canonicalLawNativePartsBoundaryRouteTarget_iff_canonicalLawNativeAlignmentBoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalLawNativePartsBoundaryRouteTarget ↔
      data.canonicalLawNativeAlignmentBoundaryRouteTarget := by
  constructor
  · intro htarget
    exact
      data.canonicalLawNativeAlignmentBoundaryRouteTargetOfCanonicalLawNativePartsBoundaryRouteTarget
        htarget
  · intro htarget
    exact
      data.canonicalLawNativePartsBoundaryRouteTargetOfCanonicalLawNativeAlignmentBoundaryRouteTarget
        htarget

/-- The smaller rigidity-split route already determines the law-native Step 4
package uniquely: once the endpoint-rigidity principle on the fixed sector
generation, the reduced endpoint-rigidity surface, and the representative
package are fixed, the intermediate rigidity package and hence the alignment
are fixed as well. -/
theorem canonicalLawNativePartsBoundaryRouteTargetOfCanonicalLawNativeRigidityBoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeRigidityBoundaryRouteTarget) :
    data.canonicalLawNativePartsBoundaryRouteTarget := by
  rcases htarget with
    ⟨hcollapse, rigidityPrinciple, usesSectorGeneration, huniquePrinciple,
      endpointRigidity, huniqueEndpointRigidity,
      representatives, huniqueRepresentatives, hboundary⟩
  let rigidity : CompletionRigidity data.lawNativeConstructiveSectorLaw :=
    CompletionRigidity.ofParts
      rigidityPrinciple
      usesSectorGeneration
      endpointRigidity
  refine
    ⟨hcollapse, rigidity, ?_, representatives, huniqueRepresentatives, ?_⟩
  · intro other
    have hprinciple :
        other.rigidityPrinciple = rigidityPrinciple :=
      huniquePrinciple other.rigidityPrinciple other.usesSectorGeneration
    have hendpoint :
        other.endpointRigidity = endpointRigidity :=
      huniqueEndpointRigidity other.endpointRigidity
    exact CompletionRigidity.eq_of_parts_eq hprinciple hendpoint
  · simpa [rigidity] using hboundary

/-- Conversely, the split-Step-4 route already determines the smaller
rigidity pieces uniquely: the rigidity package remembers exactly one endpoint-
rigidity principle on the fixed sector generation and exactly one reduced
endpoint-rigidity surface. -/
theorem canonicalLawNativeRigidityBoundaryRouteTargetOfCanonicalLawNativePartsBoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativePartsBoundaryRouteTarget) :
    data.canonicalLawNativeRigidityBoundaryRouteTarget := by
  rcases htarget with
    ⟨hcollapse, rigidity, huniqueRigidity,
      representatives, huniqueRepresentatives, hboundary⟩
  let rigidityPrinciple := rigidity.rigidityPrinciple
  let usesSectorGeneration := rigidity.usesSectorGeneration
  let endpointRigidity := rigidity.endpointRigidity
  refine
    ⟨hcollapse, rigidityPrinciple, usesSectorGeneration, ?_,
      endpointRigidity, ?_, representatives, huniqueRepresentatives, ?_⟩
  · intro other hotherSectorGeneration
    let otherRigidity : CompletionRigidity data.lawNativeConstructiveSectorLaw :=
      CompletionRigidity.ofParts
        other
        hotherSectorGeneration
        endpointRigidity
    have hsameRigidity : otherRigidity = rigidity :=
      huniqueRigidity otherRigidity
    have hsamePrinciple :
        otherRigidity.rigidityPrinciple = rigidity.rigidityPrinciple :=
      congrArg CompletionRigidity.rigidityPrinciple hsameRigidity
    simpa [rigidityPrinciple, otherRigidity] using hsamePrinciple
  · intro other
    let otherRigidity : CompletionRigidity data.lawNativeConstructiveSectorLaw :=
      CompletionRigidity.ofParts
        rigidityPrinciple
        usesSectorGeneration
        other
    have hsameRigidity : otherRigidity = rigidity :=
      huniqueRigidity otherRigidity
    have hsameEndpoint :
        otherRigidity.endpointRigidity = rigidity.endpointRigidity :=
      congrArg CompletionRigidity.endpointRigidity hsameRigidity
    simpa [endpointRigidity, otherRigidity] using hsameEndpoint
  · have hsameRigidity :
        CompletionRigidity.ofParts
            rigidityPrinciple
            usesSectorGeneration
            endpointRigidity =
          rigidity :=
      CompletionRigidity.ofParts_eq rigidity
    simpa [rigidityPrinciple, usesSectorGeneration, endpointRigidity, hsameRigidity] using
      hboundary

/-- Thus the stricter law-native route can also be read through the exact
smaller rigidity-side pieces without loss of information. -/
theorem canonicalLawNativeRigidityBoundaryRouteTarget_iff_canonicalLawNativePartsBoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalLawNativeRigidityBoundaryRouteTarget ↔
      data.canonicalLawNativePartsBoundaryRouteTarget := by
  constructor
  · intro htarget
    exact
      data.canonicalLawNativePartsBoundaryRouteTargetOfCanonicalLawNativeRigidityBoundaryRouteTarget
        htarget
  · intro htarget
    exact
      data.canonicalLawNativeRigidityBoundaryRouteTargetOfCanonicalLawNativePartsBoundaryRouteTarget
        htarget

/-- The smaller rigidity-split route has two independent ingredients: the
current-side completion-collapse clause and the fixed-assembly Step 4
uniqueness/boundary remainder. -/
theorem canonicalLawNativeCompletionCollapseTarget_and_canonicalLawNativeStep4BoundaryRouteTarget_of_canonicalLawNativeRigidityBoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeRigidityBoundaryRouteTarget) :
    data.canonicalLawNativeCompletionCollapseTarget ∧
      data.canonicalLawNativeStep4BoundaryRouteTarget := by
  rcases htarget with
    ⟨hcollapse, rigidityPrinciple, usesSectorGeneration, huniquePrinciple,
      endpointRigidity, huniqueEndpointRigidity,
      representatives, huniqueRepresentatives, hboundary⟩
  exact
    ⟨hcollapse,
      ⟨rigidityPrinciple,
        usesSectorGeneration,
        huniquePrinciple,
        endpointRigidity,
        huniqueEndpointRigidity,
        representatives,
        huniqueRepresentatives,
        hboundary⟩⟩

/-- Conversely, recombining the current-side completion-collapse clause with
the fixed-assembly Step 4 uniqueness/boundary remainder recovers the exact
smaller rigidity-split route. -/
theorem canonicalLawNativeRigidityBoundaryRouteTarget_of_canonicalLawNativeCompletionCollapseTarget_and_canonicalLawNativeStep4BoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalLawNativeCompletionCollapseTarget ∧
        data.canonicalLawNativeStep4BoundaryRouteTarget) :
    data.canonicalLawNativeRigidityBoundaryRouteTarget := by
  rcases htarget with ⟨hcollapse, hstep4⟩
  rcases hstep4 with
    ⟨rigidityPrinciple, usesSectorGeneration, huniquePrinciple,
      endpointRigidity, huniqueEndpointRigidity,
      representatives, huniqueRepresentatives, hboundary⟩
  exact
    ⟨hcollapse, rigidityPrinciple, usesSectorGeneration, huniquePrinciple,
      endpointRigidity, huniqueEndpointRigidity,
      representatives, huniqueRepresentatives, hboundary⟩

/-- So the remaining strict route splits exactly into a current-side collapse
problem and a fixed-assembly Step 4 uniqueness/boundary problem. -/
theorem canonicalLawNativeRigidityBoundaryRouteTarget_iff_canonicalLawNativeCompletionCollapseTarget_and_canonicalLawNativeStep4BoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalLawNativeRigidityBoundaryRouteTarget ↔
      (data.canonicalLawNativeCompletionCollapseTarget ∧
        data.canonicalLawNativeStep4BoundaryRouteTarget) := by
  constructor
  · intro htarget
    exact
      data.canonicalLawNativeCompletionCollapseTarget_and_canonicalLawNativeStep4BoundaryRouteTarget_of_canonicalLawNativeRigidityBoundaryRouteTarget
        htarget
  · intro htarget
    exact
      data.canonicalLawNativeRigidityBoundaryRouteTarget_of_canonicalLawNativeCompletionCollapseTarget_and_canonicalLawNativeStep4BoundaryRouteTarget
        htarget

/-- The stricter law-native route can also be read directly through the new
fixed-assembly candidate-law target: it is exactly the current-side completion
collapse clause together with one unique completion-boundary law carrying
automatic boundary closure across the whole law-native alignment class. -/
theorem canonicalLawNativeCompletionCollapseTarget_and_canonicalCompletionBoundaryLawFillTarget_of_canonicalLawNativeAlignmentBoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeAlignmentBoundaryRouteTarget) :
    data.canonicalLawNativeCompletionCollapseTarget ∧
      data.canonicalCompletionBoundaryLawFillTarget := by
  rcases htarget with ⟨hcollapse, alignment, huniqueAlignment, hboundary⟩
  refine ⟨hcollapse, ?_⟩
  exact
    data.canonicalCompletionBoundaryLawFillTargetOfCanonicalLawNativeAlignmentBoundaryTarget
      ⟨alignment, huniqueAlignment, hboundary⟩

/-- Conversely, the current-side collapse clause together with the sharper
fixed-assembly candidate-law target already rebuild the strict law-native
route. -/
theorem canonicalLawNativeAlignmentBoundaryRouteTarget_of_canonicalLawNativeCompletionCollapseTarget_and_canonicalCompletionBoundaryLawFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalLawNativeCompletionCollapseTarget ∧
        data.canonicalCompletionBoundaryLawFillTarget) :
    data.canonicalLawNativeAlignmentBoundaryRouteTarget := by
  rcases htarget with ⟨hcollapse, hfill⟩
  have halignment :
      data.canonicalLawNativeAlignmentBoundaryTarget :=
    (data.canonicalCompletionBoundaryLawFillTarget_iff_canonicalLawNativeAlignmentBoundaryTarget).1
      hfill
  rcases halignment with ⟨alignment, huniqueAlignment, hboundary⟩
  exact ⟨hcollapse, alignment, huniqueAlignment, hboundary⟩

/-- So the strict law-native route is exactly the same as the conjunction of
current-side completion collapse and the sharper unique fixed-assembly
candidate-law target. -/
theorem canonicalLawNativeAlignmentBoundaryRouteTarget_iff_canonicalLawNativeCompletionCollapseTarget_and_canonicalCompletionBoundaryLawFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalLawNativeAlignmentBoundaryRouteTarget ↔
      (data.canonicalLawNativeCompletionCollapseTarget ∧
        data.canonicalCompletionBoundaryLawFillTarget) := by
  constructor
  · intro htarget
    exact
      data.canonicalLawNativeCompletionCollapseTarget_and_canonicalCompletionBoundaryLawFillTarget_of_canonicalLawNativeAlignmentBoundaryRouteTarget
        htarget
  · intro htarget
    exact
      data.canonicalLawNativeAlignmentBoundaryRouteTarget_of_canonicalLawNativeCompletionCollapseTarget_and_canonicalCompletionBoundaryLawFillTarget
        htarget

/-- The remaining strict route is exactly current-side completion collapse
plus selected-cut endpoint terminality. -/
theorem canonicalLawNativeAlignmentBoundaryRouteTarget_iff_canonicalLawNativeCompletionCollapseTarget_and_selectedCutEndpointTerminalityTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalLawNativeAlignmentBoundaryRouteTarget ↔
      (data.canonicalLawNativeCompletionCollapseTarget ∧
        data.selectedCutEndpointTerminalityTarget) := by
  exact
    data.canonicalLawNativeAlignmentBoundaryRouteTarget_iff_canonicalLawNativeCompletionCollapseTarget_and_canonicalCompletionBoundaryLawFillTarget

/-- So the strict remaining route is exactly the same as the canonical
selected completion target. -/
theorem canonicalSelectedCompletionTarget_iff_canonicalLawNativeAlignmentBoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalSelectedCompletionTarget ↔
      data.canonicalLawNativeAlignmentBoundaryRouteTarget := by
  exact Iff.symm
    (data.canonicalLawNativeAlignmentBoundaryRouteTarget_iff_canonicalLawNativeCompletionCollapseTarget_and_canonicalCompletionBoundaryLawFillTarget)

/-- The strict law-native route therefore already yields the canonical
selected completion target. -/
theorem canonicalSelectedCompletionTargetOfCanonicalLawNativeAlignmentBoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeAlignmentBoundaryRouteTarget) :
    data.canonicalSelectedCompletionTarget := by
  exact
    (data.canonicalSelectedCompletionTarget_iff_canonicalLawNativeAlignmentBoundaryRouteTarget).2
      htarget

/-- Canonical selected completion is exactly current-side collapse plus
selected-cut endpoint terminality. -/
theorem canonicalSelectedCompletionTarget_iff_canonicalLawNativeCompletionCollapseTarget_and_selectedCutEndpointTerminalityTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalSelectedCompletionTarget ↔
      (data.canonicalLawNativeCompletionCollapseTarget ∧
        data.selectedCutEndpointTerminalityTarget) := by
  constructor
  · intro htarget
    have hroute :
        data.canonicalLawNativeAlignmentBoundaryRouteTarget :=
      (data.canonicalSelectedCompletionTarget_iff_canonicalLawNativeAlignmentBoundaryRouteTarget).1
        htarget
    exact
      (data.canonicalLawNativeAlignmentBoundaryRouteTarget_iff_canonicalLawNativeCompletionCollapseTarget_and_selectedCutEndpointTerminalityTarget).1
        hroute
  · intro htarget
    have hroute :
        data.canonicalLawNativeAlignmentBoundaryRouteTarget :=
      (data.canonicalLawNativeAlignmentBoundaryRouteTarget_iff_canonicalLawNativeCompletionCollapseTarget_and_selectedCutEndpointTerminalityTarget).2
        htarget
    exact
      (data.canonicalSelectedCompletionTarget_iff_canonicalLawNativeAlignmentBoundaryRouteTarget).2
        hroute

/-- Once current-side collapse is known, selected-cut endpoint terminality is
exactly the remaining theorem needed to force canonical selected completion. -/
theorem canonicalSelectedCompletionTargetOfCanonicalLawNativeCompletionCollapseTarget_and_selectedCutEndpointTerminalityTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalLawNativeCompletionCollapseTarget ∧
        data.selectedCutEndpointTerminalityTarget) :
    data.canonicalSelectedCompletionTarget := by
  exact
    (data.canonicalSelectedCompletionTarget_iff_canonicalLawNativeCompletionCollapseTarget_and_selectedCutEndpointTerminalityTarget).2
      htarget

/-- The more explicit state-bridge / Step 3 route already yields the canonical
selected completion target. This is the current sharpest law-native upstream
route phrased entirely through visible current-side data plus one unique Step 4
alignment on the fixed law-native sector law. -/
theorem canonicalLawNativeStateBridgeBoundaryRouteTarget_iff_canonicalLawNativeVisibleStateBridgeTarget_and_canonicalLawNativeStep3PackageTarget_and_canonicalLawNativeAlignmentBoundaryTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalLawNativeStateBridgeBoundaryRouteTarget ↔
      (data.canonicalLawNativeVisibleStateBridgeTarget ∧
        data.canonicalLawNativeStep3PackageTarget ∧
        data.canonicalLawNativeAlignmentBoundaryTarget) := by
  constructor
  · intro htarget
    rcases htarget with ⟨hcurrentSurface, alignment, huniqueAlignment, hboundary⟩
    refine ⟨?_, ?_, ⟨alignment, huniqueAlignment, hboundary⟩⟩
    · intro completionLaw hbridge hprinciple
      rcases hcurrentSurface completionLaw hbridge hprinciple with
        ⟨hstateBridge, hassemblyStateBridge, _hgeneration, _hintrinsic, _hminimal⟩
      exact ⟨hstateBridge, hassemblyStateBridge⟩
    · intro completionLaw hbridge hprinciple
      rcases hcurrentSurface completionLaw hbridge hprinciple with
        ⟨_hstateBridge, _hassemblyStateBridge, hgeneration, hintrinsic, hminimal⟩
      exact ⟨hgeneration, hintrinsic, hminimal⟩
  · intro htarget
    rcases htarget with ⟨hvisible, hstep3, halignment⟩
    rcases halignment with ⟨alignment, huniqueAlignment, hboundary⟩
    refine ⟨?_, alignment, huniqueAlignment, hboundary⟩
    intro completionLaw hbridge hprinciple
    rcases hvisible completionLaw hbridge hprinciple with
      ⟨hstateBridge, hassemblyStateBridge⟩
    rcases hstep3 completionLaw hbridge hprinciple with
      ⟨hgeneration, hintrinsic, hminimal⟩
    exact ⟨hstateBridge, hassemblyStateBridge, hgeneration, hintrinsic, hminimal⟩

/-- The more explicit state-bridge / Step 3 route already yields the canonical
selected completion target. This is the current sharpest law-native upstream
route phrased entirely through visible current-side data plus one unique Step 4
alignment on the fixed law-native sector law. -/
theorem canonicalSelectedCompletionTargetOfCanonicalLawNativeStateBridgeBoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeStateBridgeBoundaryRouteTarget) :
    data.canonicalSelectedCompletionTarget := by
  exact
    data.canonicalSelectedCompletionTargetOfCanonicalLawNativeAlignmentBoundaryRouteTarget
      (data.canonicalLawNativeAlignmentBoundaryRouteTargetOfCanonicalLawNativeStateBridgeBoundaryRouteTarget
        htarget)

/-- The explicit route can therefore be attacked as three independent
subproblems: visible current-side state-bridge rigidity, literal Step 3
packaging coherence, and one unique law-native Step 4 alignment with boundary
closure. Solving those three clauses already closes the canonical selected
completion target. -/
theorem canonicalSelectedCompletionTargetOfCanonicalLawNativeVisibleStateBridgeTarget_and_canonicalLawNativeStep3PackageTarget_and_canonicalLawNativeAlignmentBoundaryTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget :
      data.canonicalLawNativeVisibleStateBridgeTarget ∧
        data.canonicalLawNativeStep3PackageTarget ∧
        data.canonicalLawNativeAlignmentBoundaryTarget) :
    data.canonicalSelectedCompletionTarget := by
  exact
    data.canonicalSelectedCompletionTargetOfCanonicalLawNativeStateBridgeBoundaryRouteTarget
      ((data.canonicalLawNativeStateBridgeBoundaryRouteTarget_iff_canonicalLawNativeVisibleStateBridgeTarget_and_canonicalLawNativeStep3PackageTarget_and_canonicalLawNativeAlignmentBoundaryTarget).2
        htarget)

/-- Conversely, the canonical selected completion target already rebuilds the
strict law-native route. -/
theorem canonicalLawNativeAlignmentBoundaryRouteTargetOfCanonicalSelectedCompletionTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalSelectedCompletionTarget) :
    data.canonicalLawNativeAlignmentBoundaryRouteTarget := by
  exact
    (data.canonicalSelectedCompletionTarget_iff_canonicalLawNativeAlignmentBoundaryRouteTarget).1
      htarget

/-- The fixed-assembly Step 4 remainder alone already forces one unique
completion-boundary law on the law-native sector law and four-state assembly.
The current-side collapse clause is not used here. -/
theorem canonicalCompletionBoundaryLawTargetOfCanonicalLawNativeStep4BoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeStep4BoundaryRouteTarget) :
    data.canonicalCompletionBoundaryLawTarget := by
  rcases htarget with
    ⟨rigidityPrinciple, usesSectorGeneration, huniquePrinciple,
      endpointRigidity, huniqueEndpointRigidity,
      representatives, huniqueRepresentatives, hboundary⟩
  let rigidity : CompletionRigidity data.lawNativeConstructiveSectorLaw :=
    CompletionRigidity.ofParts
      rigidityPrinciple
      usesSectorGeneration
      endpointRigidity
  have huniqueRigidity :
      ∀ other : CompletionRigidity data.lawNativeConstructiveSectorLaw,
        other = rigidity := by
    intro other
    have hprinciple :
        other.rigidityPrinciple = rigidityPrinciple :=
      huniquePrinciple other.rigidityPrinciple other.usesSectorGeneration
    have hendpoint :
        other.endpointRigidity = endpointRigidity :=
      huniqueEndpointRigidity other.endpointRigidity
    exact CompletionRigidity.eq_of_parts_eq hprinciple hendpoint
  let alignment : CompletionAlignment data.lawNativeConstructiveSectorLaw :=
    CompletionAlignment.ofParts rigidity representatives
  have huniqueAlignment :
      ∀ other : CompletionAlignment data.lawNativeConstructiveSectorLaw,
        other = alignment := by
    intro other
    have hrigidity :
        other.toCompletionRigidity = rigidity :=
      huniqueRigidity other.toCompletionRigidity
    have hrepresentatives :
        other.toCanonicalRepresentatives = representatives :=
      huniqueRepresentatives other.toCanonicalRepresentatives
    calc
      other =
          CompletionAlignment.ofParts
            other.toCompletionRigidity
            other.toCanonicalRepresentatives := by
              symm
              exact CompletionAlignment.ofParts_eq other
      _ = CompletionAlignment.ofParts rigidity representatives := by
            simp [hrigidity, hrepresentatives]
      _ = alignment := rfl
  let law :
      CompletionBoundaryLaw
        Index Time Carrier Law
        data.lawNativeConstructiveSectorLaw
        data.lawNativeFourStateAssembly :=
    { alignment := alignment
      boundary := by simpa [alignment, rigidity] using hboundary }
  refine ⟨law, ?_⟩
  intro other
  exact CompletionBoundaryLaw.eq_of_alignment_eq (huniqueAlignment other.alignment)

/-- The stricter law-native route yields one canonical completion law on the
fixed law-native sector law whose canonical witness is already
boundary-complete.

This is the honest completion-law surface presently forced by the route
target. Literal uniqueness of the richer completion-law object is not claimed
here: the split completion bridge remembers only the smaller constructive
sector law, the current-side four-state assembly, and the smaller Step 4
alignment, not the full selected-bundle witness packaging of an arbitrary
`LocalEventFourStateCompletionLaw`. -/
theorem canonicalLawNativeBoundaryCompletionSurfaceOfCanonicalLawNativeAlignmentBoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeAlignmentBoundaryRouteTarget) :
    ∃ alignment : CompletionAlignment data.lawNativeConstructiveSectorLaw,
      (∀ other : CompletionAlignment data.lawNativeConstructiveSectorLaw,
        other = alignment) ∧
      let completionLaw := data.lawNativeCompletionLawOfAlignment alignment
      completionLaw.fourStateLaw.framed.object.bridge =
          data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
        completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
        FlagshipBoundaryTarget completionLaw.toNoStageCompletionWitness := by
  rcases htarget with ⟨_hcollapse, alignment, huniqueAlignment, hboundary⟩
  refine ⟨alignment, huniqueAlignment, ?_⟩
  let completionLaw := data.lawNativeCompletionLawOfAlignment alignment
  have hcompletionBridge :
      completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge := by
    exact data.lawNativeCompletionLawOfAlignment_sameBridge alignment
  have hcompletionPrinciple :
      completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple := by
    exact data.lawNativeCompletionLawOfAlignment_samePhysicalPrinciple alignment
  exact ⟨hcompletionBridge, hcompletionPrinciple, hboundary⟩

/-- The stricter law-native route also yields a literally unique smaller
candidate law on the fixed law-native four-state assembly: once the assembly
is fixed, the only remaining datum is the Step 4 alignment, and the route
target already makes that alignment unique. -/
theorem canonicalCompletionBoundaryLawTargetOfCanonicalLawNativeAlignmentBoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeAlignmentBoundaryRouteTarget) :
    data.canonicalCompletionBoundaryLawTarget := by
  rcases htarget with ⟨_hcollapse, alignment, huniqueAlignment, hboundary⟩
  let law :
      CompletionBoundaryLaw
        Index Time Carrier Law
        data.lawNativeConstructiveSectorLaw
        data.lawNativeFourStateAssembly :=
    { alignment := alignment
      boundary := hboundary }
  refine ⟨law, ?_⟩
  intro other
  exact CompletionBoundaryLaw.eq_of_alignment_eq (huniqueAlignment other.alignment)

/-- The smaller split-Step-4 route therefore already forces one unique
fixed-assembly completion-boundary law. -/
theorem canonicalCompletionBoundaryLawTargetOfCanonicalLawNativePartsBoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativePartsBoundaryRouteTarget) :
    data.canonicalCompletionBoundaryLawTarget := by
  exact
    data.canonicalCompletionBoundaryLawTargetOfCanonicalLawNativeAlignmentBoundaryRouteTarget
      ((data.canonicalLawNativePartsBoundaryRouteTarget_iff_canonicalLawNativeAlignmentBoundaryRouteTarget).1
        htarget)

/-- The still smaller rigidity-split route therefore also already forces one
unique fixed-assembly completion-boundary law. -/
theorem canonicalCompletionBoundaryLawTargetOfCanonicalLawNativeRigidityBoundaryRouteTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalLawNativeRigidityBoundaryRouteTarget) :
    data.canonicalCompletionBoundaryLawTarget := by
  exact
    data.canonicalCompletionBoundaryLawTargetOfCanonicalLawNativePartsBoundaryRouteTarget
      ((data.canonicalLawNativeRigidityBoundaryRouteTarget_iff_canonicalLawNativePartsBoundaryRouteTarget).1
        htarget)

/-- The smaller unique completion-boundary law already yields one strong
microscopic package on the same bridge and physical principle, and therefore
the analytic flagship surface and exact physical equation field. -/
theorem strongMicroscopicLawSurfaceOfCanonicalCompletionBoundaryLawTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionBoundaryLawTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong := by
  rcases htarget with ⟨law, _hunique⟩
  rcases law.surface with
    ⟨strong, hcompletion, _hcompletionSurface, hanalytic, hphysical⟩
  have hbridge :
      law.toCompletionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge := by
    exact data.lawNativeCompletionLawOfAlignment_sameBridge law.alignment
  have hprinciple :
      law.toCompletionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple := by
    exact data.lawNativeCompletionLawOfAlignment_samePhysicalPrinciple law.alignment
  refine ⟨strong, ?_, ?_, hanalytic, hphysical⟩
  · simpa [hcompletion] using hbridge
  · simpa [hcompletion] using hprinciple

/-- The sharper fixed-assembly candidate-law target already yields one strong
microscopic package on the same bridge and physical principle, and therefore
the analytic flagship surface and exact physical equation field. -/
theorem candidateLawSurfaceOfCanonicalCompletionBoundaryLawFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionBoundaryLawFillTarget) :
    ∃ law :
        CompletionBoundaryLaw
          Index Time Carrier Law
          data.lawNativeConstructiveSectorLaw
          data.lawNativeFourStateAssembly,
      (∀ other :
          CompletionBoundaryLaw
            Index Time Carrier Law
            data.lawNativeConstructiveSectorLaw
            data.lawNativeFourStateAssembly,
        other = law) ∧
      ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
        strong.completionLaw = law.toCompletionLaw ∧
        strong.completionLaw.fourStateLaw.framed.object.bridge =
          data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
        strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
        AnalyticFlagshipSurface strong ∧
        PhysicalEquationSurface strong := by
  rcases htarget with ⟨hlaw, _hfill⟩
  rcases hlaw with ⟨law, huniqueLaw⟩
  rcases law.surface with
    ⟨strong, hcompletion, _hcompletionSurface, hanalytic, hphysical⟩
  have hbridge :
      law.toCompletionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge := by
    exact data.lawNativeCompletionLawOfAlignment_sameBridge law.alignment
  have hprinciple :
      law.toCompletionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple := by
    exact data.lawNativeCompletionLawOfAlignment_samePhysicalPrinciple law.alignment
  refine ⟨law, huniqueLaw, strong, hcompletion, ?_, ?_, hanalytic, hphysical⟩
  · simpa [hcompletion] using hbridge
  · simpa [hcompletion] using hprinciple

/-- The sharper fixed-assembly candidate-law target already yields one strong
microscopic package on the same bridge and physical principle, and therefore
the analytic flagship surface and exact physical equation field. -/
theorem strongMicroscopicLawSurfaceOfCanonicalCompletionBoundaryLawFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionBoundaryLawFillTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong := by
  exact
    data.strongMicroscopicLawSurfaceOfCanonicalCompletionBoundaryLawTarget
      htarget.1

/-- Selected-cut endpoint terminality already yields the canonical fixed-
assembly candidate law together with its strong microscopic/equation package.
-/
theorem candidateLawSurfaceOfSelectedCutEndpointTerminalityTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.selectedCutEndpointTerminalityTarget) :
    ∃ law :
        CompletionBoundaryLaw
          Index Time Carrier Law
          data.lawNativeConstructiveSectorLaw
          data.lawNativeFourStateAssembly,
      (∀ other :
          CompletionBoundaryLaw
            Index Time Carrier Law
            data.lawNativeConstructiveSectorLaw
            data.lawNativeFourStateAssembly,
        other = law) ∧
      ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
        strong.completionLaw = law.toCompletionLaw ∧
        strong.completionLaw.fourStateLaw.framed.object.bridge =
          data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
        strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
        AnalyticFlagshipSurface strong ∧
        PhysicalEquationSurface strong := by
  exact data.candidateLawSurfaceOfCanonicalCompletionBoundaryLawFillTarget htarget

/-- Selected-cut endpoint terminality already fixes one boundary-complete law on
the law-native four-state assembly, and the reconstructed completion law on that
same selected cut already satisfies the active Part IV law-completion statement.
-/
theorem selectedCutEndpointTerminalitySurface
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.selectedCutEndpointTerminalityTarget) :
    ∃ law :
        CompletionBoundaryLaw
          Index Time Carrier Law
          data.lawNativeConstructiveSectorLaw
          data.lawNativeFourStateAssembly,
      (∀ other :
          CompletionBoundaryLaw
            Index Time Carrier Law
            data.lawNativeConstructiveSectorLaw
            data.lawNativeFourStateAssembly,
        other = law) ∧
      PartIVLawCompletionStatement law.toCompletionLaw.toNaturalOperatorCompletion ∧
      FlagshipBoundaryTarget law.toCompletionLaw.toNoStageCompletionWitness := by
  rcases htarget with ⟨hlaw, hfill⟩
  rcases hlaw with ⟨law, huniqueLaw⟩
  have hsurface := law.alignment.surface
  refine ⟨law, huniqueLaw, hsurface.2.2, ?_⟩
  simpa [CompletionBoundaryLaw.toCompletionLaw,
    TerminalExactificationLaw.lawNativeCompletionLawOfAlignment] using
    hfill law.alignment

/-- The canonical selected completion target contains the same fixed-assembly
law-completion surface through its selected-cut endpoint-terminality
component. -/
theorem selectedCutEndpointTerminalitySurfaceOfCanonicalSelectedCompletionTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalSelectedCompletionTarget) :
    ∃ law :
        CompletionBoundaryLaw
          Index Time Carrier Law
          data.lawNativeConstructiveSectorLaw
          data.lawNativeFourStateAssembly,
      (∀ other :
          CompletionBoundaryLaw
            Index Time Carrier Law
            data.lawNativeConstructiveSectorLaw
            data.lawNativeFourStateAssembly,
        other = law) ∧
      PartIVLawCompletionStatement law.toCompletionLaw.toNaturalOperatorCompletion ∧
      FlagshipBoundaryTarget law.toCompletionLaw.toNoStageCompletionWitness := by
  exact data.selectedCutEndpointTerminalitySurface htarget.2

/-- Selected-cut endpoint terminality already yields one strong microscopic
law on the law-native bridge and physical principle, and therefore the
analytic flagship surface and exact physical equation field. -/
theorem strongMicroscopicLawSurfaceOfSelectedCutEndpointTerminalityTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.selectedCutEndpointTerminalityTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong := by
  exact data.strongMicroscopicLawSurfaceOfCanonicalCompletionBoundaryLawFillTarget htarget

/-- The canonical selected completion target already yields one strong
microscopic package on the same bridge and physical principle, and therefore
the analytic flagship surface and exact physical equation field. -/
theorem candidateLawSurfaceOfCanonicalSelectedCompletionTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalSelectedCompletionTarget) :
    ∃ law :
        CompletionBoundaryLaw
          Index Time Carrier Law
          data.lawNativeConstructiveSectorLaw
          data.lawNativeFourStateAssembly,
      (∀ other :
          CompletionBoundaryLaw
            Index Time Carrier Law
            data.lawNativeConstructiveSectorLaw
            data.lawNativeFourStateAssembly,
        other = law) ∧
      ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
        strong.completionLaw = law.toCompletionLaw ∧
        strong.completionLaw.fourStateLaw.framed.object.bridge =
          data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
        strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
        AnalyticFlagshipSurface strong ∧
        PhysicalEquationSurface strong := by
  exact
    data.candidateLawSurfaceOfCanonicalCompletionBoundaryLawFillTarget
      htarget.2

/-- The canonical selected completion target already yields one strong
microscopic package on the same bridge and physical principle, and therefore
the analytic flagship surface and exact physical equation field. -/
theorem strongMicroscopicLawSurfaceOfCanonicalSelectedCompletionTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalSelectedCompletionTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong := by
  exact
    data.strongMicroscopicLawSurfaceOfCanonicalCompletionBoundaryLawFillTarget
      htarget.2

/-- The honest boundary-form candidate law target already yields one strong
microscopic package on the same bridge and physical principle, and therefore
the analytic flagship surface and exact physical equation field. This is the
law-facing replacement for the stronger endpoint-bundle bottleneck. -/
theorem strongMicroscopicLawSurfaceOfCanonicalBoundaryMicroscopicLawTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalBoundaryMicroscopicLawTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong := by
  rcases htarget with
    ⟨completionLaw, hbridge, hprinciple, _huniqueLaw, hboundary⟩
  let boundaryLaw : BoundaryMicroscopicLaw Index Time Carrier Law :=
    { completionLaw := completionLaw
      boundary := hboundary }
  rcases boundaryLaw.surface with
    ⟨strong, hcompletion, _hcompletionSurface, hanalytic, hphysical⟩
  refine ⟨strong, ?_, ?_, hanalytic, hphysical⟩
  · simpa [hcompletion] using hbridge
  · simpa [hcompletion] using hprinciple

/-- The completion-law-side universal boundary-fill formulation already yields
one strong microscopic package on the same bridge and physical principle, and
therefore the analytic flagship surface and exact physical equation field. -/
theorem strongMicroscopicLawSurfaceOfCanonicalCompletionLawBoundaryFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionLawBoundaryFillTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong := by
  exact
    data.strongMicroscopicLawSurfaceOfCanonicalBoundaryMicroscopicLawTarget
      ((data.canonicalCompletionLawBoundaryFillTarget_iff_canonicalBoundaryMicroscopicLawTarget).1
        htarget)

/-- The honest boundary-form target already upgrades to literal uniqueness of
the candidate-law object itself: on the law-native bridge and physical
principle there is one unique boundary microscopic law, not merely one unique
completion law carrying boundary closure. -/
theorem canonicalBoundaryMicroscopicLawObjectTargetOfCanonicalBoundaryMicroscopicLawTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalBoundaryMicroscopicLawTarget) :
    data.canonicalBoundaryMicroscopicLawObjectTarget := by
  rcases htarget with
    ⟨completionLaw, hbridge, hprinciple, huniqueLaw, hboundary⟩
  let boundaryLaw : BoundaryMicroscopicLaw Index Time Carrier Law :=
    { completionLaw := completionLaw
      boundary := hboundary }
  refine ⟨boundaryLaw, hbridge, hprinciple, ?_⟩
  intro other hotherBridge hotherPrinciple
  have hsameCompletion : other.completionLaw = completionLaw :=
    huniqueLaw other.completionLaw hotherBridge hotherPrinciple
  exact BoundaryMicroscopicLaw.eq_of_completionLaw_eq hsameCompletion

/-- The law-facing completion-law boundary-fill formulation therefore already
upgrades to literal uniqueness of the boundary microscopic law object itself. -/
theorem canonicalBoundaryMicroscopicLawObjectTargetOfCanonicalCompletionLawBoundaryFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalCompletionLawBoundaryFillTarget) :
    data.canonicalBoundaryMicroscopicLawObjectTarget := by
  exact
    data.canonicalBoundaryMicroscopicLawObjectTargetOfCanonicalBoundaryMicroscopicLawTarget
      ((data.canonicalCompletionLawBoundaryFillTarget_iff_canonicalBoundaryMicroscopicLawTarget).1
        htarget)

/-- The completion-law-side boundary-fill bottleneck is exactly equivalent to
the object-level formulation: one unique boundary microscopic law object on the
law-native bridge and physical principle, together with automatic boundary
closure on every aligned completion law. -/
theorem canonicalBoundaryMicroscopicLawObjectFillTarget_iff_canonicalCompletionLawBoundaryFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law) :
    data.canonicalBoundaryMicroscopicLawObjectFillTarget ↔
      data.canonicalCompletionLawBoundaryFillTarget := by
  constructor
  · intro htarget
    rcases htarget with ⟨hobj, hfill⟩
    rcases hobj with ⟨boundaryLaw, hbridge, hprinciple, hunique⟩
    refine ⟨boundaryLaw.completionLaw, hbridge, hprinciple, ?_, hfill⟩
    intro other hotherBridge hotherPrinciple
    have hsame :
        ({ completionLaw := other
           boundary := hfill other hotherBridge hotherPrinciple } :
          BoundaryMicroscopicLaw Index Time Carrier Law) =
        boundaryLaw := by
      exact hunique
        { completionLaw := other
          boundary := hfill other hotherBridge hotherPrinciple }
        hotherBridge hotherPrinciple
    exact congrArg BoundaryMicroscopicLaw.completionLaw hsame
  · intro htarget
    exact
      ⟨data.canonicalBoundaryMicroscopicLawObjectTargetOfCanonicalCompletionLawBoundaryFillTarget
          htarget,
        by
          rcases htarget with ⟨_completionLaw, _hbridge, _hprinciple, _huniqueLaw, hfill⟩
          exact hfill⟩

/-- The selected-completion target therefore already contains the literal
unique fixed-assembly candidate law object on the law-native sector law and
law-native four-state assembly. -/
theorem canonicalCompletionBoundaryLawTargetOfCanonicalSelectedCompletionTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalSelectedCompletionTarget) :
    data.canonicalCompletionBoundaryLawTarget := by
  exact htarget.2.1

/-- Literal object-level uniqueness of the boundary microscopic law already
yields one strong microscopic package on the same bridge and physical
principle, and therefore the analytic flagship surface and exact physical
equation field. -/
theorem strongMicroscopicLawSurfaceOfCanonicalBoundaryMicroscopicLawObjectTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalBoundaryMicroscopicLawObjectTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong := by
  rcases htarget with ⟨boundaryLaw, hbridge, hprinciple, _hunique⟩
  rcases boundaryLaw.surface with
    ⟨strong, hcompletion, _hcompletionSurface, hanalytic, hphysical⟩
  refine ⟨strong, ?_, ?_, hanalytic, hphysical⟩
  · simpa [hcompletion] using hbridge
  · simpa [hcompletion] using hprinciple

/-- The exact object-level bottleneck already yields one strong microscopic
package on the same bridge and physical principle, and therefore the analytic
flagship surface and exact physical equation field. -/
theorem strongMicroscopicLawSurfaceOfCanonicalBoundaryMicroscopicLawObjectFillTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.canonicalBoundaryMicroscopicLawObjectFillTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong := by
  exact
    data.strongMicroscopicLawSurfaceOfCanonicalCompletionLawBoundaryFillTarget
      ((data.canonicalBoundaryMicroscopicLawObjectFillTarget_iff_canonicalCompletionLawBoundaryFillTarget).1
        htarget)

/-- The same strongest law-native flagship witness bridge target already
recovers the strong microscopic package together with its analytic flagship
surface and exact physical equation field. -/
theorem strongMicroscopicLawSurfaceOfFlagshipWitnessBridgeTarget
    {Index Time Carrier Law : Type}
    (data : TerminalExactificationLaw Index Time Carrier Law)
    (htarget : data.flagshipWitnessBridgeTarget) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.toMicroscopicClosureLaw =
        data.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong := by
  rcases
      data.strongMicroscopicLawOfFlagshipWitnessBridgeTarget
        htarget with
    ⟨strong, hstrong⟩
  exact
    ⟨strong,
      hstrong,
      LocalEventFourStateFlagshipLaw.analyticSurface strong,
      LocalEventFourStateFlagshipLaw.physicalEquationSurface strong⟩

end TerminalExactificationLaw

/-- Explicit third Part II physical law above terminal exactification.

After terminal exactification on a selected bridge, the local interaction is
microscopically complete on that same bridge and physical principle: no further
hidden stage and no exogenous constitutive completion remain, and the
law-native fixed four-state assembly carries one boundary-complete completion
law. This is the smallest structured completion-side law strong enough to
recover the endpoint-complete strong microscopic package. -/
structure EndpointCompletionLaw (Index Time Carrier Law : Type) where
  terminal : TerminalExactificationLaw Index Time Carrier Law
  completionBoundary :
    CompletionBoundaryLaw
      Index Time Carrier Law
      terminal.lawNativeConstructiveSectorLaw
      terminal.lawNativeFourStateAssembly

namespace EndpointCompletionLaw

/-- The no-stage completion law carried by the explicit endpoint-completion
surface. -/
abbrev completionLaw
    {Index Time Carrier Law : Type}
    (data : EndpointCompletionLaw Index Time Carrier Law) :
    LocalEventFourStateCompletionLaw Index Time Carrier Law :=
  data.completionBoundary.toCompletionLaw

/-- The carried completion law lives on the same selected bridge as the
law-native microscopic law determined by terminal exactification. -/
theorem completionLaw_sameBridge
    {Index Time Carrier Law : Type}
    (data : EndpointCompletionLaw Index Time Carrier Law) :
    data.completionLaw.fourStateLaw.framed.object.bridge =
      data.terminal.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge := by
  exact
    data.terminal.lawNativeCompletionLawOfAlignment_sameBridge
      data.completionBoundary.alignment

/-- The carried completion law uses the same physical principle as the
law-native microscopic law determined by terminal exactification. -/
theorem completionLaw_samePhysicalPrinciple
    {Index Time Carrier Law : Type}
    (data : EndpointCompletionLaw Index Time Carrier Law) :
    data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
      data.terminal.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple := by
  exact
    data.terminal.lawNativeCompletionLawOfAlignment_samePhysicalPrinciple
      data.completionBoundary.alignment

/-- Endpoint completion already yields one concrete boundary-complete split
completion bridge on the law-native microscopic law. -/
theorem completionBridgeTarget
    {Index Time Carrier Law : Type}
    (data : EndpointCompletionLaw Index Time Carrier Law) :
    data.terminal.flagshipCompletionBridgeTarget := by
  let bridge : NoStageCompletionBridge Index Time Carrier Law :=
    data.terminal.lawNativeFourStateAssembly.toNoStageCompletionBridge
      data.completionBoundary.alignment
  refine ⟨bridge, rfl, ?_⟩
  simpa [bridge, CompletionBoundaryLaw.toCompletionLaw,
    TerminalExactificationLaw.lawNativeCompletionLawOfAlignment,
    NoStageCompletionBridge.toNoStageCompletionWitness,
    LocalEventFourStateCompletionLaw.toNoStageCompletionWitness] using
    data.completionBoundary.boundary

/-- Endpoint completion already yields one endpoint-complete strong microscopic
package on the law-native bridge and physical principle, and therefore the
analytic flagship surface and exact physical equation field. -/
theorem strongMicroscopicLawSurface
    {Index Time Carrier Law : Type}
    (data : EndpointCompletionLaw Index Time Carrier Law) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw = data.completionLaw ∧
      strong.completionLaw.fourStateLaw.framed.object.bridge =
        data.terminal.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.bridge ∧
      strong.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        data.terminal.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong := by
  rcases data.completionBoundary.surface with
    ⟨strong, hcompletion, _hcompletionSurface, hanalytic, hphysical⟩
  refine ⟨strong, hcompletion, ?_, ?_, hanalytic, hphysical⟩
  · simpa [hcompletion] using data.completionLaw_sameBridge
  · simpa [hcompletion] using data.completionLaw_samePhysicalPrinciple

/-- Endpoint completion therefore also recovers the single law-native flagship
completion-bridge target already consumed by the existing Part IV bridge
theorems. -/
theorem strongMicroscopicLawSurfaceOnLawNativeMicroscopicLaw
    {Index Time Carrier Law : Type}
    (data : EndpointCompletionLaw Index Time Carrier Law) :
    ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
      strong.completionLaw.toMicroscopicClosureLaw =
        data.terminal.lawNativeConstructiveSectorLaw.toMicroscopicClosureLaw ∧
      AnalyticFlagshipSurface strong ∧
      PhysicalEquationSurface strong := by
  exact
    data.terminal.strongMicroscopicLawSurfaceOfFlagshipCompletionBridgeTarget
      data.completionBridgeTarget

end EndpointCompletionLaw

namespace DetachedFlagshipPackage

/-- Completion-side strong microscopic package read from the detached flagship
package. -/
def toStrongMicroscopicLaw
    {Index Time Carrier Law : Type}
    (data : DetachedFlagshipPackage Index Time Carrier Law) :
    StrongMicroscopicLaw Index Time Carrier Law where
  completionLaw := data.completionLaw
  endpointWitnesses := data.carrierFaces

/-- Completion-side normal form read from the detached flagship package. -/
def toCoherentRealizationNormalForm
    {Index Time Carrier Law : Type}
    (data : DetachedFlagshipPackage Index Time Carrier Law) :
    CoherentRealizationNormalForm Index Time Carrier Law :=
  data.toStrongMicroscopicLaw

/-- Completion-side normal form carried by the detached flagship package. -/
theorem completionNormalFormSurface
    {Index Time Carrier Law : Type}
    (data : DetachedFlagshipPackage Index Time Carrier Law) :
    PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
      Nonempty
        (PhaseLane.RecognizableIdentity
          Time Carrier Law
          data.carrierFaces.phase.Field
          data.carrierFaces.phase.Scalar) ∧
      Nonempty
        (WaveLane.RecognizableIdentity
          Time Carrier Law
          data.carrierFaces.wave.Field
          data.carrierFaces.wave.Scalar) ∧
      Nonempty
        (GaugeLane.RecognizableIdentity
          Time Carrier Law
          data.carrierFaces.gauge.Field
          data.carrierFaces.gauge.Source) ∧
      Nonempty
        (GeometricLane.RecognizableIdentity
          Time Carrier Law
          data.carrierFaces.geometric.Tensor
          data.carrierFaces.geometric.Scalar) := by
  exact data.toStrongMicroscopicLaw.surface

/-- Detached closure target surface read from the detached flagship package. -/
theorem targetSurface
    {Index Time Carrier Law : Type}
    (data : DetachedFlagshipPackage Index Time Carrier Law) :
    ConstructiveMicroscopicTarget data.completionLaw.toMicroscopicClosureLaw ∧
      OriginClosureTarget data.completionLaw.toMicroscopicClosureLaw ∧
      SectorClosureTarget data.completionLaw.toMicroscopicClosureLaw ∧
      NoStageCompletionTarget data.completionLaw.toMicroscopicClosureLaw ∧
      FlagshipExactTarget data.completionLaw.toMicroscopicClosureLaw ∧
      FlagshipRecognizableTarget data.completionLaw.toMicroscopicClosureLaw := by
  exact data.toStrongMicroscopicLaw.targetSurface

/-- Concrete detached closure-program surface read from the detached flagship
package. -/
theorem fullClosureWitnessSurface
    {Index Time Carrier Law : Type}
    (data : DetachedFlagshipPackage Index Time Carrier Law) :
    ∃ witness : NoStageCompletionWitness data.completionLaw.toMicroscopicClosureLaw,
      ∃ endpointWitnesses :
          FlagshipEndpointWitnesses witness.completionLaw,
        witness.completionLaw.fourStateLaw.framed.object.bridge =
            data.completionLaw.toMicroscopicClosureLaw.bridge ∧
          witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.completionLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
          Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
          Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
          realized_generator_carries_bedrock_law
            data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
          AutonomousHorizon
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
            data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
          horizonFiberInvariant
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
            data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
          PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.phase.Field
              endpointWitnesses.phase.Scalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.wave.Field
              endpointWitnesses.wave.Scalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.gauge.Field
              endpointWitnesses.gauge.Source) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.geometric.Tensor
              endpointWitnesses.geometric.Scalar) := by
  exact data.toStrongMicroscopicLaw.fullClosureWitnessSurface

/-- Concrete detached normal-form surface read from the detached flagship
package. -/
theorem fullNormalFormSurface
    {Index Time Carrier Law : Type}
    (data : DetachedFlagshipPackage Index Time Carrier Law) :
    ∃ witness : NoStageCompletionWitness data.completionLaw.toMicroscopicClosureLaw,
      ∃ normalForms : FlagshipNormalForms Time Carrier Law,
        witness.completionLaw.fourStateLaw.framed.object.bridge =
            data.completionLaw.toMicroscopicClosureLaw.bridge ∧
          witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.completionLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
          Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
          Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
          realized_generator_carries_bedrock_law
            data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
          AutonomousHorizon
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
            data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
          horizonFiberInvariant
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
            data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
          PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              normalForms.PhaseField
              normalForms.PhaseScalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              normalForms.WaveField
              normalForms.WaveScalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GaugeField
              normalForms.GaugeSource) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GeometricTensor
              normalForms.GeometricScalar) := by
  exact data.toStrongMicroscopicLaw.fullNormalFormSurface

/-- Strongest current analytic flagship surface read from the detached
flagship package. -/
theorem analyticSurface
    {Index Time Carrier Law : Type}
    (data : DetachedFlagshipPackage Index Time Carrier Law) :
    AnalyticFlagshipSurface data.toStrongMicroscopicLaw := by
  exact data.toStrongMicroscopicLaw.analyticSurface

/-- One exact physical equation field on `State`, carried by the detached
flagship package. -/
theorem physicalEquationSurface
    {Index Time Carrier Law : Type}
    (data : DetachedFlagshipPackage Index Time Carrier Law) :
    PhysicalEquationSurface data.toStrongMicroscopicLaw := by
  exact data.toStrongMicroscopicLaw.physicalEquationSurface

end DetachedFlagshipPackage

namespace CoherentRealizationLaw

/-- The coherent realization law already carries one exact visible law on one
same coherent bundle, read as the observable dynamics on the realized cut
class. -/
theorem realizationSurface
    {Index Time Carrier Law : Type}
    (data : CoherentRealizationLaw Index Time Carrier Law) :
    exactVisibleOnCut
        (data.selectedLaw.selection.realization.tower.π
          data.selectedLaw.selection.horizon)
        (selected_observed_law
          data.selectedLaw.selection).op ∧
      data.observableDynamicsExactlySelectedLaw ∧
      data.sameCoherentBundle ∧
      data.observerCovariance := by
  have h := physical_realization_principle data
  rcases h with
    ⟨hexact, _hclosed, _hnoConst, _happarent, hobs, hbundle, hcov, _hleast,
      _hexchange, _hzero, _hreturn, _hforcing, _hirr, _hloc, _helim⟩
  exact ⟨hexact, hobs, hbundle, hcov⟩

/-- Same-bundle conservation surface of the coherent realization law: visible
source is exchange-boundary reentry, closed realized systems have no net
internal visible creation, and all observable forcing/irreversibility is
return-side data of that same coherent bundle. -/
theorem exchangeReturnSurface
    {Index Time Carrier Law : Type}
    (data : CoherentRealizationLaw Index Time Carrier Law) :
    data.visibleSourcesOnlyExchangeBoundaryReentry ∧
      data.zeroNetInternalCreationOnClosedSystems ∧
      data.onlyReturnActs ∧
      data.visibleForcingIsReturnedResidual ∧
      data.observableIrreversibilityIsUnrecoveredResidual ∧
      data.residualLocalizesOnUniqueInterface ∧
      data.selectedLawObtainedByResidualElimination := by
  exact
    ⟨data.visibleSourcesOnlyExchangeBoundaryReentry_valid,
      data.zeroNetInternalCreationOnClosedSystems_valid,
      data.onlyReturnActs_valid,
      data.visibleForcingIsReturnedResidual_valid,
      data.observableIrreversibilityIsUnrecoveredResidual_valid,
      data.residualLocalizesOnUniqueInterface_valid,
      data.selectedLawObtainedByResidualElimination_valid⟩

/-- Self-sufficient selected-cut closure surface of the coherent realization
law. -/
theorem selectedCutCompletionSurface
    {Index Time Carrier Law : Type}
    (data : CoherentRealizationLaw Index Time Carrier Law) :
    exactVisibleOnCut
        (data.selectedLaw.selection.realization.tower.π
          data.selectedLaw.selection.horizon)
        (selected_observed_law
          data.selectedLaw.selection).op ∧
      data.intrinsicallyClosedOnLeastMotionCut ∧
      data.noExogenousConstitutiveCompletion ∧
      data.apparentConstitutiveTermsAreReturnedResidual := by
  exact
    ⟨data.exactVisibleSelectedLawOnLeastMotionCut,
      data.intrinsicallyClosedOnLeastMotionCut_valid,
      data.noExogenousConstitutiveCompletion_valid,
      data.apparentConstitutiveTermsAreReturnedResidual_valid⟩

/-- The least-motion cut is not a second primitive law-side input on the public
surface. It is the canonical representative theorem already carried by the
realized faithful cut class of the same coherent realization law. -/
theorem canonicalRepresentativeSurface
    {Index Time Carrier Law : Type}
    (data : CoherentRealizationLaw Index Time Carrier Law) :
    data.observerCovariance ∧
      data.leastMotionFaithfulCutUnique := by
  exact
    ⟨data.observerCovariance_valid,
      data.leastMotionFaithfulCutUnique_valid⟩

end CoherentRealizationLaw

namespace CoherentRealizationNormalForm

/-- The completion-side normal form is exactly the endpoint-complete detached
strong microscopic package. -/
theorem surface
    {Index Time Carrier Law : Type}
    (data : CoherentRealizationNormalForm Index Time Carrier Law) :
    PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
      Nonempty
        (PhaseLane.RecognizableIdentity
          Time Carrier Law
          data.endpointWitnesses.phase.Field
          data.endpointWitnesses.phase.Scalar) ∧
      Nonempty
        (WaveLane.RecognizableIdentity
          Time Carrier Law
          data.endpointWitnesses.wave.Field
          data.endpointWitnesses.wave.Scalar) ∧
      Nonempty
        (GaugeLane.RecognizableIdentity
          Time Carrier Law
          data.endpointWitnesses.gauge.Field
          data.endpointWitnesses.gauge.Source) ∧
      Nonempty
        (GeometricLane.RecognizableIdentity
          Time Carrier Law
          data.endpointWitnesses.geometric.Tensor
          data.endpointWitnesses.geometric.Scalar) := by
  exact StrongMicroscopicLaw.surface data

/-- The completion-side normal form closes the detached closure target surface.
-/
theorem targetSurface
    {Index Time Carrier Law : Type}
    (data : CoherentRealizationNormalForm Index Time Carrier Law) :
    ConstructiveMicroscopicTarget data.completionLaw.toMicroscopicClosureLaw ∧
      OriginClosureTarget data.completionLaw.toMicroscopicClosureLaw ∧
      SectorClosureTarget data.completionLaw.toMicroscopicClosureLaw ∧
      NoStageCompletionTarget data.completionLaw.toMicroscopicClosureLaw ∧
      FlagshipExactTarget data.completionLaw.toMicroscopicClosureLaw ∧
      FlagshipRecognizableTarget data.completionLaw.toMicroscopicClosureLaw := by
  exact StrongMicroscopicLaw.targetSurface data

/-- Concrete full detached closure-program surface carried by the completion-side
normal form. -/
theorem fullClosureWitnessSurface
    {Index Time Carrier Law : Type}
    (data : CoherentRealizationNormalForm Index Time Carrier Law) :
    ∃ witness : NoStageCompletionWitness data.completionLaw.toMicroscopicClosureLaw,
      ∃ endpointWitnesses :
          FlagshipEndpointWitnesses witness.completionLaw,
        witness.completionLaw.fourStateLaw.framed.object.bridge =
            data.completionLaw.toMicroscopicClosureLaw.bridge ∧
          witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.completionLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
          Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
          Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
          realized_generator_carries_bedrock_law
            data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
          AutonomousHorizon
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
            data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
          horizonFiberInvariant
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
            data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
          PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.phase.Field
              endpointWitnesses.phase.Scalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.wave.Field
              endpointWitnesses.wave.Scalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.gauge.Field
              endpointWitnesses.gauge.Source) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              endpointWitnesses.geometric.Tensor
              endpointWitnesses.geometric.Scalar) := by
  exact StrongMicroscopicLaw.fullClosureWitnessSurface data

/-- Concrete full detached normal-form surface carried by the completion-side
normal form. -/
theorem fullNormalFormSurface
    {Index Time Carrier Law : Type}
    (data : CoherentRealizationNormalForm Index Time Carrier Law) :
    ∃ witness : NoStageCompletionWitness data.completionLaw.toMicroscopicClosureLaw,
      ∃ normalForms : FlagshipNormalForms Time Carrier Law,
        witness.completionLaw.fourStateLaw.framed.object.bridge =
            data.completionLaw.toMicroscopicClosureLaw.bridge ∧
          witness.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            data.completionLaw.toMicroscopicClosureLaw.physicalPrinciple ∧
          Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
          Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
          realized_generator_carries_bedrock_law
            data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
          AutonomousHorizon
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
            data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
          horizonFiberInvariant
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.realization.tower
            data.completionLaw.toMicroscopicClosureLaw.bridge.selectedBridge.observer.selection.horizon
            data.completionLaw.toMicroscopicClosureLaw.bridge.generator ∧
          PartIVLawCompletionStatement witness.completionLaw.toNaturalOperatorCompletion ∧
          Nonempty
            (PhaseLane.RecognizableIdentity
              Time Carrier Law
              normalForms.PhaseField
              normalForms.PhaseScalar) ∧
          Nonempty
            (WaveLane.RecognizableIdentity
              Time Carrier Law
              normalForms.WaveField
              normalForms.WaveScalar) ∧
          Nonempty
            (GaugeLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GaugeField
              normalForms.GaugeSource) ∧
          Nonempty
            (GeometricLane.RecognizableIdentity
              Time Carrier Law
              normalForms.GeometricTensor
              normalForms.GeometricScalar) := by
  exact StrongMicroscopicLaw.fullNormalFormSurface data

/-- Strongest current analytic flagship surface carried by the completion-side
normal form. -/
theorem analyticSurface
    {Index Time Carrier Law : Type}
    (data : CoherentRealizationNormalForm Index Time Carrier Law) :
    AnalyticFlagshipSurface data := by
  exact LocalEventFourStateFlagshipLaw.analyticSurface data

/-- One exact physical equation field on `State`, carried by the completion-side
normal form. -/
theorem physicalEquationSurface
    {Index Time Carrier Law : Type}
    (data : CoherentRealizationNormalForm Index Time Carrier Law) :
    PhysicalEquationSurface data := by
  exact LocalEventFourStateFlagshipLaw.physicalEquationSurface data

end CoherentRealizationNormalForm

end ClosureCurrent

end CoherenceCalculus
