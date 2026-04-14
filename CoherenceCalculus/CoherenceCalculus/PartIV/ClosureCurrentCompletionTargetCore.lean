import CoherenceCalculus.PartIV.ClosureCurrentOriginClosureCore
import CoherenceCalculus.PartIV.ClosureCurrentFlagshipCompletionCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentCompletionTargetCore

Later theorem targets above the smaller microscopic closure law.

`ClosureCurrentOriginClosureCore` states the first two upstream targets: forcing
the selected-bundle/readout witness and the intrinsic sector-generation witness
from one smaller microscopic closure law. This file isolates the next two
remaining law-side seams:

* `NoStageCompletionWitness law` is the target saying that the same microscopic
  law already carries one no-stage local-event four-state completion law on the
  same selected bridge and physical principle;
* `Phase/Wave/Gauge/GeometricEndpointWitnessTarget data` are the four exact
  lane-wise flagship-side targets above one fixed no-stage completion witness;
* `EndpointWitnessTarget data` is the aggregate target saying that such a
  witness already carries the exact flagship endpoint witness bundles on its
  own law-native selected bundle.

Supplying those targets does not prove the microscopic closure theorem program.
It states the remaining completion-side and flagship-side theorem obligations
exactly, and shows how they close the present detached flagship surface once
they are available.
-/

namespace ClosureCurrent

/-- Completion-side theorem witness above one smaller microscopic closure law.
This is not a new microscopic primitive. It is the exact target asserting that
the law already carries one no-stage local-event four-state completion package
on the same selected bridge and physical principle. -/
structure NoStageCompletionWitness
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) where
  completionLaw : LocalEventFourStateCompletionLaw Index Time Carrier Law
  sameBridge :
    completionLaw.fourStateLaw.framed.object.bridge = law.bridge
  samePhysicalPrinciple :
    completionLaw.fourStateLaw.framed.object.physicalPrinciple =
      law.physicalPrinciple

/-- The theorem target saying that one smaller microscopic closure law already
forces a no-stage local-event four-state completion law on the same selected
bridge and physical principle. -/
def NoStageCompletionTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) : Prop :=
  Nonempty (NoStageCompletionWitness law)

/-- Exact phase endpoint-witness target above one fixed no-stage completion
witness. -/
def PhaseEndpointWitnessTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law) : Prop :=
  Nonempty (PhaseEndpointWitness data.completionLaw)

/-- Exact wave endpoint-witness target above one fixed no-stage completion
witness. -/
def WaveEndpointWitnessTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law) : Prop :=
  Nonempty (WaveEndpointWitness data.completionLaw)

/-- Exact gauge endpoint-witness target above one fixed no-stage completion
witness. -/
def GaugeEndpointWitnessTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law) : Prop :=
  Nonempty (GaugeEndpointWitness data.completionLaw)

/-- Exact geometric endpoint-witness target above one fixed no-stage
completion witness. -/
def GeometricEndpointWitnessTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law) : Prop :=
  Nonempty (GeometricEndpointWitness data.completionLaw)

/-- The theorem target saying that a no-stage completion witness already forces
the exact flagship endpoint witness bundles on its own law-native selected
bundle. -/
def EndpointWitnessTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law) : Prop :=
  Nonempty (FlagshipEndpointWitnesses data.completionLaw)

/-- Fixed-witness strong-law extension target. It says that the given no-stage
completion witness already extends to some endpoint-complete strong microscopic
law on that same completion law. -/
def StrongMicroscopicExtensionTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law) : Prop :=
  ∃ strong : StrongMicroscopicLaw Index Time Carrier Law,
    strong.completionLaw = data.completionLaw

/-- Existence-level flagship target above one smaller microscopic closure law.
This is the concrete target matched by an endpoint-complete detached flagship
law: the same microscopic law carries some no-stage completion witness, and
that witness carries its own endpoint witness bundle.

Unlike the stronger universal endpoint-target input used by
`MicroscopicClosureLaw.fullClosureProgramSurface`, this target is aligned with
what one concrete flagship witness can realize directly. -/
def FlagshipTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) : Prop :=
  ∃ data : NoStageCompletionWitness law, EndpointWitnessTarget data

/-- Exact recognizable flagship forms carried by one no-stage completion
witness. Unlike `FlagshipEndpointWitnesses`, this package records only the
final recognizable identities, not the auxiliary endpoint frontier data used
to construct them. It is the direct normal-form target suggested by the
existing endpoint-rigidity / orthogonality / duality machinery. -/
structure FlagshipNormalForms
    (Time Carrier Law : Type) where
  PhaseField : Type
  PhaseScalar : Type
  phase :
    Nonempty
      (PhaseLane.RecognizableIdentity
        Time Carrier Law PhaseField PhaseScalar)
  WaveField : Type
  WaveScalar : Type
  wave :
    Nonempty
      (WaveLane.RecognizableIdentity
        Time Carrier Law WaveField WaveScalar)
  GaugeField : Type
  GaugeSource : Type
  gauge :
    Nonempty
      (GaugeLane.RecognizableIdentity
        Time Carrier Law GaugeField GaugeSource)
  GeometricTensor : Type
  GeometricScalar : Type
  geometric :
    Nonempty
      (GeometricLane.RecognizableIdentity
        Time Carrier Law GeometricTensor GeometricScalar)

/-- Surface theorem for the direct recognizable flagship forms. -/
theorem FlagshipNormalForms.surface
    {Time Carrier Law : Type}
    (data : FlagshipNormalForms Time Carrier Law) :
    Nonempty
        (PhaseLane.RecognizableIdentity
          Time Carrier Law data.PhaseField data.PhaseScalar) ∧
      Nonempty
        (WaveLane.RecognizableIdentity
          Time Carrier Law data.WaveField data.WaveScalar) ∧
      Nonempty
        (GaugeLane.RecognizableIdentity
          Time Carrier Law data.GaugeField data.GaugeSource) ∧
      Nonempty
        (GeometricLane.RecognizableIdentity
          Time Carrier Law data.GeometricTensor data.GeometricScalar) := by
  exact
    ⟨data.phase,
      data.wave,
      data.gauge,
      data.geometric⟩

/-- Direct normal-form target above one smaller microscopic closure law. This
asks only for one no-stage completion witness carrying the recognizable
Schr\"odinger, wave/Klein--Gordon, Maxwell, and Einstein forms, without
insisting that the auxiliary endpoint witness bundles are themselves the
primitive target. -/
def NormalFormTarget
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law) : Prop :=
  ∃ _data : NoStageCompletionWitness law,
    Nonempty (FlagshipNormalForms Time Carrier Law)

/-- Surface theorem for the no-stage completion witness. Once this target is
met, the no-stage completion law already reconstructs the active Part IV
completion surface on the same selected bridge and physical principle as the
smaller microscopic closure law. -/
theorem NoStageCompletionWitness.surface
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law) :
    data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
      data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        law.physicalPrinciple ∧
      PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion := by
  obtain
    ⟨_hbundle, _hsector, _hbedrock, _haut, _hfiber, _hstate, _hreduced,
      _hschur, hcompletion⟩ := data.completionLaw.attachedSurface
  exact
    ⟨data.sameBridge,
      data.samePhysicalPrinciple,
      hcompletion⟩

/-- The four exact lane-specific endpoint-witness targets above one fixed
no-stage completion witness reassemble the aggregate endpoint-witness target.
-/
theorem NoStageCompletionWitness.endpointWitnessTargetOfLaneTargets
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hphase : PhaseEndpointWitnessTarget data)
    (hwave : WaveEndpointWitnessTarget data)
    (hgauge : GaugeEndpointWitnessTarget data)
    (hgeometric : GeometricEndpointWitnessTarget data) :
    EndpointWitnessTarget data := by
  rcases hphase with ⟨phase⟩
  rcases hwave with ⟨wave⟩
  rcases hgauge with ⟨gauge⟩
  rcases hgeometric with ⟨geometric⟩
  exact
    ⟨{ phase := phase
       wave := wave
       gauge := gauge
       geometric := geometric }⟩

/-- Once the endpoint-witness target is met, the corresponding endpoint-complete
flagship surface exists on the same no-stage completion witness and closes the
remaining textbook flagship seam. -/
theorem NoStageCompletionWitness.flagshipSurface
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hendpoint : EndpointWitnessTarget data) :
    ∃ endpointWitnesses : FlagshipEndpointWitnesses data.completionLaw,
      PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
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
  rcases hendpoint with ⟨endpointWitnesses⟩
  let flagship : LocalEventFourStateFlagshipLaw Index Time Carrier Law :=
    { completionLaw := data.completionLaw
      endpointWitnesses := endpointWitnesses }
  have hsurface := flagship.surface
  exact
    ⟨endpointWitnesses,
      hsurface.1,
      hsurface.2.1,
      hsurface.2.2.1,
      hsurface.2.2.2.1,
      hsurface.2.2.2.2⟩

/-- An aggregate endpoint-witness target on one fixed no-stage completion
witness already extends to an endpoint-complete strong microscopic law on that
same completion law. -/
theorem NoStageCompletionWitness.strongMicroscopicExtensionTargetOfEndpointWitnessTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hendpoint : EndpointWitnessTarget data) :
    StrongMicroscopicExtensionTarget data := by
  rcases hendpoint with ⟨endpointWitnesses⟩
  exact
    ⟨{ completionLaw := data.completionLaw
       endpointWitnesses := endpointWitnesses },
      rfl⟩

/-- Conversely, any endpoint-complete strong microscopic law extending the
same completion law already yields the aggregate endpoint-witness target on
that fixed no-stage completion witness. -/
theorem NoStageCompletionWitness.endpointWitnessTargetOfStrongMicroscopicExtensionTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hext : StrongMicroscopicExtensionTarget data) :
    EndpointWitnessTarget data := by
  rcases hext with ⟨strong, hcompletion⟩
  dsimp [EndpointWitnessTarget]
  rw [← hcompletion]
  exact ⟨strong.endpointWitnesses⟩

/-- On one fixed no-stage completion witness, aggregate endpoint-witness fill
is equivalent to strong microscopic extension on that same completion law. -/
theorem NoStageCompletionWitness.endpointWitnessTarget_iff_strongMicroscopicExtensionTarget
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law) :
    EndpointWitnessTarget data ↔ StrongMicroscopicExtensionTarget data := by
  constructor
  · exact data.strongMicroscopicExtensionTargetOfEndpointWitnessTarget
  · exact data.endpointWitnessTargetOfStrongMicroscopicExtensionTarget

/-- A no-stage completion witness is determined by its completion law. The
bridge and physical-principle fields are propositional alignment witnesses, so
once the completion law agrees the witnesses themselves agree. -/
theorem NoStageCompletionWitness.eq_of_completionLaw_eq
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    {data other : NoStageCompletionWitness law}
    (hcompletion : data.completionLaw = other.completionLaw) :
    data = other := by
  cases data
  cases other
  cases hcompletion
  simp

/-- The four exact lane-specific endpoint-witness targets above one fixed
no-stage completion witness already recover the endpoint-complete flagship
surface on that same witness. -/
theorem NoStageCompletionWitness.flagshipSurfaceOfLaneTargets
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (hphase : PhaseEndpointWitnessTarget data)
    (hwave : WaveEndpointWitnessTarget data)
    (hgauge : GaugeEndpointWitnessTarget data)
    (hgeometric : GeometricEndpointWitnessTarget data) :
    ∃ endpointWitnesses : FlagshipEndpointWitnesses data.completionLaw,
      PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
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
  exact
    data.flagshipSurface
      (data.endpointWitnessTargetOfLaneTargets
        hphase hwave hgauge hgeometric)

/-- Once one no-stage completion witness carries the direct recognizable
flagship forms, the textbook flagship identities already hold on that same
witness with no endpoint-bundle primitive in the conclusion. -/
theorem NoStageCompletionWitness.normalFormSurface
    {Index Time Carrier Law : Type}
    {law : MicroscopicClosureLaw Index Time Carrier Law}
    (data : NoStageCompletionWitness law)
    (normalForms : FlagshipNormalForms Time Carrier Law) :
    data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
      data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
        law.physicalPrinciple ∧
      PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
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
  have hsurface := data.surface
  have hnormal := normalForms.surface
  exact
    ⟨hsurface.1,
      hsurface.2.1,
      hsurface.2.2,
      hnormal.1,
      hnormal.2.1,
      hnormal.2.2.1,
      hnormal.2.2.2⟩

/-- If the no-stage completion target is met for a smaller microscopic closure
law, the active Part IV completion surface follows on one completion witness
carried by that same law. -/
theorem MicroscopicClosureLaw.completionTargetSurface
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hcompletion : NoStageCompletionTarget law) :
    ∃ data : NoStageCompletionWitness law,
      data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
        data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
          law.physicalPrinciple ∧
        PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion := by
  rcases hcompletion with ⟨data⟩
  exact ⟨data, data.surface⟩

/-- If both the no-stage completion target and the endpoint-witness target are
met, the endpoint-complete flagship surface follows on one law-native flagship
law carried by the same smaller microscopic closure law. -/
theorem MicroscopicClosureLaw.flagshipTargetSurface
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hcompletion : NoStageCompletionTarget law)
    (hendpoint :
      ∀ data : NoStageCompletionWitness law, EndpointWitnessTarget data) :
    ∃ data : NoStageCompletionWitness law,
      ∃ endpointWitnesses : FlagshipEndpointWitnesses data.completionLaw,
        PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
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
  rcases hcompletion with ⟨data⟩
  have hsurface := data.flagshipSurface (hendpoint data)
  exact
    ⟨data,
      hsurface⟩

/-- Existence-level flagship surface above one smaller microscopic closure law.
If the law carries one no-stage completion witness together with endpoint
witness data on that same witness, then the endpoint-complete flagship surface
already follows. This is the theorem shape matched by a concrete detached
flagship law. -/
theorem MicroscopicClosureLaw.flagshipWitnessSurface
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hflagship : FlagshipTarget law) :
    ∃ data : NoStageCompletionWitness law,
      ∃ endpointWitnesses : FlagshipEndpointWitnesses data.completionLaw,
        data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
          data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple ∧
          PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
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
  rcases hflagship with ⟨data, hendpoint⟩
  rcases data.flagshipSurface hendpoint with
    ⟨endpointWitnesses, hcompletion, hphase, hwave, hgauge, hgeometric⟩
  exact
    ⟨data,
      endpointWitnesses,
      data.sameBridge,
      data.samePhysicalPrinciple,
      hcompletion,
      hphase,
      hwave,
      hgauge,
      hgeometric⟩

/-- Direct recognizable flagship surface above one smaller microscopic closure
law. This is the sharper normal-form target: one law-native no-stage
completion witness carries the recognizable flagship equations directly,
without first asking for the auxiliary endpoint witness bundles as part of the
abstract target. -/
theorem MicroscopicClosureLaw.normalFormTargetSurface
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (hnormal : NormalFormTarget law) :
    ∃ data : NoStageCompletionWitness law,
      ∃ normalForms : FlagshipNormalForms Time Carrier Law,
        data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
          data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple ∧
          PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
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
  rcases hnormal with ⟨data, normalForms⟩
  rcases normalForms with ⟨normalForms⟩
  exact
    ⟨data,
      normalForms,
      data.normalFormSurface normalForms⟩

/-- End-to-end theorem-program surface above one smaller microscopic closure
law. If the origin-closure, sector-closure, no-stage completion, and endpoint-
witness targets are all met, then the detached flagship surface is recovered on
the same microscopic law. This theorem is purely organizational: it does not
prove any of those targets, but it states the full closure program as one exact
Lean proposition. -/
theorem MicroscopicClosureLaw.fullClosureProgramSurface
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (horigin : OriginClosureTarget law)
    (hsector : SectorClosureTarget law)
    (hcompletion : NoStageCompletionTarget law)
    (hendpoint :
      ∀ data : NoStageCompletionWitness law, EndpointWitnessTarget data) :
    ∃ data : NoStageCompletionWitness law,
      ∃ endpointWitnesses : FlagshipEndpointWitnesses data.completionLaw,
        data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
          data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple ∧
          Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
          Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
          realized_generator_carries_bedrock_law law.bridge.generator ∧
          AutonomousHorizon
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          horizonFiberInvariant
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
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
  obtain ⟨hbundle, hstep3, hbedrock, haut, hfiber, _hgenmin, _hprofile⟩ :=
    law.sectorTargetSurface horigin hsector
  rcases hcompletion with ⟨data⟩
  rcases hendpoint data with ⟨endpointWitnesses⟩
  let flagship : LocalEventFourStateFlagshipLaw Index Time Carrier Law :=
    { completionLaw := data.completionLaw
      endpointWitnesses := endpointWitnesses }
  have hflagship := flagship.surface
  exact
    ⟨data,
      endpointWitnesses,
      data.sameBridge,
      data.samePhysicalPrinciple,
      hbundle,
      hstep3,
      hbedrock,
      haut,
      hfiber,
      hflagship.1,
      hflagship.2.1,
      hflagship.2.2.1,
      hflagship.2.2.2.1,
      hflagship.2.2.2.2⟩

/-- Existence-level full closure-program surface above one smaller microscopic
closure law. This is the concrete form matched by one detached flagship law:
origin and sector closure remain target-level hypotheses, but the flagship side
now asks only for one law-native completion witness carrying one endpoint
witness bundle, rather than a universal endpoint target over every completion
witness. -/
theorem MicroscopicClosureLaw.fullClosureWitnessSurface
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (horigin : OriginClosureTarget law)
    (hsector : SectorClosureTarget law)
    (hflagship : FlagshipTarget law) :
    ∃ data : NoStageCompletionWitness law,
      ∃ endpointWitnesses : FlagshipEndpointWitnesses data.completionLaw,
        data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
          data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple ∧
          Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
          Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
          realized_generator_carries_bedrock_law law.bridge.generator ∧
          AutonomousHorizon
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          horizonFiberInvariant
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
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
  obtain ⟨hbundle, hstep3, hbedrock, haut, hfiber, _hgenmin, _hprofile⟩ :=
    law.sectorTargetSurface horigin hsector
  rcases law.flagshipWitnessSurface hflagship with
    ⟨data, endpointWitnesses, hbridge, hprinciple, hcompletion, hphase, hwave,
      hgauge, hgeometric⟩
  exact
    ⟨data,
      endpointWitnesses,
      hbridge,
      hprinciple,
      hbundle,
      hstep3,
      hbedrock,
      haut,
      hfiber,
      hcompletion,
      hphase,
      hwave,
      hgauge,
      hgeometric⟩

/-- Existence-level full closure surface through the direct recognizable
normal-form target. If origin closure, sector closure, and one direct normal-
form witness are available, then the smaller microscopic closure law already
carries the active completion surface together with the recognizable flagship
equations. -/
theorem MicroscopicClosureLaw.fullNormalFormSurface
    {Index Time Carrier Law : Type}
    (law : MicroscopicClosureLaw Index Time Carrier Law)
    (horigin : OriginClosureTarget law)
    (hsector : SectorClosureTarget law)
    (hnormal : NormalFormTarget law) :
    ∃ data : NoStageCompletionWitness law,
      ∃ normalForms : FlagshipNormalForms Time Carrier Law,
        data.completionLaw.fourStateLaw.framed.object.bridge = law.bridge ∧
          data.completionLaw.fourStateLaw.framed.object.physicalPrinciple =
            law.physicalPrinciple ∧
          Nonempty (IntrinsicSelectedBundleExistence Time Carrier Law) ∧
          Nonempty (IntrinsicSectorGeneration Time Carrier Law) ∧
          realized_generator_carries_bedrock_law law.bridge.generator ∧
          AutonomousHorizon
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          horizonFiberInvariant
            law.bridge.selectedBridge.observer.selection.realization.tower
            law.bridge.selectedBridge.observer.selection.horizon
            law.bridge.generator ∧
          PartIVLawCompletionStatement data.completionLaw.toNaturalOperatorCompletion ∧
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
  obtain ⟨hbundle, hstep3, hbedrock, haut, hfiber, _hgenmin, _hprofile⟩ :=
    law.sectorTargetSurface horigin hsector
  rcases law.normalFormTargetSurface hnormal with
    ⟨data, normalForms, hbridge, hprinciple, hcompletion, hphase, hwave, hgauge,
      hgeometric⟩
  exact
    ⟨data,
      normalForms,
      hbridge,
      hprinciple,
      hbundle,
      hstep3,
      hbedrock,
      haut,
      hfiber,
      hcompletion,
      hphase,
      hwave,
      hgauge,
      hgeometric⟩

end ClosureCurrent

end CoherenceCalculus
