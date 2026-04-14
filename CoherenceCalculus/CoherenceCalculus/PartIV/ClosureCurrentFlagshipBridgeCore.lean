import CoherenceCalculus.PartIV.ClosureCurrentContinuumAttachmentCore
import CoherenceCalculus.PartIV.FlagshipCore

namespace CoherenceCalculus

/-!
# PartIV.ClosureCurrentFlagshipBridgeCore

Law-native bridge from the detached no-stage completion law to the recognizable
flagship identities.

`ClosureCurrentContinuumAttachmentCore` closes the detached lane back into the
active Part IV completion surface from one no-stage local-event four-state
completion law. The remaining question is then not whether the detached law can
reach the selected-cut completion surface, but whether the recognizable
flagship identities are already forced there.

This file keeps that bridge honest and one-way. It does not redesign any
flagship lane. Instead, it takes the existing endpoint-frontier data already
used in the phase, wave, gauge, and geometric lanes, fixes the physical
selected law to the one carried by the no-stage completion law, and reads off
the recognizable witnesses from the corresponding lane theorems.

The hydrodynamic lane is intentionally not bundled here: at present it does not
yet expose the same selected-closure frontier theorem surface as the other four
textbook flagship lanes.
-/

namespace ClosureCurrent

/-- The intrinsically selected bundle carried by a no-stage local-event
four-state completion law. This is the law-native selected-bundle surface
recovered from the detached completion package itself. -/
def LocalEventFourStateCompletionLaw.selectedBundle
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) :
    IntrinsicSelectedBundleExistence Time Carrier Law :=
  data.toSelectedBundleForcing.toIntrinsicSelectedBundleExistence

/-- Phase endpoint frontier read on the same selected datum as the no-stage
completion law. -/
structure PhaseFrontier
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) where
  Field : Type
  Scalar : Type
  Channel : Type
  frontier :
    PhaseLane.EndpointFoundationFrontierData
      Time Carrier Law Field Scalar Index Channel
  readOnSelectedBundle :
    data.selectedBundle.phaseCarrierReadOnSelectedBundle
      frontier.collapse.law.observer

/-- Wave endpoint frontier read on the same selected datum as the no-stage
completion law. -/
structure WaveFrontier
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) where
  Field : Type
  Scalar : Type
  System : Type
  Vertex : Type
  PhaseClass : Type
  ClosureClass : Type
  WaveIndex : Type
  tower : HorizonTower
  frontier :
    WaveLane.EndpointRecursionKernelFrontierData
      Time Carrier Law Field Scalar System Vertex
      PhaseClass ClosureClass WaveIndex tower
  readOnSelectedBundle :
    data.selectedBundle.waveCarrierReadOnSelectedBundle
      frontier.frontier.frontier.collapse.law.observer

/-- Gauge endpoint frontier read on the same selected datum as the no-stage
completion law. -/
structure GaugeFrontier
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) where
  Field : Type
  Source : Type
  Vertex : Type
  frontier :
    GaugeLane.EndpointFoundationFrontierData
      Time Carrier Law Field Source Vertex
  readOnSelectedBundle :
    data.selectedBundle.gaugeCarrierReadOnSelectedBundle
      frontier.collapse.law.observer

/-- Geometric endpoint frontier read on the same selected datum as the
no-stage completion law. -/
structure GeometricFrontier
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) where
  Tensor : Type
  Scalar : Type
  Group : Type
  frontier :
    GeometricLane.EndpointFoundationFrontierData
      Time Carrier Law Tensor Scalar Group
  readOnSelectedBundle :
    data.selectedBundle.geometricCarrierReadOnSelectedBundle
      frontier.collapse.law.observer

/-- The four textbook flagship endpoint frontiers read on the same selected
datum as the no-stage completion law. -/
structure FlagshipFrontiers
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law) where
  phase : PhaseFrontier data
  wave : WaveFrontier data
  gauge : GaugeFrontier data
  geometric : GeometricFrontier data

/-- Turn a detached phase frontier into the native selected-bundle closure
package used by the flagship phase lane. -/
def PhaseFrontier.toBundleIdentification
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law)
    (frontier : PhaseFrontier data) :
    PhaseLane.SelectedBundleClosureIdentificationData
      Time Carrier Law frontier.Field frontier.Scalar Index frontier.Channel where
  frontier := frontier.frontier
  selectedBundle := data.selectedBundle
  phaseCarrierReadOnSelectedBundle := frontier.readOnSelectedBundle

/-- Turn a detached wave frontier into the native selected-bundle closure
package used by the flagship wave lane. -/
def WaveFrontier.toBundleIdentification
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law)
    (frontier : WaveFrontier data) :
    WaveLane.SelectedBundleClosureIdentificationData
      Time Carrier Law frontier.Field frontier.Scalar frontier.System
      frontier.Vertex frontier.PhaseClass frontier.ClosureClass
      frontier.WaveIndex frontier.tower where
  frontier := frontier.frontier
  selectedBundle := data.selectedBundle
  waveCarrierReadOnSelectedBundle := frontier.readOnSelectedBundle

/-- Turn a detached gauge frontier into the native selected-bundle closure
package used by the flagship gauge lane. -/
def GaugeFrontier.toBundleIdentification
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law)
    (frontier : GaugeFrontier data) :
    GaugeLane.SelectedBundleClosureIdentificationData
      Time Carrier Law frontier.Field frontier.Source frontier.Vertex where
  frontier := frontier.frontier
  selectedBundle := data.selectedBundle
  gaugeCarrierReadOnSelectedBundle := frontier.readOnSelectedBundle

/-- Turn a detached geometric frontier into the native selected-bundle closure
package used by the flagship geometric lane. -/
def GeometricFrontier.toBundleIdentification
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law)
    (frontier : GeometricFrontier data) :
    GeometricLane.SelectedBundleClosureIdentificationData
      Time Carrier Law frontier.Tensor frontier.Scalar frontier.Group where
  frontier := frontier.frontier
  selectedBundle := data.selectedBundle
  geometricCarrierReadOnSelectedBundle := frontier.readOnSelectedBundle

/-- On a phase frontier read from the same selected datum as the no-stage
completion law, the recognizable Schrödinger identity is forced directly from
the law-native physical selected closure law. -/
  theorem LocalEventFourStateCompletionLaw.phaseSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law)
    (frontier : PhaseFrontier data) :
    let cls := frontier.frontier.collapse.law.observer.continuumClass
    let target := data.selectedBundle.physicalPrinciple.selectedLaw.selectedClosureLaw
    ForcedContinuumLaw cls target ∧
      Nonempty
        (PhaseLane.RecognizableIdentity
          Time Carrier Law frontier.Field frontier.Scalar) := by
  have hclosure :=
    PhaseLane.closureFromSelectedBundle
      (frontier.toBundleIdentification data)
  rcases hclosure with ⟨_hsingleton, _hrep, hforced, hrecognizable⟩
  exact ⟨hforced, hrecognizable⟩

/-- On a wave frontier read from the same selected datum as the no-stage
completion law, the recognizable wave/Klein-Gordon identity is forced
directly from the law-native physical selected closure law. -/
  theorem LocalEventFourStateCompletionLaw.waveSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law)
    (frontier : WaveFrontier data) :
    let cls := frontier.frontier.frontier.frontier.collapse.law.observer.continuumClass
    let target := data.selectedBundle.physicalPrinciple.selectedLaw.selectedClosureLaw
    ForcedContinuumLaw cls target ∧
      Nonempty
        (WaveLane.RecognizableIdentity
          Time Carrier Law frontier.Field frontier.Scalar) := by
  have hclosure :=
    WaveLane.closureFromSelectedBundle
      (frontier.toBundleIdentification data)
  rcases hclosure with ⟨_hsingleton, _hrep, hforced, hrecognizable⟩
  exact ⟨hforced, hrecognizable⟩

/-- On a gauge frontier read from the same selected datum as the no-stage
completion law, the recognizable Maxwell identity is forced directly from the
law-native physical selected closure law. -/
  theorem LocalEventFourStateCompletionLaw.gaugeSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law)
    (frontier : GaugeFrontier data) :
    let cls := frontier.frontier.collapse.law.observer.continuumClass
    let target := data.selectedBundle.physicalPrinciple.selectedLaw.selectedClosureLaw
    ForcedContinuumLaw cls target ∧
      Nonempty
        (GaugeLane.RecognizableIdentity
          Time Carrier Law frontier.Field frontier.Source) := by
  have hclosure :=
    GaugeLane.closureFromSelectedBundle
      (frontier.toBundleIdentification data)
  rcases hclosure with ⟨_hsingleton, _hrep, hforced, hrecognizable⟩
  exact ⟨hforced, hrecognizable⟩

/-- On a geometric frontier read from the same selected datum as the no-stage
completion law, the recognizable Einstein identity is forced directly from the
law-native physical selected closure law. -/
  theorem LocalEventFourStateCompletionLaw.geometricSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law)
    (frontier : GeometricFrontier data) :
    let cls := frontier.frontier.collapse.law.observer.continuumClass
    let target := data.selectedBundle.physicalPrinciple.selectedLaw.selectedClosureLaw
    ForcedContinuumLaw cls target ∧
      Nonempty
        (GeometricLane.RecognizableIdentity
          Time Carrier Law frontier.Tensor frontier.Scalar) := by
  have hclosure :=
    GeometricLane.closureFromSelectedBundle
      (frontier.toBundleIdentification data)
  rcases hclosure with ⟨_hsingleton, _hrep, hforced, hrecognizable⟩
  exact ⟨hforced, hrecognizable⟩

/-- The no-stage completion law, together with the four exact endpoint
frontiers on the same selected datum, already forces the recognizable
Schrödinger, wave/Klein-Gordon, Maxwell, and Einstein identities. -/
theorem LocalEventFourStateCompletionLaw.flagshipSurface
    {Index Time Carrier Law : Type}
    (data : LocalEventFourStateCompletionLaw Index Time Carrier Law)
    (frontiers : FlagshipFrontiers data) :
    PartIVLawCompletionStatement data.toNaturalOperatorCompletion ∧
      Nonempty
        (Σ Field : Type, Σ Scalar : Type,
          PhaseLane.RecognizableIdentity
            Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Scalar : Type,
          WaveLane.RecognizableIdentity
            Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Source : Type,
          GaugeLane.RecognizableIdentity
            Time Carrier Law Field Source) ∧
      Nonempty
        (Σ Tensor : Type, Σ Scalar : Type,
          GeometricLane.RecognizableIdentity
            Time Carrier Law Tensor Scalar) := by
  obtain
    ⟨_hbundle, _hsector, _hbedrock, _haut, _hfiber, _hstate, _hreduced,
      _hschur, hcompletion⟩ := data.attachedSurface
  have hphase := data.phaseSurface frontiers.phase
  have hwave := data.waveSurface frontiers.wave
  have hgauge := data.gaugeSurface frontiers.gauge
  have hgeometric := data.geometricSurface frontiers.geometric
  rcases hphase with ⟨_hphaseForced, hphaseRecognizable⟩
  rcases hwave with ⟨_hwaveForced, hwaveRecognizable⟩
  rcases hgauge with ⟨_hgaugeForced, hgaugeRecognizable⟩
  rcases hgeometric with ⟨_hgeometricForced, hgeometricRecognizable⟩
  rcases hphaseRecognizable with ⟨phaseWitness⟩
  rcases hwaveRecognizable with ⟨waveWitness⟩
  rcases hgaugeRecognizable with ⟨gaugeWitness⟩
  rcases hgeometricRecognizable with ⟨geometricWitness⟩
  exact
    ⟨hcompletion,
      ⟨⟨frontiers.phase.Field, frontiers.phase.Scalar, phaseWitness⟩⟩,
      ⟨⟨frontiers.wave.Field, frontiers.wave.Scalar, waveWitness⟩⟩,
      ⟨⟨frontiers.gauge.Field, frontiers.gauge.Source, gaugeWitness⟩⟩,
      ⟨⟨frontiers.geometric.Tensor, frontiers.geometric.Scalar,
        geometricWitness⟩⟩⟩

end ClosureCurrent

end CoherenceCalculus
