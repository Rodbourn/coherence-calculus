import CoherenceCalculus.PartIV.FlagshipCore

namespace CoherenceCalculus

/-- Downstream completion package: the generic Part IV law-completion chain is
realized by concrete flagship witnesses rather than only by abstract carrier
classification props. This sits after `FlagshipCore` to avoid importing the
flagship recognition packages back into the generic observer-selection layer. -/
structure FlagshipLawCompletion (Time Carrier Law : Type) where
  completion : NaturalOperatorCompletion Time Carrier Law
  phaseWitness :
    Σ Field : Type, Σ Scalar : Type,
      PhaseLane.RecognizableIdentity Time Carrier Law Field Scalar
  waveWitness :
    Σ Field : Type, Σ Scalar : Type,
      WaveLane.RecognizableIdentity Time Carrier Law Field Scalar
  kineticWitness :
    Σ State : Type, Σ Velocity : Type, Σ Observable : Type, Σ Scalar : Type,
      HydrodynamicLane.RecognizableIdentity
        Time Carrier Law State Velocity Observable Scalar
  gaugeWitness :
    Σ Field : Type, Σ Source : Type,
      GaugeLane.RecognizableIdentity Time Carrier Law Field Source
  geometricWitness :
    Σ Tensor : Type, Σ Scalar : Type,
      GeometricLane.RecognizableIdentity Time Carrier Law Tensor Scalar

namespace FlagshipLawCompletion

/-- The downstream flagship package still carries the full generic Part IV
completion surface on its abstract completion datum. -/
theorem completionSurface
    {Time Carrier Law : Type}
    (data : FlagshipLawCompletion Time Carrier Law) :
    PartIVLawCompletionStatement data.completion := by
  exact partIV_law_completion data.completion

/-- The same downstream package also carries concrete recognizable witnesses
for the five flagship lanes. -/
theorem recognizableWitnesses
    {Time Carrier Law : Type}
    (data : FlagshipLawCompletion Time Carrier Law) :
    Nonempty
      (Σ Field : Type, Σ Scalar : Type,
        PhaseLane.RecognizableIdentity
          Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Scalar : Type,
          WaveLane.RecognizableIdentity
            Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ State : Type, Σ Velocity : Type, Σ Observable : Type, Σ Scalar : Type,
          HydrodynamicLane.RecognizableIdentity
            Time Carrier Law State Velocity Observable Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Source : Type,
          GaugeLane.RecognizableIdentity
            Time Carrier Law Field Source) ∧
      Nonempty
        (Σ Tensor : Type, Σ Scalar : Type,
          GeometricLane.RecognizableIdentity
            Time Carrier Law Tensor Scalar) := by
  exact
    ⟨⟨data.phaseWitness⟩,
      ⟨data.waveWitness⟩,
      ⟨data.kineticWitness⟩,
      ⟨data.gaugeWitness⟩,
      ⟨data.geometricWitness⟩⟩

/-- The downstream flagship completion theorem turns Step 4 into concrete
recognition witnesses for the five flagship carrier laws. -/
theorem flagship_law_completion
    {Time Carrier Law : Type}
    (data : FlagshipLawCompletion Time Carrier Law) :
    PartIVLawCompletionStatement data.completion ∧
      Nonempty
        (Σ Field : Type, Σ Scalar : Type,
          PhaseLane.RecognizableIdentity
            Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Scalar : Type,
          WaveLane.RecognizableIdentity
            Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ State : Type, Σ Velocity : Type, Σ Observable : Type, Σ Scalar : Type,
          HydrodynamicLane.RecognizableIdentity
            Time Carrier Law State Velocity Observable Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Source : Type,
          GaugeLane.RecognizableIdentity
            Time Carrier Law Field Source) ∧
      Nonempty
        (Σ Tensor : Type, Σ Scalar : Type,
          GeometricLane.RecognizableIdentity
            Time Carrier Law Tensor Scalar) := by
  exact ⟨completionSurface data, recognizableWitnesses data⟩

end FlagshipLawCompletion

/-- The downstream flagship completion theorem turns Step 4 into concrete
recognition witnesses for the five flagship carrier laws. This root-level
export preserves the established manuscript-facing name while the
`FlagshipLawCompletion` namespace carries the smaller helper surfaces. -/
theorem flagship_law_completion
    {Time Carrier Law : Type}
    (data : FlagshipLawCompletion Time Carrier Law) :
    PartIVLawCompletionStatement data.completion ∧
      Nonempty
        (Σ Field : Type, Σ Scalar : Type,
          PhaseLane.RecognizableIdentity
            Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Scalar : Type,
          WaveLane.RecognizableIdentity
            Time Carrier Law Field Scalar) ∧
      Nonempty
        (Σ State : Type, Σ Velocity : Type, Σ Observable : Type, Σ Scalar : Type,
          HydrodynamicLane.RecognizableIdentity
            Time Carrier Law State Velocity Observable Scalar) ∧
      Nonempty
        (Σ Field : Type, Σ Source : Type,
          GaugeLane.RecognizableIdentity
            Time Carrier Law Field Source) ∧
      Nonempty
        (Σ Tensor : Type, Σ Scalar : Type,
          GeometricLane.RecognizableIdentity
            Time Carrier Law Tensor Scalar) := by
  exact FlagshipLawCompletion.flagship_law_completion data

end CoherenceCalculus
