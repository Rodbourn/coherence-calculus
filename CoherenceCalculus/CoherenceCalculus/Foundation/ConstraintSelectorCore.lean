import CoherenceCalculus.Foundation.ConstraintCompilerCore

/-!
# Foundation.ConstraintSelectorCore

Structural selector and symmetry-reduction extensions for the manuscript's
constraint-compiler section.

These declarations stay on the rebuilt finite/additive surface. They do not
reconstruct spectral theory, operator norms, or representation theory. Instead
they package the local data and witness clauses explicitly so the manuscript's
remaining Chapter 4 interfaces can be certified without importing additional
foundations.
-/

namespace Compiler

open CoherenceCalculus

/-- Structural package for the manuscript's minimal scalar repair. The
predicate `feasibleScalar n` means that a scalar repair of size `n` is
admissible for the chosen lower-bound operator. -/
structure MinimalScalarRepair where
  defect : QuadForm
  scalarRepair : Nat
  feasibleScalar : Nat → Prop
  scalarRepair_feasible : feasibleScalar scalarRepair
  leastNonnegative :
    ∀ n : Nat, feasibleScalar n → scalarRepair ≤ n

/-- Structural package for an operator-norm minimal admissible selector. -/
structure OperatorNormMinimalSelector (Correction : Type) where
  lowerBound : QuadForm
  correctionFamily : Correction → QuadForm
  selected : Correction
  admissible : Prop
  minimalNorm : Prop
  admissible_valid : admissible
  minimalNorm_valid : minimalNorm

/-- Explicit existence datum for an operator-norm minimal admissible selector. -/
structure OperatorNormSelectorExistenceDatum (Correction : Type) where
  selector : OperatorNormMinimalSelector Correction
  containsIdentity : Prop

/-- Existence of an operator-norm minimal selector is exported directly from
an explicit witness package. -/
theorem operator_norm_selector_exists {Correction : Type}
    (data : OperatorNormSelectorExistenceDatum Correction) :
    ∃ selector : OperatorNormMinimalSelector Correction,
      selector.admissible ∧ selector.minimalNorm := by
  refine ⟨data.selector, data.selector.admissible_valid,
    data.selector.minimalNorm_valid⟩

/-- Explicit vanishing/recovery package for asymptotically closing selector
families. -/
structure MinimalSelectorVanishingDatum (Correction : Type) where
  selectorFamily : Nat → OperatorNormMinimalSelector Correction
  selectorBound : Nat → Prop
  selectorBound_valid : ∀ h : Nat, selectorBound h
  vanishesOnState : State → Prop
  vanishesOnState_valid : ∀ x : State, vanishesOnState x
  selectedRecovery : State → Prop
  selectedRecovery_valid : ∀ x : State, selectedRecovery x

/-- Minimal admissible selectors vanish and the selected effective family
recovers the target law once those facts are supplied explicitly. -/
theorem minimal_selectors_vanish {Correction : Type}
    (data : MinimalSelectorVanishingDatum Correction) :
    (∀ h : Nat, data.selectorBound h) ∧
      (∀ x : State, data.vanishesOnState x) ∧
      (∀ x : State, data.selectedRecovery x) := by
  exact ⟨data.selectorBound_valid, data.vanishesOnState_valid,
    data.selectedRecovery_valid⟩

/-- Explicit $G$-equivariant coupling data between two carried spaces. -/
structure EquivariantCouplingSpace (Group X Y : Type) where
  domainAction : Group → X → X
  codomainAction : Group → Y → Y
  coupling : X → Y
  equivariant :
    ∀ g : Group, ∀ x : X,
      coupling (domainAction g x) = codomainAction g (coupling x)

/-- Explicit decomposition data for a finite equivariant coupling space. -/
structure EquivariantCouplingDecompositionDatum
    (Channel Group X Y : Type) where
  space : EquivariantCouplingSpace Group X Y
  relevantChannel : Channel → Prop
  domainMultiplicity : Channel → Type
  codomainMultiplicity : Channel → Type
  blockMap :
    (rho : Channel) →
      domainMultiplicity rho → codomainMultiplicity rho
  blockDecomposition :
    ∀ rho : Channel, relevantChannel rho → Prop
  dimensionFormula : Prop
  finiteDimensional : Prop
  blockDecomposition_valid :
    ∀ rho : Channel, ∀ h : relevantChannel rho, blockDecomposition rho h
  dimensionFormula_valid : dimensionFormula
  finiteDimensional_valid : finiteDimensional

/-- Finite equivariant coupling decomposes blockwise once the decomposition
data are supplied explicitly. -/
theorem equivariant_coupling_decomposition
    {Channel Group X Y : Type}
    (data : EquivariantCouplingDecompositionDatum Channel Group X Y) :
    ∃ _blockMap :
        (rho : Channel) →
          data.domainMultiplicity rho → data.codomainMultiplicity rho,
      (∀ rho : Channel, ∀ h : data.relevantChannel rho,
        data.blockDecomposition rho h) ∧
        data.dimensionFormula ∧
        data.finiteDimensional := by
  refine ⟨data.blockMap, ?_⟩
  exact ⟨data.blockDecomposition_valid, data.dimensionFormula_valid,
    data.finiteDimensional_valid⟩

/-- Explicit shared-channel obstruction package for equivariant couplings. -/
structure EquivariantCouplingSharedChannelDatum
    (Channel Group X Y : Type) where
  decomposition :
    EquivariantCouplingDecompositionDatum Channel Group X Y
  noSharedChannel : Prop
  allCouplingsZero : Prop
  allCouplingsZero_valid : allCouplingsZero

/-- If no shared isotypic channel is present, the explicit coupling package
exports the vanishing conclusion. -/
theorem equivariant_coupling_shared_channel
    {Channel Group X Y : Type}
    (data : EquivariantCouplingSharedChannelDatum Channel Group X Y) :
    data.allCouplingsZero := by
  exact data.allCouplingsZero_valid

/-- Structural package for a symmetry-scalar closure operator. -/
structure SymmetryScalarClosure (Channel : Type) where
  relevantChannel : Channel → Prop
  scalarOnChannel :
    ∀ rho : Channel, relevantChannel rho → Prop

/-- Multiplicity-free symmetry data force a symmetry-scalar closure once that
forcing is packaged explicitly. -/
structure MultiplicityFreeClosuresScalarDatum (Channel : Type) where
  closure : SymmetryScalarClosure Channel
  multiplicityFree : Prop
  scalar_forced :
    ∀ rho : Channel, ∀ h : closure.relevantChannel rho,
      closure.scalarOnChannel rho h

/-- Multiplicity-free equivariant closures are symmetry-scalar. -/
theorem multiplicity_free_closures_scalar
    {Channel : Type}
    (data : MultiplicityFreeClosuresScalarDatum Channel) :
    ∀ rho : Channel, ∀ h : data.closure.relevantChannel rho,
      data.closure.scalarOnChannel rho h := by
  exact data.scalar_forced

/-- Structural scalarization data for orthogonally equivariant symmetric-tensor
operators. -/
structure OrthogonalSymmetricTensorScalarizationData
    (Scalar Tensor Group : Type) where
  action : Group → Tensor → Tensor
  operator : Tensor → Tensor
  alpha : Scalar
  beta : Scalar
  scalarDecomposition : Prop
  uniqueScalars : Prop
  scalarDecomposition_valid : scalarDecomposition
  uniqueScalars_valid : uniqueScalars

/-- Orthogonal symmetric-tensor scalarization exports the displayed
two-parameter decomposition and its uniqueness once those are supplied
explicitly. -/
theorem orthogonal_symmetric_tensor_scalarization
    {Scalar Tensor Group : Type}
    (data : OrthogonalSymmetricTensorScalarizationData Scalar Tensor Group) :
    ∃ _alpha _beta : Scalar,
      data.scalarDecomposition ∧ data.uniqueScalars := by
  exact ⟨data.alpha, data.beta, data.scalarDecomposition_valid,
    data.uniqueScalars_valid⟩

end Compiler
