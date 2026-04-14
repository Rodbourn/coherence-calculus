import CoherenceCalculus.Foundation.CharacteristicTransportCore
import CoherenceCalculus.Foundation.ConstraintCompilerCore
import CoherenceCalculus.Foundation.ProjectorCalculusCore
import CoherenceCalculus.Foundation.TargetCore

/-!
# Foundation.VariationalSelectionCore

Minimal Chapter 7 variational and selection bridge interfaces.

This module keeps the realized dynamics / selection surface explicit and
finite. It does not import continuum mechanics or analytic Hamilton-Jacobi
machinery. Instead it records:

- a regular variational datum relating Lagrangian, Hamiltonian, and
  characteristic residual laws
- a projection bridge from the dynamics-side characteristic law to the
  observer-side transport presentation
- an explicit finite selection datum over the already-certified compiler and
  projector-calculus interfaces

The point is to certify the structural reduction carried by the manuscript
without overstating any hidden analytic foundation.
-/

namespace CoherenceCalculus

/-- Explicit dynamics-side variational datum relating Lagrangian,
Hamiltonian, and Hamilton-Jacobi characteristic residual laws. -/
structure RegularVariationalSystem (Config Phase : Type) where
  lagrangianResidual : Config → SignedCount
  hamiltonianResidual : Phase → SignedCount
  characteristicResidual : Config → SignedCount
  lagrangian_hamiltonian :
    (∀ q : Config, lagrangianResidual q = SignedCount.zero) ↔
      (∀ p : Phase, hamiltonianResidual p = SignedCount.zero)
  hamiltonian_characteristic :
    (∀ p : Phase, hamiltonianResidual p = SignedCount.zero) ↔
      (∀ q : Config, characteristicResidual q = SignedCount.zero)

/-- The three dynamics-side presentations agree once the explicit regular
variational datum is fixed. -/
theorem dynamics_triad {Config Phase : Type}
    (data : RegularVariationalSystem Config Phase) :
    (∀ q : Config, data.lagrangianResidual q = SignedCount.zero) ↔
      (∀ p : Phase, data.hamiltonianResidual p = SignedCount.zero) ∧
        (∀ q : Config, data.characteristicResidual q = SignedCount.zero) := by
  constructor
  · intro hLag
    have hHam : ∀ p : Phase, data.hamiltonianResidual p = SignedCount.zero :=
      data.lagrangian_hamiltonian.mp hLag
    exact ⟨hHam, data.hamiltonian_characteristic.mp hHam⟩
  · intro h
    exact data.lagrangian_hamiltonian.mpr h.1

/-- Explicit projection bridge from the dynamics-side characteristic residual
to the observer-side characteristic transport residual. -/
structure HamiltonJacobiProjectionDatum (Config Phase : Type) where
  dynamics : RegularVariationalSystem Config Phase
  observer : ConservativeTransportDatum Config Config
  observer_characteristic_eq :
    ∀ q : Config,
      observer.characteristicResidual q = dynamics.characteristicResidual q

/-- Observer-side characteristic transport is exactly the projected
dynamics-side characteristic law. -/
theorem hj_projection {Config Phase : Type}
    (data : HamiltonJacobiProjectionDatum Config Phase) :
    CharacteristicPresentation data.observer ↔
      (∀ q : Config, data.dynamics.characteristicResidual q = SignedCount.zero) := by
  constructor
  · intro h q
    have hq := h q
    rw [data.observer_characteristic_eq q] at hq
    exact hq
  · intro h q
    rw [data.observer_characteristic_eq q]
    exact h q

/-- Explicit realized class carrying both the observer-side characteristic
horizon realization and the dynamics-side variational bridge data. -/
structure RealizedVariationalClass (Index Time Config Phase : Type) where
  realization : Index → CharacteristicHorizonRealization Time
  dynamics : Index → RegularVariationalSystem Config Phase
  projection : Index → HamiltonJacobiProjectionDatum Config Phase
  projection_uses_dynamics : ∀ i : Index, (projection i).dynamics = dynamics i

/-- On a realized variational class, the active Part I transport calculus and
the dynamics-side triad hold uniformly across the class. -/
theorem selection_problem {Index Time Config Phase : Type}
    (cls : RealizedVariationalClass Index Time Config Phase) :
    (∀ i : Index,
      (∀ x : State, trueBoundary (trueBoundary x) = State.zero) ∧
        (∀ h : Nat, ∀ x : State,
          observedBoundary (cls.realization i).tower h
              (observedBoundary (cls.realization i).tower h x) =
            State.negate (boundaryDefect (cls.realization i).tower h x))) ∧
      (∀ i : Index,
        (∀ q : Config, (cls.dynamics i).lagrangianResidual q = SignedCount.zero) ↔
          (∀ p : Phase, (cls.dynamics i).hamiltonianResidual p = SignedCount.zero) ∧
            (∀ q : Config, (cls.dynamics i).characteristicResidual q = SignedCount.zero)) ∧
      (∀ i : Index,
        CharacteristicPresentation (cls.projection i).observer ↔
          (∀ q : Config, (cls.dynamics i).characteristicResidual q = SignedCount.zero)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact transfer_part_one (cls.realization i)
  · intro i
    exact dynamics_triad (cls.dynamics i)
  · intro i
    rw [← cls.projection_uses_dynamics i]
    exact hj_projection (cls.projection i)

/-- Explicit finite selection datum at one fixed horizon inside a realized
class. -/
structure SelectionDatum (Time : Type) where
  realization : CharacteristicHorizonRealization Time
  horizon : Nat
  derivation : Compiler.DerivationStep
  symmetry : Compiler.FinGroup
  representation : Compiler.UnitaryRep symmetry
  decomposition : Compiler.IsotypicDecomposition symmetry representation
  derivation_equivariant :
    Compiler.IsGEquivariant symmetry representation derivation.form.op
  parameterCount : Compiler.ParameterCount symmetry representation
  objective : DesignObjective
  candidates : CandidateFamily objective.rank
  minimizer : MinimizerCertificate objective candidates
  gradient : GradientFunctional
  selectedProjection : Projection
  stationary : isStationaryFor gradient selectedProjection

/-- The selected observed law is the explicitly certified reduced datum carried
by the current compiler derivation step. -/
def selected_observed_law {Time : Type} (data : SelectionDatum Time) : Compiler.QuadForm :=
  Compiler.stepDefect data.derivation

/-- The explicitly selected candidate in the finite observer-side family. -/
def selectedCandidate {Time : Type}
    (data : SelectionDatum Time) : GrassmannianElem data.objective.rank :=
  data.candidates.elem
    (existence_of_minimizers data.objective data.candidates data.minimizer)

/-- The projection carried by the explicitly selected finite candidate. -/
def selectedCandidateProjection {Time : Type}
    (data : SelectionDatum Time) : Projection :=
  (selectedCandidate data).proj

/-- The current finite observer-motion value is the certified objective value
of the selected candidate. -/
def observerMotionValue {Time : Type} (data : SelectionDatum Time) : Nat :=
  data.objective.eval (selectedCandidate data)

/-- The selected candidate projection lies in the certified Grassmannian surface
for the current observer-side objective. -/
theorem selectedCandidateProjection_in_grassmannian {Time : Type}
    (data : SelectionDatum Time) :
    isInGrassmannian data.objective.rank (selectedCandidateProjection data) := by
  refine ⟨selectedCandidate data, rfl⟩

/-- The selected observer-motion value is minimal among the listed candidate
family by construction of the minimizer certificate. -/
theorem observerMotionValue_minimal {Time : Type}
    (data : SelectionDatum Time) (i : Fin (Nat.succ data.candidates.size)) :
    observerMotionValue data ≤ data.objective.eval (data.candidates.elem i) := by
  exact existence_of_minimizers_minimizes
    data.objective
    data.candidates
    data.minimizer
    i

/-- Horizon-preserving equivalence is explicit transport of observed boundary,
defect, and selected reduced law at one fixed horizon. -/
structure HorizonPreservingEquivalence {Time : Type}
    (left right : SelectionDatum Time) where
  transport : AddMap
  sameHorizon : left.horizon = right.horizon
  observed_boundary :
    ∀ x : State,
      transport (observedBoundary left.realization.tower left.horizon x) =
        observedBoundary right.realization.tower right.horizon (transport x)
  observed_defect :
    ∀ x : State,
      transport (boundaryDefect left.realization.tower left.horizon x) =
        boundaryDefect right.realization.tower right.horizon (transport x)
  selected_transport :
    ∀ x : State,
      transport ((selected_observed_law left).op x) =
        (selected_observed_law right).op (transport x)

/-- An admissible realized class is an indexed family of explicit finite
selection data. -/
structure AdmissibleRealizedClass (Index Time : Type) where
  datum : Index → SelectionDatum Time

/-- The forcing problem on an admissible realized class is reduced to the
already-certified finite compiler and stationarity interfaces. -/
theorem selection_interface {Index Time : Type}
    (cls : AdmissibleRealizedClass Index Time) (i : Index) :
    (∀ x : State, trueBoundary (trueBoundary x) = State.zero) ∧
      (∀ rho sigma : Fin (cls.datum i).decomposition.numIrreps, rho ≠ sigma →
        ∀ x : State,
          ((cls.datum i).decomposition.P rho).proj
            ((cls.datum i).derivation.form.op
              (((cls.datum i).decomposition.P sigma).proj x)) = State.zero) ∧
      Compiler.commutantDim
          (cls.datum i).symmetry
          (cls.datum i).representation
          (cls.datum i).parameterCount =
        Compiler.finNatSum (cls.datum i).parameterCount.numIrreps
          (fun rho =>
            (cls.datum i).parameterCount.multiplicity rho *
              (cls.datum i).parameterCount.multiplicity rho *
              (cls.datum i).parameterCount.endomorphismDim rho) ∧
      (∃ bc : Compiler.BoundCertificate (cls.datum i).derivation,
        ∀ x : State,
          State.pair x (bc.bound.op x) =
            State.pair x ((selected_observed_law (cls.datum i)).op x)) ∧
      minimizesAt
        (cls.datum i).objective
        (cls.datum i).candidates
        (existence_of_minimizers
          (cls.datum i).objective
          (cls.datum i).candidates
          (cls.datum i).minimizer) ∧
      (∀ x : State,
        projectionCommutator
            ((cls.datum i).gradient.gradient (cls.datum i).selectedProjection)
            (cls.datum i).selectedProjection x = State.zero) := by
  refine And.intro fullBoundary_closes ?_
  refine And.intro ?_ ?_
  · intro rho sigma hne x
    exact Compiler.normal_form
      (cls.datum i).symmetry
      (cls.datum i).representation
      (cls.datum i).decomposition
      (cls.datum i).derivation.form.op
      (cls.datum i).derivation_equivariant
      rho sigma hne x
  refine And.intro ?_ ?_
  · exact Compiler.parameter_count_formula
      (cls.datum i).symmetry
      (cls.datum i).representation
      (cls.datum i).parameterCount
  refine And.intro ?_ ?_
  · obtain ⟨bc, hbc⟩ := Compiler.compiler_contract (cls.datum i).derivation
    refine ⟨bc, ?_⟩
    intro x
    simpa [selected_observed_law] using hbc x
  refine And.intro ?_ ?_
  · exact existence_of_minimizers_minimizes
      (cls.datum i).objective
      (cls.datum i).candidates
      (cls.datum i).minimizer
  · exact (stationarity_condition
      (cls.datum i).gradient
      (cls.datum i).selectedProjection).mp (cls.datum i).stationary

/-- If all admissible selection data lie in one horizon-preserving equivalence
class, then the selected observed law is forced across the class. -/
theorem selection_to_forcing {Index Time : Type}
    (cls : AdmissibleRealizedClass Index Time)
    (hunique : ∀ i j : Index,
      HorizonPreservingEquivalence (cls.datum i) (cls.datum j)) :
    ∀ i j : Index,
      (cls.datum i).horizon = (cls.datum j).horizon ∧
        (∀ x : State,
          (hunique i j).transport ((selected_observed_law (cls.datum i)).op x) =
            (selected_observed_law (cls.datum j)).op ((hunique i j).transport x)) := by
  intro i j
  exact ⟨(hunique i j).sameHorizon, (hunique i j).selected_transport⟩

end CoherenceCalculus
