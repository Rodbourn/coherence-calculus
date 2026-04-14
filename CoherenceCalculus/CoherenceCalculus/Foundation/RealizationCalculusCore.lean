import CoherenceCalculus.Foundation.ObservableClosureCore
import CoherenceCalculus.Foundation.ProjectorCalculusCore

/-!
# Foundation.RealizationCalculusCore

Import-free realization grammar for the manuscript's numerical host layer.

This file does not derive a specific numerical method. It records the finite,
explicit certification surface needed to state and audit:

- variational laws and realization chains
- typed residual ledgers
- Fortin-compatible inheritance in witness form
- geometry/quadrature/aliasing packages
- stage, solver, interface, and adjoint-goal certificates

Hard analytic ingredients remain explicit local data. Nothing here imports a
continuum, Hilbert, or spectral hierarchy.
-/

namespace CoherenceCalculus

/-- Residual-valued variational law on explicit trial/test carriers. -/
structure VariationalLaw where
  trialSpace : Type
  testSpace : Type
  bilinear : trialSpace → testSpace → State
  load : testSpace → State
  observables : Type
  invariants : Type

/-- Declared realization chain together with all residual representatives used
by the realization ledger. -/
structure RealizationChain (V : VariationalLaw) where
  trialRealization : Type
  testRealization : Type
  trialLift : trialRealization → V.trialSpace
  testLift : testRealization → V.testSpace
  geometryData : Type
  quadratureData : Type
  stageData : Type
  solverData : Type
  interfaceData : Type
  residualProj : trialRealization → testRealization → State
  residualGeom : trialRealization → testRealization → State
  residualQuad : trialRealization → testRealization → State
  residualAlias : trialRealization → testRealization → State
  residualSplit : trialRealization → testRealization → State
  residualLin : trialRealization → testRealization → State
  residualAlg : trialRealization → testRealization → State
  residualBc : trialRealization → testRealization → State
  residualIface : trialRealization → testRealization → State

/-- The continuum residual attached to a realization chain. -/
def continuumResidual {V : VariationalLaw}
    (R : RealizationChain V) :
    R.trialRealization → R.testRealization → State :=
  fun u v => State.sub (V.load (R.testLift v)) (V.bilinear (R.trialLift u) (R.testLift v))

/-- The terminal realized residual is the interface-level representative. -/
def residualReal {V : VariationalLaw}
    (R : RealizationChain V) :
    R.trialRealization → R.testRealization → State :=
  R.residualIface

/-- Typed realization-crime ledger. -/
structure TypedCrimeLedger (Trial Test : Type) where
  proj : Trial → Test → State
  geom : Trial → Test → State
  quad : Trial → Test → State
  alias : Trial → Test → State
  split : Trial → Test → State
  lin : Trial → Test → State
  alg : Trial → Test → State
  bc : Trial → Test → State
  iface : Trial → Test → State

/-- The canonical crime ledger attached to a realization chain. -/
def typedCrimeLedger {V : VariationalLaw}
    (R : RealizationChain V) :
    TypedCrimeLedger R.trialRealization R.testRealization where
  proj := fun u v => State.sub (R.residualProj u v) (continuumResidual R u v)
  geom := fun u v => State.sub (R.residualGeom u v) (R.residualProj u v)
  quad := fun u v => State.sub (R.residualQuad u v) (R.residualGeom u v)
  alias := fun u v => State.sub (R.residualAlias u v) (R.residualQuad u v)
  split := fun u v => State.sub (R.residualSplit u v) (R.residualAlias u v)
  lin := fun u v => State.sub (R.residualLin u v) (R.residualSplit u v)
  alg := fun u v => State.sub (R.residualAlg u v) (R.residualLin u v)
  bc := fun u v => State.sub (R.residualBc u v) (R.residualAlg u v)
  iface := fun u v => State.sub (R.residualIface u v) (R.residualBc u v)

/-- Nested sum of the typed crime ledger at one realized state/test pair. -/
def crimeLedgerSum {Trial Test : Type}
    (C : TypedCrimeLedger Trial Test) (u : Trial) (v : Test) : State :=
  State.add
    (C.proj u v)
    (State.add
      (C.geom u v)
      (State.add
        (C.quad u v)
        (State.add
          (C.alias u v)
          (State.add
            (C.split u v)
            (State.add
              (C.lin u v)
              (State.add
                (C.alg u v)
                (State.add (C.bc u v) (C.iface u v))))))))

private theorem residual_telescope_step (r₀ r₁ r₂ : State) :
    State.add (State.sub r₁ r₀) (State.sub r₂ r₁) = State.sub r₂ r₀ := by
  calc
    State.add (State.sub r₁ r₀) (State.sub r₂ r₁)
        = State.add (State.sub r₂ r₁) (State.sub r₁ r₀) := by
            rw [State.add_comm]
    _ = State.sub r₂ r₀ := by
          exact sub_eq_add_sub r₂ r₁ r₀

private theorem residual_telescope_nine
    (r₀ r₁ r₂ r₃ r₄ r₅ r₆ r₇ r₈ r₉ : State) :
    State.add
        (State.sub r₁ r₀)
        (State.add
          (State.sub r₂ r₁)
          (State.add
            (State.sub r₃ r₂)
            (State.add
              (State.sub r₄ r₃)
              (State.add
                (State.sub r₅ r₄)
                (State.add
                  (State.sub r₆ r₅)
                  (State.add
                    (State.sub r₇ r₆)
                    (State.add (State.sub r₈ r₇) (State.sub r₉ r₈)))))))) =
      State.sub r₉ r₀ := by
  calc
    State.add
        (State.sub r₁ r₀)
        (State.add
          (State.sub r₂ r₁)
          (State.add
            (State.sub r₃ r₂)
            (State.add
              (State.sub r₄ r₃)
              (State.add
                (State.sub r₅ r₄)
                (State.add
                  (State.sub r₆ r₅)
                  (State.add
                    (State.sub r₇ r₆)
                    (State.add (State.sub r₈ r₇) (State.sub r₉ r₈))))))))
        =
      State.add
        (State.sub r₂ r₀)
        (State.add
          (State.sub r₃ r₂)
          (State.add
            (State.sub r₄ r₃)
            (State.add
              (State.sub r₅ r₄)
              (State.add
                (State.sub r₆ r₅)
                (State.add
                  (State.sub r₇ r₆)
                  (State.add (State.sub r₈ r₇) (State.sub r₉ r₈))))))) := by
          rw [← State.add_assoc, residual_telescope_step]
    _ =
      State.add
        (State.sub r₃ r₀)
        (State.add
          (State.sub r₄ r₃)
          (State.add
            (State.sub r₅ r₄)
            (State.add
              (State.sub r₆ r₅)
              (State.add
                (State.sub r₇ r₆)
                (State.add (State.sub r₈ r₇) (State.sub r₉ r₈)))))) := by
          rw [← State.add_assoc, residual_telescope_step]
    _ =
      State.add
        (State.sub r₄ r₀)
        (State.add
          (State.sub r₅ r₄)
          (State.add
            (State.sub r₆ r₅)
            (State.add
              (State.sub r₇ r₆)
              (State.add (State.sub r₈ r₇) (State.sub r₉ r₈))))) := by
          rw [← State.add_assoc, residual_telescope_step]
    _ =
      State.add
        (State.sub r₅ r₀)
        (State.add
          (State.sub r₆ r₅)
          (State.add
            (State.sub r₇ r₆)
            (State.add (State.sub r₈ r₇) (State.sub r₉ r₈)))) := by
          rw [← State.add_assoc, residual_telescope_step]
    _ =
      State.add
        (State.sub r₆ r₀)
        (State.add
          (State.sub r₇ r₆)
          (State.add (State.sub r₈ r₇) (State.sub r₉ r₈))) := by
          rw [← State.add_assoc, residual_telescope_step]
    _ =
      State.add
        (State.sub r₇ r₀)
        (State.add (State.sub r₈ r₇) (State.sub r₉ r₈)) := by
          rw [← State.add_assoc, residual_telescope_step]
    _ = State.add (State.sub r₈ r₀) (State.sub r₉ r₈) := by
          rw [← State.add_assoc, residual_telescope_step]
    _ = State.sub r₉ r₀ := by
          exact residual_telescope_step r₀ r₈ r₉

/-- The realized residual differs from the continuum residual by the exact sum
of the typed crimes. -/
theorem exact_residual_ledger {V : VariationalLaw}
    (R : RealizationChain V) (u : R.trialRealization) (v : R.testRealization) :
    State.sub (residualReal R u v) (continuumResidual R u v) =
      crimeLedgerSum (typedCrimeLedger R) u v := by
  unfold residualReal continuumResidual crimeLedgerSum typedCrimeLedger
  exact
    (residual_telescope_nine
      (State.sub (V.load (R.testLift v)) (V.bilinear (R.trialLift u) (R.testLift v)))
      (R.residualProj u v)
      (R.residualGeom u v)
      (R.residualQuad u v)
      (R.residualAlias u v)
      (R.residualSplit u v)
      (R.residualLin u v)
      (R.residualAlg u v)
      (R.residualBc u v)
      (R.residualIface u v)).symm

/-- Realization-exactness means every entry of the typed crime ledger vanishes
pointwise. -/
def realizationExact {V : VariationalLaw}
    (R : RealizationChain V) : Prop :=
  ∀ u v,
    (typedCrimeLedger R).proj u v = State.zero ∧
      (typedCrimeLedger R).geom u v = State.zero ∧
      (typedCrimeLedger R).quad u v = State.zero ∧
      (typedCrimeLedger R).alias u v = State.zero ∧
      (typedCrimeLedger R).split u v = State.zero ∧
      (typedCrimeLedger R).lin u v = State.zero ∧
      (typedCrimeLedger R).alg u v = State.zero ∧
      (typedCrimeLedger R).bc u v = State.zero ∧
      (typedCrimeLedger R).iface u v = State.zero

/-- If every typed crime vanishes, the realized residual is the continuum
residual. -/
theorem no_hidden_crime {V : VariationalLaw}
    (R : RealizationChain V) (hexact : realizationExact R)
    (u : R.trialRealization) (v : R.testRealization) :
    residualReal R u v = continuumResidual R u v := by
  rcases hexact u v with ⟨hproj, hgeom, hquad, halias, hsplit, hlin, halg, hbc, hiface⟩
  have hsum : crimeLedgerSum (typedCrimeLedger R) u v = State.zero := by
    unfold crimeLedgerSum
    rw [hproj, hgeom, hquad, halias, hsplit, hlin, halg, hbc, hiface]
    rw [State.zero_add, State.zero_add, State.zero_add, State.zero_add]
    rw [State.zero_add, State.zero_add, State.zero_add, State.add_zero]
  calc
    residualReal R u v =
      State.add (State.sub (residualReal R u v) (continuumResidual R u v)) (continuumResidual R u v) := by
        exact (State.add_sub_cancel_right (residualReal R u v) (continuumResidual R u v)).symm
    _ = State.add (crimeLedgerSum (typedCrimeLedger R) u v) (continuumResidual R u v) := by
          rw [exact_residual_ledger]
    _ = State.add State.zero (continuumResidual R u v) := by
          rw [hsum]
    _ = continuumResidual R u v := by
          rw [State.zero_add]

/-- Explicit Fortin-compatible mixed realization with norms recorded as natural
size functions on the import-free lane. -/
structure FortinCompatibleRealization (U Uh Mh : Type) where
  continuumForm : U → Mh → State
  realizedForm : Uh → Mh → State
  lift : U → Uh
  normU : U → Nat
  normUh : Uh → Nat
  normM : Mh → Nat
  fortin : ∀ u q, realizedForm (lift u) q = continuumForm u q
  fortinConstant : Nat
  lift_bound : ∀ u, normUh (lift u) ≤ fortinConstant * normU u

/-- Continuum inf-sup witness data on the same explicit size scale. The bound is
recorded in cross-multiplied form so no field or division hierarchy is needed. -/
structure ContinuumInfSupWitness {U Uh Mh : Type}
    (data : FortinCompatibleRealization U Uh Mh) where
  beta : Nat
  witness : Mh → U
  lower_bound :
    ∀ q,
      beta * data.normU (witness q) * data.normM q ≤
        State.energy (data.continuumForm (witness q) q)

/-- Explicit transfer certificate for the discrete Fortin-bound inheritance
surface. -/
structure DiscreteInfSupTransferData (U Uh Mh : Type) where
  realization : FortinCompatibleRealization U Uh Mh
  witness : ContinuumInfSupWitness realization
  transferred_bound :
    ∀ q,
      witness.beta * realization.normUh (realization.lift (witness.witness q)) *
          realization.normM q ≤
        realization.fortinConstant *
          State.energy
            (realization.realizedForm (realization.lift (witness.witness q)) q)

/-- The discrete Fortin-bound inheritance theorem on the active import-free
lane is carried by an explicit transfer certificate. -/
theorem discrete_infsup_from_fortin {U Uh Mh : Type}
    (data : DiscreteInfSupTransferData U Uh Mh) (q : Mh) :
    data.witness.beta *
        data.realization.normUh (data.realization.lift (data.witness.witness q)) *
          data.realization.normM q ≤
      data.realization.fortinConstant *
        State.energy
          (data.realization.realizedForm
            (data.realization.lift (data.witness.witness q)) q) := by
  exact data.transferred_bound q

/-- Explicit lifted constraint crime for a declared compatibility square. -/
def liftedConstraintCrime {U Uh : Type}
    (lift : U → Uh)
    (realizedConstraint : Uh → State)
    (projectedConstraint : U → State)
    (u : U) : State :=
  State.sub (realizedConstraint (lift u)) (projectedConstraint u)

/-- A commuting constraint square kills the lifted compatibility crime. -/
theorem commuting_constraint_crime_vanishes {U Uh : Type}
    (lift : U → Uh)
    (realizedConstraint : Uh → State)
    (projectedConstraint : U → State)
    (hcomm : ∀ u, realizedConstraint (lift u) = projectedConstraint u) :
    ∀ u, liftedConstraintCrime lift realizedConstraint projectedConstraint u = State.zero := by
  intro u
  unfold liftedConstraintCrime
  rw [hcomm u]
  exact State.sub_self (projectedConstraint u)

/-- Geometry-realized form together with the projected exact reference form. -/
structure GeometryRealizedForm (Xh Yh : Type) where
  projectedForm : Xh → Yh → State
  geometryForm : Xh → Yh → State

/-- Geometry crime relative to the projected exact form. -/
def geometryCrime {Xh Yh : Type}
    (data : GeometryRealizedForm Xh Yh) (u : Xh) (v : Yh) : State :=
  State.sub (data.geometryForm u v) (data.projectedForm u v)

/-- Exact geometry realization kills the geometry crime. -/
theorem geometry_exactness_kills_geometry_crime {Xh Yh : Type}
    (data : GeometryRealizedForm Xh Yh)
    (hexact : ∀ u v, data.geometryForm u v = data.projectedForm u v) :
    ∀ u v, geometryCrime data u v = State.zero := by
  intro u v
  unfold geometryCrime
  rw [hexact u v]
  exact State.sub_self (data.projectedForm u v)

/-- Quadrature-realized form layered over the geometry realization. -/
structure QuadratureRealizedForm (Xh Yh : Type) where
  projectedForm : Xh → Yh → State
  geometryForm : Xh → Yh → State
  quadratureForm : Xh → Yh → State

/-- Quadrature crime relative to the geometry-realized form. -/
def quadratureCrime {Xh Yh : Type}
    (data : QuadratureRealizedForm Xh Yh) (u : Xh) (v : Yh) : State :=
  State.sub (data.quadratureForm u v) (data.geometryForm u v)

/-- Exact quadrature on the declared workload kills the quadrature crime. -/
theorem quadrature_exactness_kills_quadrature_crime {Xh Yh : Type}
    (data : QuadratureRealizedForm Xh Yh)
    (hexact : ∀ u v, data.quadratureForm u v = data.geometryForm u v) :
    ∀ u v, quadratureCrime data u v = State.zero := by
  intro u v
  unfold quadratureCrime
  rw [hexact u v]
  exact State.sub_self (data.geometryForm u v)

/-- Paired aliasing package on a selected realized workload. -/
structure PairedAliasingPackage (Xh Yh : Type) where
  source : Xh → Prop
  test : Yh → Prop
  aliasing : Xh → Yh → State

/-- One-sided observable transfer induced by a paired aliasing package. -/
def oneSidedAliasingTransfer {Xh Yh : Type}
    (Ω : PairedAliasingPackage Xh Yh) (u : Xh) (v : Yh) : State :=
  Ω.aliasing u v

/-- Quadrature exactness on the selected workload kills both the paired aliasing
package and every one-sided transfer induced from it. -/
theorem quadrature_exactness_kills_aliasing {Xh Yh : Type}
    (Ω : PairedAliasingPackage Xh Yh)
    (hzero : ∀ u v, Ω.source u → Ω.test v → Ω.aliasing u v = State.zero) :
    ∀ u v, Ω.source u → Ω.test v →
      Ω.aliasing u v = State.zero ∧ oneSidedAliasingTransfer Ω u v = State.zero := by
  intro u v hu hv
  refine ⟨hzero u v hu hv, ?_⟩
  exact hzero u v hu hv

/-- A filtered source workload is certified dealias-free when the paired
aliasing package vanishes after filtering. -/
theorem certified_dealiasing_selected_workload {Xh Yh : Type}
    (Ω : PairedAliasingPackage Xh Yh) (F : Xh → Xh)
    (hzero : ∀ u v, Ω.source u → Ω.test v → Ω.aliasing (F u) v = State.zero) :
    ∀ u v, Ω.source u → Ω.test v →
      oneSidedAliasingTransfer Ω (F u) v = State.zero := by
  intro u v hu hv
  exact hzero u v hu hv

/-- Left-to-right composition of a finite stage list. -/
def composeStageList : List AddMap → AddMap
  | [] => AddMap.id
  | ψ :: stages => AddMap.comp (composeStageList stages) ψ

/-- A stage bundle together with its reference full-step evolution. -/
structure StageBundle where
  stages : List AddMap
  referenceEvolution : AddMap

/-- The composed stage evolution of a stage bundle. -/
def stageBundleMap (bundle : StageBundle) : AddMap :=
  composeStageList bundle.stages

/-- The split crime of a stage bundle against its declared reference step. -/
def stageBundleSplitCrime (bundle : StageBundle) : AddMap :=
  AddMap.sub (stageBundleMap bundle) bundle.referenceEvolution

/-- An observable survives a stage when the stage leaves it unchanged. -/
def invariantUnder (I ψ : AddMap) : Prop :=
  ∀ x : State, I (ψ x) = I x

/-- If every stage preserves an invariant, their finite composition does too. -/
theorem stagewise_invariants_survive_composition
    (I : AddMap) (stages : List AddMap)
    (hpres : ∀ ψ, ψ ∈ stages → invariantUnder I ψ) :
    invariantUnder I (composeStageList stages) := by
  induction stages with
  | nil =>
      intro x
      rfl
  | cons ψ stages ih =>
      intro x
      have hψ : invariantUnder I ψ := by
        exact hpres ψ List.mem_cons_self
      have htail : ∀ φ, φ ∈ stages → invariantUnder I φ := by
        intro φ hφ
        exact hpres φ (List.mem_cons_of_mem ψ hφ)
      calc
        I (composeStageList (ψ :: stages) x)
            = I (composeStageList stages (ψ x)) := by
                rfl
        _ = I (ψ x) := by
              exact ih htail (ψ x)
        _ = I x := by
              exact hψ x

/-- Solver package on the rebuilt additive state space. -/
structure SolverPackage where
  operator : AddMap
  preconditioner : AddMap
  decomposition : Type
  restrictionProlongation : Type
  rhs : State
  computedState : State

/-- Algebraic crime of a declared solver package. -/
def solverPackageAlgebraicCrime (data : SolverPackage) : State :=
  State.sub data.rhs (data.operator data.computedState)

/-- Exact solve is equivalent to vanishing algebraic crime once an explicit
inverse witness has been supplied. -/
theorem exact_solve_iff_algebraic_crime_vanishes
    (data : SolverPackage) (hinv : HasInverse data.operator) :
    solverPackageAlgebraicCrime data = State.zero ↔
      data.computedState = hinv.inv data.rhs := by
  constructor
  · intro hzero
    have hsolve :
        data.operator data.computedState = data.rhs := by
      have hcancel :=
        State.add_sub_cancel_right data.rhs (data.operator data.computedState)
      unfold solverPackageAlgebraicCrime at hzero
      rw [hzero, State.zero_add] at hcancel
      exact hcancel
    calc
      data.computedState = hinv.inv (data.operator data.computedState) := by
        symm
        exact hinv.left_inv data.computedState
      _ = hinv.inv data.rhs := by
            rw [hsolve]
  · intro hsolve
    unfold solverPackageAlgebraicCrime
    rw [hsolve, hinv.right_inv]
    exact State.sub_self data.rhs

/-- Explicit solver-spectrum certification data. The analytic work is kept in
the certificate fields rather than imported as hidden machinery. -/
structure SpectralEquivalenceSolverData where
  lowerBound : Nat
  upperBound : Nat
  conditionBound : Nat
  eigenvalue : Nat → Prop
  eigenvalue_window : ∀ value, eigenvalue value → lowerBound ≤ value ∧ value ≤ upperBound
  condition_number_bound : upperBound ≤ conditionBound * lowerBound

/-- A spectral-equivalence solver certificate packages the eigenvalue window and
the resulting condition-number bound on the declared surface. -/
theorem spectral_equivalence_solver_certificate
    (data : SpectralEquivalenceSolverData) :
    (∀ value, data.eigenvalue value → data.lowerBound ≤ value ∧ value ≤ data.upperBound) ∧
      data.upperBound ≤ data.conditionBound * data.lowerBound := by
  exact ⟨data.eigenvalue_window, data.condition_number_bound⟩

/-- Interface package between an external host state and the current realized
state space. -/
structure InterfacePackage (Ext : Type) where
  trace : AddMap
  externalTrace : Ext → State
  transfer : AddMap
  lift : AddMap
  hostTransfer : Ext → State

/-- Interface crime of a declared host transfer square. -/
def interfaceCrime {Ext : Type}
    (data : InterfacePackage Ext) (u : Ext) : State :=
  State.sub
    (data.trace (data.hostTransfer u))
    (data.transfer (data.externalTrace u))

/-- A commuting interface square kills the interface crime, and therefore any
lifted correction generated from it. -/
theorem commuting_interface_diagrams_kill_interface_crime {Ext : Type}
    (data : InterfacePackage Ext)
    (hcomm :
      ∀ u, data.trace (data.hostTransfer u) = data.transfer (data.externalTrace u))
    (_hlift : ∀ x, data.trace (data.lift x) = x) :
    (∀ u, interfaceCrime data u = State.zero) ∧
      (∀ u, data.lift (interfaceCrime data u) = State.zero) := by
  refine ⟨?_, ?_⟩
  · intro u
    unfold interfaceCrime
    rw [hcomm u]
    exact State.sub_self (data.transfer (data.externalTrace u))
  · intro u
    have hzero : interfaceCrime data u = State.zero := by
      unfold interfaceCrime
      rw [hcomm u]
      exact State.sub_self (data.transfer (data.externalTrace u))
    rw [hzero, data.lift.map_zero]

/-- Sum of a finite list of state residuals. -/
def stateListSum : List State → State
  | [] => State.zero
  | x :: xs => State.add x (stateListSum xs)

/-- Sum of a finite list of goal contributions. -/
def goalContributionSum : List Nat → Nat
  | [] => 0
  | n :: ns => n + goalContributionSum ns

/-- Explicit adjoint-goal certificate for the goal-error ledger. The final
weighted decomposition is kept as a field so no hidden bilinear algebra is
smuggled in. -/
structure AdjointGoalCertificate where
  operator : AddMap
  inverse : HasInverse operator
  rhs : State
  computedState : State
  goalVector : State
  adjointWeight : State
  residualTerms : List State
  adjoint_identity :
    ∀ x : State,
      State.pair goalVector x = State.pair adjointWeight (operator x)
  residual_split :
    State.sub rhs (operator computedState) = stateListSum residualTerms
  weighted_residual_split :
    State.pair adjointWeight (State.sub rhs (operator computedState)) =
      goalContributionSum (List.map (fun r => State.pair adjointWeight r) residualTerms)

/-- Exact solved state carried by an adjoint-goal certificate. -/
def exactState (data : AdjointGoalCertificate) : State :=
  data.inverse.inv data.rhs

/-- Algebraic residual carried by an adjoint-goal certificate. -/
def algebraicResidual (data : AdjointGoalCertificate) : State :=
  State.sub data.rhs (data.operator data.computedState)

/-- Goal error carried by an adjoint-goal certificate. -/
def goalError (data : AdjointGoalCertificate) : Nat :=
  State.pair data.goalVector (State.sub (exactState data) data.computedState)

/-- Exact goal-error ledger identity from the explicit adjoint-goal
certificate. -/
theorem exact_goal_error_ledger_identity
    (data : AdjointGoalCertificate) :
    goalError data = State.pair data.adjointWeight (algebraicResidual data) ∧
      goalError data =
        goalContributionSum (List.map (fun r => State.pair data.adjointWeight r) data.residualTerms) := by
  have hres :
      data.operator (State.sub (exactState data) data.computedState) =
        algebraicResidual data := by
    unfold exactState algebraicResidual
    rw [AddMap.map_sub_state data.operator (data.inverse.inv data.rhs) data.computedState]
    rw [data.inverse.right_inv]
  have hgoal :
      goalError data =
        State.pair data.adjointWeight
          (data.operator (State.sub (exactState data) data.computedState)) := by
    unfold goalError
    rw [data.adjoint_identity (State.sub (exactState data) data.computedState)]
  have hpair :
      goalError data = State.pair data.adjointWeight (algebraicResidual data) := by
    calc
      goalError data =
        State.pair data.adjointWeight
          (data.operator (State.sub (exactState data) data.computedState)) := hgoal
      _ = State.pair data.adjointWeight (algebraicResidual data) := by
            rw [hres]
  constructor
  · exact hpair
  · calc
      goalError data = State.pair data.adjointWeight (algebraicResidual data) := hpair
      _ =
        goalContributionSum (List.map (fun r => State.pair data.adjointWeight r) data.residualTerms) := by
          unfold algebraicResidual
          exact data.weighted_residual_split

end CoherenceCalculus
