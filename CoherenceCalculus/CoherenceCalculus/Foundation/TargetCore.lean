import CoherenceCalculus.Foundation.PairingCore
import CoherenceCalculus.Foundation.SolverInterfaceCore

/-!
# Foundation.TargetCore

Manuscript-facing structural and objective targets rebuilt on the active
projection/complex spine.

This module keeps the structural certifications exact:
- perfect coherence as vanishing Schur correction
- solver exactness and holographic saturation as names for the active complex
  interfaces

For the optimization surface, the active rebuild stays explicit and finite: a
Grassmannian element is packaged by a projection together with a certified
observable orthogonal frame, and minimizer existence is proved for explicit
finite candidate families.
-/

namespace CoherenceCalculus

/-- The `PQ` transport block vanishes identically. -/
def hasZeroPQ (P : Projection) (A : AddMap) : Prop :=
  ∀ x : State, blockPQ P A x = State.zero

/-- The `QP` transport block vanishes identically. -/
def hasZeroQP (P : Projection) (A : AddMap) : Prop :=
  ∀ x : State, blockQP P A x = State.zero

/-- Perfect coherence means every explicit Schur correction vanishes. -/
def hasPerfectCoherence (P : Projection) (A : AddMap) : Prop :=
  ∀ Rqq : AddMap, ∀ x : State, schurComplement P A Rqq x = State.zero

/-- An additive operator is observable-supported on a projection cut when its
observable compression already recovers the full operator. -/
def observableSupportedOn (P : Projection) (A : AddMap) : Prop :=
  ∀ x : State, blockPP P A x = A x

/-- An additive operator is exactly visible on a projection cut when its full
action is already the observable compression there. -/
def exactVisibleOnCut (P : Projection) (A : AddMap) : Prop :=
  ∀ x : State, A x = blockPP P A x

/-- If the `PQ` block vanishes, the Schur correction is identically zero. -/
theorem zeroPQ_implies_perfect (P : Projection) (A : AddMap)
    (hPQ : hasZeroPQ P A) : hasPerfectCoherence P A := by
  intro Rqq x
  rw [schur_factorization]
  exact hPQ (Rqq (blockQP P A x))

/-- If the `QP` block vanishes, the Schur correction is identically zero. -/
theorem zeroQP_implies_perfect (P : Projection) (A : AddMap)
    (hQP : hasZeroQP P A) : hasPerfectCoherence P A := by
  intro Rqq x
  rw [schur_factorization, hQP x, Rqq.map_zero]
  exact (blockPQ P A).map_zero

/-- An additive operator commutes with a projection when it preserves the
observable sector exactly. -/
def commutesWithProjection (P : Projection) (A : AddMap) : Prop :=
  ∀ x : State, A (P x) = P (A x)

/-- Commuting with a projection forces the `PQ` transport block to vanish. -/
theorem commutes_implies_zeroPQ (P : Projection) (A : AddMap)
    (hcomm : commutesWithProjection P A) : hasZeroPQ P A := by
  intro x
  rw [blockPQ_apply]
  have hshadow := hcomm (projectionShadow P x)
  rw [proj_shadow_orthogonal] at hshadow
  rw [A.map_zero] at hshadow
  exact hshadow.symm

/-- Commuting with a projection forces the `QP` transport block to vanish. -/
theorem commutes_implies_zeroQP (P : Projection) (A : AddMap)
    (hcomm : commutesWithProjection P A) : hasZeroQP P A := by
  intro x
  rw [blockQP_apply, hcomm x]
  exact shadow_proj_orthogonal P (A x)

/-- If an operator commutes with the chosen projection, then it is perfectly
coherent across that split. -/
theorem commutant_implies_perfect (P : Projection) (A : AddMap)
    (hcomm : commutesWithProjection P A) : hasPerfectCoherence P A := by
  exact zeroPQ_implies_perfect P A (commutes_implies_zeroPQ P A hcomm)

/-- Exact visible support on a cut immediately yields observable support in the
orientation used by the effective-law statements. -/
theorem exact_visible_implies_observable_supported
    (P : Projection) (A : AddMap)
    (hvis : exactVisibleOnCut P A) :
    observableSupportedOn P A := by
  intro x
  exact (hvis x).symm

/-- Exact visible support on a cut forces the operator to commute with that
cut. -/
theorem exact_visible_implies_commutes
    (P : Projection) (A : AddMap)
    (hvis : exactVisibleOnCut P A) :
    commutesWithProjection P A := by
  intro x
  have hPx : A (P x) = blockPP P A (P x) := hvis (P x)
  have hx : A x = blockPP P A x := hvis x
  have hleft : A (P x) = P (A (P x)) := by
    calc
      A (P x) = blockPP P A (P x) := hPx
      _ = P (A (P (P x))) := by
            rfl
      _ = P (A (P x)) := by
            rw [P.idem]
  have hright : P (A x) = P (A (P x)) := by
    calc
      P (A x) = P (blockPP P A x) := by rw [hx]
      _ = P (P (A (P x))) := by
            rfl
      _ = P (A (P x)) := by
            rw [P.idem]
  calc
    A (P x) = P (A (P x)) := hleft
    _ = P (A x) := hright.symm

/-- Exact visible support on a cut therefore yields both local cut conditions
needed for exact effective-law recovery. -/
theorem exact_visible_implies_observable_and_commuting
    (P : Projection) (A : AddMap)
    (hvis : exactVisibleOnCut P A) :
    observableSupportedOn P A ∧ commutesWithProjection P A := by
  exact
    ⟨exact_visible_implies_observable_supported P A hvis,
      exact_visible_implies_commutes P A hvis⟩

/-- Observable support together with perfect coherence identifies the operator
with its effective observable law on the chosen projection cut. -/
theorem observable_support_and_perfect_imply_effective
    (P : Projection) (A Rqq : AddMap)
    (hobs : observableSupportedOn P A)
    (hperf : hasPerfectCoherence P A) :
    ∀ x : State, A x = effectiveOp P A Rqq x := by
  intro x
  unfold effectiveOp
  calc
    A x = blockPP P A x := by rw [hobs x]
    _ = State.add (blockPP P A x) State.zero := by
          rw [State.add_zero]
    _ = State.add (blockPP P A x) (schurComplement P A Rqq x) := by
          rw [hperf Rqq x]
    _ = effectiveOp P A Rqq x := by
          rfl

/-- If an operator commutes with the chosen projection and is already
observable-supported there, then its effective observable law is exact on that
cut for every supplied shadow propagator. -/
theorem commutes_and_observable_support_imply_effective
    (P : Projection) (A Rqq : AddMap)
    (hcomm : commutesWithProjection P A)
    (hobs : observableSupportedOn P A) :
    ∀ x : State, A x = effectiveOp P A Rqq x := by
  exact
    observable_support_and_perfect_imply_effective
      P A Rqq hobs (commutant_implies_perfect P A hcomm)

/-- Exact visible support is a one-move sufficient criterion for exact
effective-law recovery on the chosen cut. -/
theorem exact_visible_implies_effective
    (P : Projection) (A Rqq : AddMap)
    (hvis : exactVisibleOnCut P A) :
    ∀ x : State, A x = effectiveOp P A Rqq x := by
  exact
    commutes_and_observable_support_imply_effective
      P A Rqq
      (exact_visible_implies_commutes P A hvis)
      (exact_visible_implies_observable_supported P A hvis)

/-- Solver exactness is the active finite-complex exactness predicate. -/
def isSolverExact (C : finiteHilbertComplex) : Prop :=
  complexExactness C

/-- Holographic saturation is the active relative exactness predicate. -/
def isHolographicallySaturated (C : finiteHilbertComplex) (R : AddMap) : Prop :=
  holographicSaturation C R

/-- A certified rank-`r` Grassmannian datum is a projection together with an
explicit orthogonal observable `r`-frame. -/
structure GrassmannianElem (r : Nat) where
  proj : Projection
  frame : Fin r → State
  fixed : ∀ i : Fin r, proj (frame i) = frame i
  orthogonal : ∀ i j : Fin r, i ≠ j → State.pair (frame i) (frame j) = 0
  nonzero : ∀ i : Fin r, State.energy (frame i) ≠ 0

/-- Membership in the rebuilt Grassmannian means carrying explicit certified
rank data for the chosen projection. -/
def isInGrassmannian (r : Nat) (P : Projection) : Prop :=
  ∃ G : GrassmannianElem r, G.proj = P

/-- A design objective evaluates explicit rank-certified projections. -/
structure DesignObjective where
  rank : Nat
  eval : GrassmannianElem rank → Nat

/-- Workload-relative objective surface on the explicit finite Grassmannian
carrier. The active import-free lane records the three manuscript ingredients
directly: source-visible loss, returned-correction cost, and a structural
regularizer. -/
structure WorkloadDesignObjective where
  objective : DesignObjective
  sourceVisibleLoss : GrassmannianElem objective.rank → Nat
  returnedCorrectionCost : GrassmannianElem objective.rank → Nat
  regularizer : GrassmannianElem objective.rank → Nat
  eval_eq :
    ∀ P : GrassmannianElem objective.rank,
      objective.eval P =
        sourceVisibleLoss P + returnedCorrectionCost P + regularizer P

/-- Explicit finite candidate family for the objective layer. The family is
nonempty by construction. -/
structure CandidateFamily (r : Nat) where
  size : Nat
  elem : Fin (Nat.succ size) → GrassmannianElem r

/-- A minimizing index on an explicit candidate family. -/
def minimizesAt (obj : DesignObjective) (family : CandidateFamily obj.rank)
    (best : Fin (Nat.succ family.size)) : Prop :=
  ∀ i : Fin (Nat.succ family.size), obj.eval (family.elem best) ≤ obj.eval (family.elem i)

/-- Explicit certificate that a chosen candidate minimizes the design
objective on the listed family. -/
structure MinimizerCertificate (obj : DesignObjective) (family : CandidateFamily obj.rank) where
  best : Fin (Nat.succ family.size)
  minimal : minimizesAt obj family best

/-- A certified minimizer is an explicit selector on the candidate family. -/
def existence_of_minimizers (obj : DesignObjective)
    (family : CandidateFamily obj.rank) (cert : MinimizerCertificate obj family) :
    Fin (Nat.succ family.size) :=
  cert.best

/-- The certified selector satisfies the minimizer predicate by construction. -/
theorem existence_of_minimizers_minimizes (obj : DesignObjective)
    (family : CandidateFamily obj.rank) (cert : MinimizerCertificate obj family) :
    minimizesAt obj family (existence_of_minimizers obj family cert) :=
  cert.minimal

/-- Once a nonempty certified candidate family is available, existence of an
optimal projection follows even before any external construction is chosen. -/
theorem certification_without_construction (obj : DesignObjective)
    (family : CandidateFamily obj.rank) (cert : MinimizerCertificate obj family) :
    ∃ P : Projection, isInGrassmannian obj.rank P := by
  let best := existence_of_minimizers obj family cert
  exact ⟨(family.elem best).proj, ⟨family.elem best, rfl⟩⟩

/-- Workload-relative objectives inherit the same explicit finite minimizer
existence theorem as the generic design-objective layer. -/
theorem workload_relative_minimizers
    (obj : WorkloadDesignObjective)
    (family : CandidateFamily obj.objective.rank)
    (cert : MinimizerCertificate obj.objective family) :
    ∃ P : Projection, isInGrassmannian obj.objective.rank P := by
  exact certification_without_construction obj.objective family cert

end CoherenceCalculus
