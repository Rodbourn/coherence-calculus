import CoherenceCalculus.Foundation.BridgeTransportCore
import CoherenceCalculus.Foundation.TransportCycleCore
import CoherenceCalculus.PartIII.BridgeSupportCore

namespace CoherenceCalculus

structure DiscreteRealizedLawFamily where
  Realization : Nat → Type
  Observed : Nat → Type
  horizon : Nat → Nat
  realization : (n : Nat) → Realization n
  law : (n : Nat) → Observed n → Observed n

structure RefinementCompatibleFamily where
  family : DiscreteRealizedLawFamily
  compare : ∀ {n m : Nat}, n ≤ m → family.Observed n → family.Observed m
  compare_refl :
    ∀ n : Nat, ∀ x : family.Observed n, compare (Nat.le_refl n) x = x
  compare_trans :
    ∀ {n m ℓ : Nat} (hnm : n ≤ m) (hmℓ : m ≤ ℓ) (x : family.Observed n),
      compare hmℓ (compare hnm x) = compare (Nat.le_trans hnm hmℓ) x
  intertwines :
    ∀ {n m : Nat} (hnm : n ≤ m) (x : family.Observed n),
      compare hnm (family.law n x) = family.law m (compare hnm x)
  transported_data_agree : Prop

structure LevelwiseForcedFamilyData (F : RefinementCompatibleFamily) where
  selectedLaw : (n : Nat) → F.family.Observed n → F.family.Observed n
  selected_eq_law :
    ∀ n : Nat, ∀ x : F.family.Observed n, selectedLaw n x = F.family.law n x
  selected_intertwines :
    ∀ {n m : Nat} (hnm : n ≤ m) (x : F.family.Observed n),
      F.compare hnm (selectedLaw n x) = selectedLaw m (F.compare hnm x)
  unique_up_to_levelwise_equivalence : Prop

def forced_discrete_realized_families (F : RefinementCompatibleFamily)
    (data : LevelwiseForcedFamilyData F) :
    LevelwiseForcedFamilyData F := by
  exact data

structure ContinuumReconstructionDatum
    (F : DiscreteRealizedLawFamily) (X₀ X : Type) where
  limits : LimitInterface X
  embed : X₀ → X
  sample : (n : Nat) → X₀ → F.Observed n
  reconstruct : (n : Nat) → F.Observed n → X
  reconstruct_sample :
    ∀ u : X₀,
      limits.tendsTo (fun n => reconstruct n (sample n u)) (embed u)

/-- Manuscript-facing refinement-coherent reconstruction datum: a continuum
reconstruction together with exact compatibility of the sampling and
reconstruction maps with the refinement comparison maps. -/
structure RefinementCoherentReconstructionDatum
    (F : RefinementCompatibleFamily) (X₀ X : Type)
    extends ContinuumReconstructionDatum F.family X₀ X where
  sample_compare :
    ∀ {n m : Nat} (hnm : n ≤ m) (u : X₀),
      sample m u = F.compare hnm (sample n u)
  reconstruct_compare :
    ∀ {n m : Nat} (hnm : n ≤ m) (y : F.family.Observed n),
      reconstruct n y = reconstruct m (F.compare hnm y)

/-- The exact core law extracted from a refinement-coherent reconstruction
datum by evaluating the reconstructed observed law at the root stage. -/
def refinementCoherentCoreLaw
    {F : RefinementCompatibleFamily} {X₀ X : Type}
    (datum : RefinementCoherentReconstructionDatum F X₀ X) :
    X₀ → X :=
  fun u => datum.reconstruct 0 (F.family.law 0 (datum.sample 0 u))

/-- Refinement coherence makes the reconstructed observed law independent of
the refinement stage on the dense test domain. -/
theorem refinementCoherentCoreLaw_stage
    {F : RefinementCompatibleFamily} {X₀ X : Type}
    (datum : RefinementCoherentReconstructionDatum F X₀ X)
    (u : X₀) (n : Nat) :
    refinementCoherentCoreLaw datum u =
      datum.reconstruct n (F.family.law n (datum.sample n u)) := by
  have hsample := datum.sample_compare (Nat.zero_le n) u
  calc
    refinementCoherentCoreLaw datum u
        = datum.reconstruct n
            (F.compare (Nat.zero_le n)
              (F.family.law 0 (datum.sample 0 u))) := by
            simpa [refinementCoherentCoreLaw] using
              datum.reconstruct_compare
                (Nat.zero_le n)
                (F.family.law 0 (datum.sample 0 u))
    _ = datum.reconstruct n
          (F.family.law n
            (F.compare (Nat.zero_le n) (datum.sample 0 u))) := by
          rw [F.intertwines (Nat.zero_le n) (datum.sample 0 u)]
    _ = datum.reconstruct n (F.family.law n (datum.sample n u)) := by
          rw [← hsample]

def AsymptoticConsistency
    (F : DiscreteRealizedLawFamily) {X₀ X : Type}
    (datum : ContinuumReconstructionDatum F X₀ X) (L : X₀ → X) : Prop :=
  ∀ u : X₀,
    datum.limits.tendsTo
      (fun n => datum.reconstruct n (F.law n (datum.sample n u)))
      (L u)

structure StableDiscreteFamily
    (F : DiscreteRealizedLawFamily) {X₀ X : Type}
    (datum : ContinuumReconstructionDatum F X₀ X) where
  stability_witness : Nat
  stable : Prop

/-- Import-free approximation interface for the manuscript's summable
refinement-consistency branch. The analytic norm and series language is
represented here by explicit Nat-valued size, distance, and budget data so the
active bridge lane remains import-free. -/
structure SummableRefinementConsistency
    (F : DiscreteRealizedLawFamily) {X₀ X : Type}
    (datum : ContinuumReconstructionDatum F X₀ X) where
  coreSize : X₀ → Nat
  spaceDist : X → X → Nat
  errorBudget : Nat → Nat
  errorBudget_summable : Prop
  refinement_defect_bound :
    ∀ u : X₀, ∀ n : Nat,
      spaceDist
        (datum.reconstruct (Nat.succ n)
          (F.law (Nat.succ n) (datum.sample (Nat.succ n) u)))
        (datum.reconstruct n (F.law n (datum.sample n u)))
        ≤ errorBudget n * coreSize u

structure ContinuumEquivalence (X₀ X : Type) (L L' : X₀ → X) where
  spaceMap : X → X
  domainMap : X₀ → X₀
  has_inverse_data : Prop
  intertwines : ∀ u : X₀, spaceMap (L u) = L' (domainMap u)

structure ContinuumSymmetryTransport
    (F : DiscreteRealizedLawFamily) {X₀ X : Type}
    (datum : ContinuumReconstructionDatum F X₀ X) where
  spaceMap : X → X
  domainMap : X₀ → X₀
  discreteMap : (n : Nat) → F.Observed n → F.Observed n
  sample_intertwines :
    ∀ n : Nat, ∀ u : X₀,
      discreteMap n (datum.sample n u) = datum.sample n (domainMap u)
  reconstruct_intertwines :
    ∀ n : Nat, ∀ y : F.Observed n,
      spaceMap (datum.reconstruct n y) = datum.reconstruct n (discreteMap n y)
  law_commutes :
    ∀ n : Nat, ∀ y : F.Observed n,
      discreteMap n (F.law n y) = F.law n (discreteMap n y)

theorem continuum_identification_on_dense_test_domain
    (F : DiscreteRealizedLawFamily) {X₀ X : Type}
    (datum : ContinuumReconstructionDatum F X₀ X)
    {L L' : X₀ → X}
    (hL : AsymptoticConsistency F datum L)
    (hL' : AsymptoticConsistency F datum L')
    (symm : ContinuumSymmetryTransport F datum) :
    (∀ u : X₀, L u = L' u) ∧
      (∀ u : X₀, symm.spaceMap (L u) = L (symm.domainMap u)) := by
  refine ⟨?_, ?_⟩
  · intro u
    exact datum.limits.unique (hL u) (hL' u)
  · intro u
    have hbase :
        datum.limits.tendsTo
          (fun n => datum.reconstruct n (F.law n (datum.sample n u)))
          (L u) := hL u
    have hmap :
        datum.limits.tendsTo
          (fun n => symm.spaceMap (datum.reconstruct n (F.law n (datum.sample n u))))
          (symm.spaceMap (L u)) := datum.limits.map symm.spaceMap hbase
    have htransport :
        datum.limits.tendsTo
          (fun n => datum.reconstruct n (F.law n (datum.sample n (symm.domainMap u))))
          (symm.spaceMap (L u)) := by
      apply datum.limits.congr
      · intro n
        calc
          symm.spaceMap (datum.reconstruct n (F.law n (datum.sample n u)))
              = datum.reconstruct n (symm.discreteMap n (F.law n (datum.sample n u))) := by
                  exact symm.reconstruct_intertwines n (F.law n (datum.sample n u))
          _ = datum.reconstruct n (F.law n (symm.discreteMap n (datum.sample n u))) := by
                rw [symm.law_commutes n (datum.sample n u)]
          _ = datum.reconstruct n (F.law n (datum.sample n (symm.domainMap u))) := by
                rw [symm.sample_intertwines n u]
      · exact hmap
    exact datum.limits.unique htransport (hL (symm.domainMap u))

structure ContinuumLimitClass (Law : Type) where
  admissible : Law → Prop

def ForcedContinuumLaw {Law : Type}
    (cls : ContinuumLimitClass Law) (target : Law) : Prop :=
  ForcedSingleton cls.admissible target

theorem discrete_to_continuum_forcing_principle
    {Law : Type} (cls : ContinuumLimitClass Law) (target : Law)
    (hmem : cls.admissible target)
    (hunique : ∀ other : Law, cls.admissible other → other = target) :
    ForcedContinuumLaw cls target := by
  exact forcedSingleton_intro cls.admissible target hmem hunique

/-- Manuscript-facing exact forcing name for the same continuum singleton
principle. -/
theorem exact_discrete_to_continuum_forcing_principle
    {Law : Type} (cls : ContinuumLimitClass Law) (target : Law)
    (hmem : cls.admissible target)
    (hunique : ∀ other : Law, cls.admissible other → other = target) :
    ForcedContinuumLaw cls target := by
  exact discrete_to_continuum_forcing_principle cls target hmem hunique

/-- Active exact-core surface for the manuscript's refinement-coherent
realization theorem: refinement coherence forces a stage-independent core law
on the dense test domain, and that core law is unique among operators with the
same stagewise reconstruction formula. -/
theorem refinement_coherent_core_realization
    {F : RefinementCompatibleFamily} {X₀ X : Type}
    (datum : RefinementCoherentReconstructionDatum F X₀ X) :
    (∀ u : X₀, ∀ n m : Nat, n ≤ m →
      datum.reconstruct m (F.family.law m (datum.sample m u)) =
        datum.reconstruct n (F.family.law n (datum.sample n u))) ∧
      ∃ Lsharp : X₀ → X,
        (∀ u : X₀, ∀ n : Nat,
          Lsharp u = datum.reconstruct n (F.family.law n (datum.sample n u))) ∧
        (∀ L : X₀ → X,
          (∀ u : X₀, ∀ n : Nat,
            L u = datum.reconstruct n (F.family.law n (datum.sample n u))) →
            ∀ u : X₀, L u = Lsharp u) := by
  refine ⟨?_, ?_⟩
  · intro u n m hnm
    calc
      datum.reconstruct m (F.family.law m (datum.sample m u))
          = refinementCoherentCoreLaw datum u := by
              exact (refinementCoherentCoreLaw_stage datum u m).symm
      _ = datum.reconstruct n (F.family.law n (datum.sample n u)) := by
            exact refinementCoherentCoreLaw_stage datum u n
  · refine ⟨refinementCoherentCoreLaw datum, ?_, ?_⟩
    · intro u n
      exact refinementCoherentCoreLaw_stage datum u n
    · intro L hL u
      calc
        L u = datum.reconstruct 0 (F.family.law 0 (datum.sample 0 u)) := by
                exact hL u 0
        _ = refinementCoherentCoreLaw datum u := by
              rfl

/-- A forced continuum law is already a constructively realized selected-family
continuum law on the active bridge surface. -/
theorem selected_family_continuum_realization
    {Law : Type} (cls : ContinuumLimitClass Law) (target : Law)
    (hforced : ForcedContinuumLaw cls target) :
    cls.admissible target ∧
      (∀ other : Law, cls.admissible other → other = target) := by
  exact hforced

/-- On the active exact bridge surface, no ambiguity remains once the selected
continuum law has been forced in its limit class. -/
theorem exact_continuum_realization_no_ambiguity
    {Law : Type} (cls : ContinuumLimitClass Law) (target : Law)
    (hforced : ForcedContinuumLaw cls target) :
    ∀ other : Law, cls.admissible other → other = target := by
  exact hforced.2

/-- Import-free boundedness class for operators defined only on the dense core.
This keeps original-space boundedness explicit rather than importing a
normed-space hierarchy into the active bridge lane. -/
structure CoreBoundedOperatorClass (Domain Codomain : Type) where
  Bounded : (Domain → Codomain) → Prop
  congr :
    ∀ {f g : Domain → Codomain},
      (∀ x : Domain, f x = g x) → Bounded f → Bounded g

/-- Explicit extension interface for bounded operators defined on the dense
core and landing in the ambient space. -/
structure DenseCoreExtensionInterface
    {X₀ X : Type}
    (embed : X₀ → X)
    (coreBounded : CoreBoundedOperatorClass X₀ X)
    (ambientBounded : CoreBoundedOperatorClass X X) where
  extend :
    ∀ {f : X₀ → X}, coreBounded.Bounded f → X → X
  extend_bounded :
    ∀ {f : X₀ → X} (hf : coreBounded.Bounded f),
      ambientBounded.Bounded (extend hf)
  extend_agrees :
    ∀ {f : X₀ → X} (hf : coreBounded.Bounded f) (u : X₀),
      extend hf (embed u) = f u
  unique :
    ∀ {f : X₀ → X} (hf : coreBounded.Bounded f) {g : X → X},
      ambientBounded.Bounded g →
      (∀ u : X₀, g (embed u) = f u) →
      g = extend hf

/-- Explicit finite-stage control interface: marked stages carry bounded
reconstructed laws on the dense test domain. -/
structure FiniteStageBoundednessInterface
    {F : RefinementCompatibleFamily} {X₀ X : Type}
    (datum : RefinementCoherentReconstructionDatum F X₀ X)
    (coreBounded : CoreBoundedOperatorClass X₀ X) where
  finiteStage : Nat → Prop
  finite_stage_bounded :
    ∀ {n : Nat},
      finiteStage n →
      coreBounded.Bounded
        (fun u : X₀ =>
          datum.reconstruct n (F.family.law n (datum.sample n u)))

/-- Explicit graph-completion interface for the exact core law. A graph
controlled map out of the dense core extends canonically to the chosen
completion object, and extensionality on the embedded core controls the
resulting lifts. -/
structure ExactCoreGraphCompletionInterface (X₀ Completion : Type) where
  embed : X₀ → Completion
  GraphControlled : {Y : Type} → (X₀ → Y) → Prop
  controlled_congr :
    ∀ {Y : Type} {f g : X₀ → Y},
      (∀ u : X₀, f u = g u) → GraphControlled f → GraphControlled g
  lift :
    ∀ {Y : Type} (f : X₀ → Y), GraphControlled f → Completion → Y
  lift_agrees :
    ∀ {Y : Type} (f : X₀ → Y) (hf : GraphControlled f) (u : X₀),
      lift f hf (embed u) = f u
  extensional :
    ∀ {Y : Type} {φ ψ : Completion → Y},
      (∀ u : X₀, φ (embed u) = ψ (embed u)) → φ = ψ

/-- One reconstructed stage being bounded on the dense core is enough to force
bounded descent of the exact core law, provided that the original-space
extension mechanism is supplied explicitly. -/
theorem one_stage_bounded_exact_core_forcing
    {F : RefinementCompatibleFamily} {X₀ X : Type}
    (datum : RefinementCoherentReconstructionDatum F X₀ X)
    (coreBounded : CoreBoundedOperatorClass X₀ X)
    (ambientBounded : CoreBoundedOperatorClass X X)
    (extension :
      DenseCoreExtensionInterface datum.embed coreBounded ambientBounded)
    (hstage :
      ∃ n : Nat,
        coreBounded.Bounded
          (fun u : X₀ =>
            datum.reconstruct n (F.family.law n (datum.sample n u)))) :
    ∃ Linf : X → X,
      ambientBounded.Bounded Linf ∧
      (∀ u : X₀, ∀ n : Nat,
        Linf (datum.embed u) =
          datum.reconstruct n (F.family.law n (datum.sample n u))) ∧
      (∀ g : X → X,
        ambientBounded.Bounded g →
        (∀ u : X₀, ∀ n : Nat,
          g (datum.embed u) =
            datum.reconstruct n (F.family.law n (datum.sample n u))) →
        g = Linf) := by
  rcases hstage with ⟨n₀, hn₀⟩
  have hcore :
      coreBounded.Bounded (refinementCoherentCoreLaw datum) := by
    apply coreBounded.congr
    · intro u
      exact (refinementCoherentCoreLaw_stage datum u n₀).symm
    · exact hn₀
  refine ⟨extension.extend hcore, extension.extend_bounded hcore, ?_, ?_⟩
  · intro u n
    calc
      extension.extend hcore (datum.embed u)
          = refinementCoherentCoreLaw datum u := by
              exact extension.extend_agrees hcore u
      _ = datum.reconstruct n (F.family.law n (datum.sample n u)) := by
            exact refinementCoherentCoreLaw_stage datum u n
  · intro g hg hcompat
    apply extension.unique hcore hg
    intro u
    calc
      g (datum.embed u)
          = datum.reconstruct n₀ (F.family.law n₀ (datum.sample n₀ u)) := by
              exact hcompat u n₀
      _ = refinementCoherentCoreLaw datum u := by
            exact (refinementCoherentCoreLaw_stage datum u n₀).symm

/-- The exact core law admits a canonical graph-completed realization once a
constructive graph-completion interface for that law is supplied explicitly. -/
theorem exact_core_graph_completion
    {F : RefinementCompatibleFamily} {X₀ X Completion : Type}
    (datum : RefinementCoherentReconstructionDatum F X₀ X)
    (completion : ExactCoreGraphCompletionInterface X₀ Completion)
    (hbase : completion.GraphControlled datum.embed)
    (hcore : completion.GraphControlled (refinementCoherentCoreLaw datum)) :
    ∃ Igr : Completion → X, ∃ Lbar : Completion → X,
      (∀ u : X₀, Igr (completion.embed u) = datum.embed u) ∧
      (∀ u : X₀, ∀ n : Nat,
        Lbar (completion.embed u) =
          datum.reconstruct n (F.family.law n (datum.sample n u))) ∧
      (∀ {Y : Type}
        (J : X₀ → Y)
        (_hJ : completion.GraphControlled J)
        (I : Y → X)
        (G : Y → X),
        (∀ u : X₀, I (J u) = datum.embed u) →
        (∀ u : X₀, G (J u) = refinementCoherentCoreLaw datum u) →
        ∃ U : Completion → Y,
          (∀ u : X₀, U (completion.embed u) = J u) ∧
          (∀ z : Completion, I (U z) = Igr z) ∧
          (∀ z : Completion, G (U z) = Lbar z)) := by
  refine
    ⟨completion.lift datum.embed hbase,
      completion.lift (refinementCoherentCoreLaw datum) hcore,
      ?_, ?_, ?_⟩
  · intro u
    exact completion.lift_agrees datum.embed hbase u
  · intro u n
    calc
      completion.lift (refinementCoherentCoreLaw datum) hcore (completion.embed u)
          = refinementCoherentCoreLaw datum u := by
              exact completion.lift_agrees (refinementCoherentCoreLaw datum) hcore u
      _ = datum.reconstruct n (F.family.law n (datum.sample n u)) := by
            exact refinementCoherentCoreLaw_stage datum u n
  · intro Y J hJ I G hI hG
    refine ⟨completion.lift J hJ, ?_, ?_, ?_⟩
    · intro u
      exact completion.lift_agrees J hJ u
    · intro z
      have hmaps :
          (fun w : Completion => I (completion.lift J hJ w))
            =
          completion.lift datum.embed hbase := by
        apply completion.extensional
        intro u
        calc
          I (completion.lift J hJ (completion.embed u))
              = I (J u) := by
                  rw [completion.lift_agrees J hJ u]
          _ = datum.embed u := hI u
          _ = completion.lift datum.embed hbase (completion.embed u) := by
                symm
                exact completion.lift_agrees datum.embed hbase u
      exact congrArg (fun φ => φ z) hmaps
    · intro z
      have hmaps :
          (fun w : Completion => G (completion.lift J hJ w))
            =
          completion.lift (refinementCoherentCoreLaw datum) hcore := by
        apply completion.extensional
        intro u
        calc
          G (completion.lift J hJ (completion.embed u))
              = G (J u) := by
                  rw [completion.lift_agrees J hJ u]
          _ = refinementCoherentCoreLaw datum u := hG u
          _ =
            completion.lift (refinementCoherentCoreLaw datum) hcore
              (completion.embed u) := by
                symm
                exact completion.lift_agrees (refinementCoherentCoreLaw datum) hcore u
      exact congrArg (fun φ => φ z) hmaps

/-- A marked finite exact stage closes the continuum bridge on the original
space as soon as finite-stage boundedness and dense-core extension are both
supplied explicitly. -/
theorem finite_exact_stage_closes_continuum_bridge
    {F : RefinementCompatibleFamily} {X₀ X : Type}
    (datum : RefinementCoherentReconstructionDatum F X₀ X)
    (coreBounded : CoreBoundedOperatorClass X₀ X)
    (ambientBounded : CoreBoundedOperatorClass X X)
    (extension :
      DenseCoreExtensionInterface datum.embed coreBounded ambientBounded)
    (finiteData :
      FiniteStageBoundednessInterface datum coreBounded)
    (hfinite : ∃ n : Nat, finiteData.finiteStage n) :
    ∃ Linf : X → X,
      ambientBounded.Bounded Linf ∧
      (∀ u : X₀, ∀ n : Nat,
        Linf (datum.embed u) =
          datum.reconstruct n (F.family.law n (datum.sample n u))) ∧
      (∀ g : X → X,
        ambientBounded.Bounded g →
        (∀ u : X₀, ∀ n : Nat,
          g (datum.embed u) =
            datum.reconstruct n (F.family.law n (datum.sample n u))) →
        g = Linf) := by
  rcases hfinite with ⟨n, hn⟩
  exact
    one_stage_bounded_exact_core_forcing
      datum
      coreBounded
      ambientBounded
      extension
      ⟨n, finiteData.finite_stage_bounded hn⟩

/-- Manuscript-facing scalar-recursive specialization of one-stage bounded
exact-core forcing: once the exact recursion-generator family has been encoded
as a refinement-coherent realized-law family, the same dense-core bounded
descent theorem applies verbatim. -/
theorem one_stage_bounded_exact_scalar_recursion_forces_generator
    {F : RefinementCompatibleFamily} {X₀ X : Type}
    (datum : RefinementCoherentReconstructionDatum F X₀ X)
    (coreBounded : CoreBoundedOperatorClass X₀ X)
    (ambientBounded : CoreBoundedOperatorClass X X)
    (extension :
      DenseCoreExtensionInterface datum.embed coreBounded ambientBounded)
    (hstage :
      ∃ n : Nat,
        coreBounded.Bounded
          (fun u : X₀ =>
            datum.reconstruct n (F.family.law n (datum.sample n u)))) :
    ∃ Linf : X → X,
      ambientBounded.Bounded Linf ∧
      (∀ u : X₀, ∀ n : Nat,
        Linf (datum.embed u) =
          datum.reconstruct n (F.family.law n (datum.sample n u))) ∧
      (∀ g : X → X,
        ambientBounded.Bounded g →
        (∀ u : X₀, ∀ n : Nat,
          g (datum.embed u) =
            datum.reconstruct n (F.family.law n (datum.sample n u))) →
        g = Linf) := by
  exact
    one_stage_bounded_exact_core_forcing
      datum coreBounded ambientBounded extension hstage

/-- Manuscript-facing scalar-recursive specialization of exact-core graph
completion. Once the exact recursion-generator family is read through the same
refinement-coherent datum, its canonical graph realization is the same
constructive lift package. -/
theorem exact_scalar_recursion_graph_realization
    {F : RefinementCompatibleFamily} {X₀ X Completion : Type}
    (datum : RefinementCoherentReconstructionDatum F X₀ X)
    (completion : ExactCoreGraphCompletionInterface X₀ Completion)
    (hbase : completion.GraphControlled datum.embed)
    (hcore : completion.GraphControlled (refinementCoherentCoreLaw datum)) :
    ∃ Igr : Completion → X, ∃ Lbar : Completion → X,
      (∀ u : X₀, Igr (completion.embed u) = datum.embed u) ∧
      (∀ u : X₀, ∀ n : Nat,
        Lbar (completion.embed u) =
          datum.reconstruct n (F.family.law n (datum.sample n u))) ∧
      (∀ {Y : Type}
        (J : X₀ → Y)
        (_hJ : completion.GraphControlled J)
        (I : Y → X)
        (G : Y → X),
        (∀ u : X₀, I (J u) = datum.embed u) →
        (∀ u : X₀, G (J u) = refinementCoherentCoreLaw datum u) →
        ∃ U : Completion → Y,
          (∀ u : X₀, U (completion.embed u) = J u) ∧
          (∀ z : Completion, I (U z) = Igr z) ∧
          (∀ z : Completion, G (U z) = Lbar z)) := by
  exact exact_core_graph_completion datum completion hbase hcore

/-- Manuscript-facing scalar-recursive specialization of the finite-stage
bounded descent theorem. -/
theorem finite_exact_channel_stage_forces_bounded_generator
    {F : RefinementCompatibleFamily} {X₀ X : Type}
    (datum : RefinementCoherentReconstructionDatum F X₀ X)
    (coreBounded : CoreBoundedOperatorClass X₀ X)
    (ambientBounded : CoreBoundedOperatorClass X X)
    (extension :
      DenseCoreExtensionInterface datum.embed coreBounded ambientBounded)
    (finiteData :
      FiniteStageBoundednessInterface datum coreBounded)
    (hfinite : ∃ n : Nat, finiteData.finiteStage n) :
    ∃ Linf : X → X,
      ambientBounded.Bounded Linf ∧
      (∀ u : X₀, ∀ n : Nat,
        Linf (datum.embed u) =
          datum.reconstruct n (F.family.law n (datum.sample n u))) ∧
      (∀ g : X → X,
        ambientBounded.Bounded g →
        (∀ u : X₀, ∀ n : Nat,
          g (datum.embed u) =
            datum.reconstruct n (F.family.law n (datum.sample n u))) →
        g = Linf) := by
  exact
    finite_exact_stage_closes_continuum_bridge
      datum coreBounded ambientBounded extension finiteData hfinite

/-- Manuscript-facing temporal-generator packaging of the same finite-stage
bounded descent surface. When the exact selected channel family is already the
temporal generator family, no further theorem is needed beyond the finite-stage
scalar-recursive specialization above. -/
theorem finite_exact_channel_stage_yields_bounded_temporal_generator
    {F : RefinementCompatibleFamily} {X₀ X : Type}
    (datum : RefinementCoherentReconstructionDatum F X₀ X)
    (coreBounded : CoreBoundedOperatorClass X₀ X)
    (ambientBounded : CoreBoundedOperatorClass X X)
    (extension :
      DenseCoreExtensionInterface datum.embed coreBounded ambientBounded)
    (finiteData :
      FiniteStageBoundednessInterface datum coreBounded)
    (hfinite : ∃ n : Nat, finiteData.finiteStage n) :
    ∃ Linf : X → X,
      ambientBounded.Bounded Linf ∧
      (∀ u : X₀, ∀ n : Nat,
        Linf (datum.embed u) =
          datum.reconstruct n (F.family.law n (datum.sample n u))) ∧
      (∀ g : X → X,
        ambientBounded.Bounded g →
        (∀ u : X₀, ∀ n : Nat,
          g (datum.embed u) =
            datum.reconstruct n (F.family.law n (datum.sample n u))) →
        g = Linf) := by
  exact
    finite_exact_channel_stage_forces_bounded_generator
      datum coreBounded ambientBounded extension finiteData hfinite

theorem discrete_to_continuum_forcing
    {Law : Type} (cls : ContinuumLimitClass Law) (target : Law)
    (hmem : cls.admissible target)
    (hunique : ∀ other : Law, cls.admissible other → other = target) :
    ForcedContinuumLaw cls target := by
  exact discrete_to_continuum_forcing_principle cls target hmem hunique

structure LocalStencilFamilyInterpretation where
  packaged_as_observed_sector : Prop
  refinement_maps_supply_comparison : Prop
  reconstruction_interface_available : Prop

structure ContinuousHorizonInterpolation (Parameter X : Type) where
  projection : Parameter → Endo X
  shadow : Parameter → Endo X
  operator_norm_C1 : Prop

structure ContinuousBlockDerivativeDatum (Parameter X : Type) where
  interpolation : ContinuousHorizonInterpolation Parameter X
  operator : Endo X
  blockPP : Parameter → Endo X
  blockPQ : Parameter → Endo X
  blockQP : Parameter → Endo X
  blockQQ : Parameter → Endo X
  derivative_PP : Prop
  derivative_PQ : Prop
  derivative_QP : Prop
  derivative_QQ : Prop

def continuous_block_derivatives {Parameter X : Type}
    (data : ContinuousBlockDerivativeDatum Parameter X) :
    ContinuousBlockDerivativeDatum Parameter X := by
  exact data

structure ContinuousEffectiveFlowData (Parameter X : Type) where
  blockData : ContinuousBlockDerivativeDatum Parameter X
  effectiveOp : Parameter → Endo X
  flow_is_C1 : Prop
  flow_formula : Prop

def continuous_effective_flow {Parameter X : Type}
    (data : ContinuousEffectiveFlowData Parameter X) :
    ContinuousEffectiveFlowData Parameter X := by
  exact data

structure ContinuousFlowVsTowerDerivative where
  comparison_available : Prop

structure PromotedConstitutiveContext (Observed Ambient : Type) where
  project : Ambient → Ambient
  transport : Ambient → Ambient
  nonlinear : Ambient → Ambient
  reconstruct : Observed → Ambient
  combine : Ambient → Ambient → Ambient

def PromotedConstitutiveTerm {Observed Ambient : Type}
    (ctx : PromotedConstitutiveContext Observed Ambient) (p : Observed) : Ambient :=
  ctx.project (ctx.nonlinear (ctx.reconstruct p))

def promotedObservedLaw {Observed Ambient : Type}
    (ctx : PromotedConstitutiveContext Observed Ambient) (p : Observed) : Ambient :=
  ctx.combine
    (ctx.project (ctx.transport (ctx.reconstruct p)))
    (PromotedConstitutiveTerm ctx p)

structure FiberedPromotedConstitutiveContext (Observed Ambient : Type) where
  project : Observed → Ambient → Ambient
  transport : Observed → Ambient → Ambient
  nonlinear : Observed → Ambient → Ambient
  reconstruct : Observed → Ambient
  combine : Observed → Ambient → Ambient → Ambient

def FiberedPromotedConstitutiveTerm {Observed Ambient : Type}
    (ctx : FiberedPromotedConstitutiveContext Observed Ambient)
    (p : Observed) : Ambient :=
  ctx.project p (ctx.nonlinear p (ctx.reconstruct p))

def fiberedPromotedObservedLaw {Observed Ambient : Type}
    (ctx : FiberedPromotedConstitutiveContext Observed Ambient)
    (p : Observed) : Ambient :=
  ctx.combine p
    (ctx.project p (ctx.transport p (ctx.reconstruct p)))
    (FiberedPromotedConstitutiveTerm ctx p)

structure CharacteristicScalePromotionData {Observed Ambient : Type}
    (ctx : PromotedConstitutiveContext Observed Ambient) where
  solution_bijection : Prop
  boundary_identity : Prop
  transported_test_identity : Prop

def characteristic_scale_promotion {Observed Ambient : Type}
    (ctx : PromotedConstitutiveContext Observed Ambient)
    (data : CharacteristicScalePromotionData ctx) :
    CharacteristicScalePromotionData ctx := by
  exact data

structure FiberedCharacteristicScalePromotionData {Observed Ambient : Type}
    (ctx : FiberedPromotedConstitutiveContext Observed Ambient) where
  solution_bijection : Prop
  boundary_identity : Prop
  transported_test_identity : Prop

def fibered_characteristic_scale_promotion {Observed Ambient : Type}
    (ctx : FiberedPromotedConstitutiveContext Observed Ambient)
    (data : FiberedCharacteristicScalePromotionData ctx) :
    FiberedCharacteristicScalePromotionData ctx := by
  exact data

structure AdmissiblePromotionData (Law : Type) where
  length : Nat
  selectedLaw : Nat → Law
  unique_step : ∀ n : Nat, n ≤ length → Prop

def admissible_promotion {Law : Type} (data : AdmissiblePromotionData Law) :
    AdmissiblePromotionData Law := by
  exact data

structure FiberedAdmissiblePromotionData (Parameter Law : Type) where
  length : Nat
  selectedLaw : Nat → Parameter → Law
  unique_step : ∀ n : Nat, n ≤ length → Prop

def fibered_admissible_promotion {Parameter Law : Type}
    (data : FiberedAdmissiblePromotionData Parameter Law) :
    FiberedAdmissiblePromotionData Parameter Law := by
  exact data

structure CarriedTransportVersusInheritedClosure where
  transport_is_carried : Prop
  closure_is_promoted : Prop

structure TypedPromotionFiniteCarrier where
  finite_carrier_available : Prop
  canonical_signature_available : Prop
  three_parameter_control : Prop

structure MinimumEnergyPromotion where
  minimum_energy_branch : Prop
  admissibility_interpretation : Prop

structure FiberedMinimumEnergyPromotion where
  minimum_energy_branch : Prop
  admissibility_interpretation : Prop

/-- Wrapper data for the inherited minimal-order closure-class corollary: one
realized transport-order class together with the continuum singleton data it
induces. -/
structure InheritedMinimalOrderClosureClassData
    (Index Time Law : Type) where
  realizedClass : TransportOrderDisciplinedRealizedClass Index Time
  index : Index
  continuumClass : ContinuumLimitClass Law
  selectedLaw : Law
  selected_mem : continuumClass.admissible selectedLaw
  selected_unique :
    ∀ other : Law, continuumClass.admissible other → other = selectedLaw

namespace InheritedMinimalOrderClosureClassData

/-- The realized transport-order class already forces the distinguished
transport-order law at the selected index. -/
theorem transportSurface
    {Index Time Law : Type}
    (data : InheritedMinimalOrderClosureClassData Index Time Law) :
    transportOrderForced
      (data.realizedClass.transportFamily data.index)
      (data.realizedClass.distinguishedClass data.index)
      (data.realizedClass.realizedEquivalence data.index) := by
  exact realized_transport_order_forcing data.realizedClass data.index

/-- The continuum singleton data already force the chosen inherited minimal
order closure law. -/
theorem continuumSurface
    {Index Time Law : Type}
    (data : InheritedMinimalOrderClosureClassData Index Time Law) :
    ForcedContinuumLaw data.continuumClass data.selectedLaw := by
  exact
    discrete_to_continuum_forcing_principle
      data.continuumClass
      data.selectedLaw
      data.selected_mem
      data.selected_unique

end InheritedMinimalOrderClosureClassData

/-- The inherited minimal-order closure class is forced by the realized
transport-order discipline together with the continuum singleton datum. -/
theorem inherited_minimal_order_closure_class
    {Index Time Law : Type}
    (data : InheritedMinimalOrderClosureClassData Index Time Law) :
    transportOrderForced
      (data.realizedClass.transportFamily data.index)
      (data.realizedClass.distinguishedClass data.index)
      (data.realizedClass.realizedEquivalence data.index) ∧
      ForcedContinuumLaw data.continuumClass data.selectedLaw := by
  exact ⟨data.transportSurface, data.continuumSurface⟩

/-- Primitive-support spectral defect families package exactly the structural
requirements listed in the manuscript's seed-side continuum discussion. -/
structure PrimitiveSupportSpectralDefectFamily (Law : Type) where
  selectedLaw : Nat → Law
  unitSeedCarrier : Prop
  visibleSpectralLaw : Prop
  primitiveSupportGenerated : Prop
  repeatedSupportNoNewChannel : Prop
  unitSeedCarrier_valid : unitSeedCarrier
  visibleSpectralLaw_valid : visibleSpectralLaw
  primitiveSupportGenerated_valid : primitiveSupportGenerated
  repeatedSupportNoNewChannel_valid : repeatedSupportNoNewChannel

namespace PrimitiveSupportSpectralDefectFamily

/-- The primitive-support spectral-defect family already carries the seed-side
carrier and visible-spectral clauses singled out in the manuscript. -/
theorem seedSurface
    {Law : Type}
    (family : PrimitiveSupportSpectralDefectFamily Law) :
    family.unitSeedCarrier ∧
      family.visibleSpectralLaw := by
  exact
    ⟨family.unitSeedCarrier_valid,
      family.visibleSpectralLaw_valid⟩

/-- The primitive-support spectral-defect family also carries the support-side
generation and no-new-channel clauses needed for the refinement step. -/
theorem supportSurface
    {Law : Type}
    (family : PrimitiveSupportSpectralDefectFamily Law) :
    family.primitiveSupportGenerated ∧
      family.repeatedSupportNoNewChannel := by
  exact
    ⟨family.primitiveSupportGenerated_valid,
      family.repeatedSupportNoNewChannel_valid⟩

/-- The primitive-support spectral-defect family already carries the full
seed-side structural surface listed in the manuscript discussion. -/
theorem structuralSurface
    {Law : Type}
    (family : PrimitiveSupportSpectralDefectFamily Law) :
    family.unitSeedCarrier ∧
      family.visibleSpectralLaw ∧
      family.primitiveSupportGenerated ∧
      family.repeatedSupportNoNewChannel := by
  exact
    ⟨family.seedSurface.1,
      family.seedSurface.2,
      family.supportSurface.1,
      family.supportSurface.2⟩

end PrimitiveSupportSpectralDefectFamily

/-- Primitive-support towers inherit the prime-index refinement law from the
certified cyclic-refinement interface. -/
theorem primitive_support_prime_refinement
    {Law : Type}
    (family : PrimitiveSupportSpectralDefectFamily Law)
    (data : CyclicRefinementPrimeInvariantData) :
    family.primitiveSupportGenerated ∧ data.samePrimeIndexMultiset := by
  exact
    ⟨family.supportSurface.1,
      cyclic_refinement_prime_invariant data⟩

/-- Wrapper data for the forced continuum spectral-defect corollary on
primitive-support towers. -/
structure PrimitiveSupportContinuumSpectralDefectData (Law : Type) where
  family : PrimitiveSupportSpectralDefectFamily Law
  continuumClass : ContinuumLimitClass Law
  target : Law
  selfAdjointPositiveSemidefinite : Prop
  target_mem : continuumClass.admissible target
  target_unique :
    ∀ other : Law, continuumClass.admissible other → other = target
  selfAdjointPositiveSemidefinite_valid : selfAdjointPositiveSemidefinite

namespace PrimitiveSupportContinuumSpectralDefectData

/-- The primitive-support spectral-defect data already carry the self-adjoint
positive-semidefinite spectral face singled out in the manuscript. -/
theorem spectralSurface
    {Law : Type}
    (data : PrimitiveSupportContinuumSpectralDefectData Law) :
    data.selfAdjointPositiveSemidefinite := by
  exact data.selfAdjointPositiveSemidefinite_valid

/-- The continuum singleton data already force the selected primitive-support
spectral-defect law. -/
theorem continuumSurface
    {Law : Type}
    (data : PrimitiveSupportContinuumSpectralDefectData Law) :
    ForcedContinuumLaw data.continuumClass data.target := by
  exact
    discrete_to_continuum_forcing_principle
      data.continuumClass
      data.target
      data.target_mem
      data.target_unique

end PrimitiveSupportContinuumSpectralDefectData

/-- Primitive-support towers force the packaged continuum spectral-defect law
once the continuum singleton data are supplied explicitly. -/
theorem primitive_support_continuum_spectral_defect
    {Law : Type}
    (data : PrimitiveSupportContinuumSpectralDefectData Law) :
    data.selfAdjointPositiveSemidefinite ∧
      ForcedContinuumLaw data.continuumClass data.target := by
  exact ⟨data.spectralSurface, data.continuumSurface⟩

end CoherenceCalculus
