import CoherenceCalculus.Foundation.NatCore

/-!
# Foundation.StructuredChoiceCore

Constructive infinite-thread existence for explicit finite refinement towers.

This is the strongest honest "choice-like" theorem currently available in the
active foundation without adding a global choice principle. Each refinement
fiber is explicitly finite and nonempty by construction, so one can choose the
first index at every stage and thereby build a coherent infinite thread.
-/

namespace CoherenceCalculus

/-- Explicit finite refinement tower. Every parent state carries a nonempty
finite refinement fiber indexed by `Fin`, and each indexed refinement projects
back to the parent. -/
structure FiniteRefinementTower where
  Carrier : Nat → Type
  predecessor : ∀ n, Carrier (n + 1) → Carrier n
  fiberSize : ∀ n, Carrier n → Nat
  fiberElem : ∀ n (x : Carrier n), Fin (Nat.succ (fiberSize n x)) → Carrier (n + 1)
  fiberProjects : ∀ n x i, predecessor n (fiberElem n x i) = x

/-- Rooted finite refinement tower with a nonempty finite initial stage. -/
structure RootedFiniteRefinementTower extends FiniteRefinementTower where
  rootSize : Nat
  rootElem : Fin (Nat.succ rootSize) → Carrier 0

/-- The first explicit refinement above a parent state. -/
def firstRefinement (T : FiniteRefinementTower) (n : Nat) (x : T.Carrier n) :
    T.Carrier (n + 1) :=
  T.fiberElem n x ⟨0, Nat.succ_pos _⟩

/-- The first explicit refinement projects back to its parent. -/
theorem firstRefinement_projects (T : FiniteRefinementTower) (n : Nat)
    (x : T.Carrier n) :
    T.predecessor n (firstRefinement T n x) = x := by
  exact T.fiberProjects n x ⟨0, Nat.succ_pos _⟩

/-- Chosen root at stage zero. -/
def firstRoot (T : RootedFiniteRefinementTower) : T.Carrier 0 :=
  T.rootElem ⟨0, Nat.succ_pos _⟩

/-- Canonical coherent thread above a chosen root. -/
def canonicalThreadFrom (T : FiniteRefinementTower) (x₀ : T.Carrier 0) :
    (n : Nat) → T.Carrier n
  | 0 => x₀
  | n + 1 => firstRefinement T n (canonicalThreadFrom T x₀ n)

/-- The canonical thread is coherent with the predecessor maps. -/
theorem canonicalThreadFrom_coherent (T : FiniteRefinementTower)
    (x₀ : T.Carrier 0) :
    ∀ n, T.predecessor n (canonicalThreadFrom T x₀ (n + 1)) =
      canonicalThreadFrom T x₀ n := by
  intro n
  exact firstRefinement_projects T n (canonicalThreadFrom T x₀ n)

/-- A coherent infinite thread through the tower. -/
structure CoherentThread (T : FiniteRefinementTower) where
  thread : (n : Nat) → T.Carrier n
  coherent : ∀ n, T.predecessor n (thread (n + 1)) = thread n

/-- Every rooted finite refinement tower admits a coherent infinite thread. -/
theorem rooted_coherent_thread_exists (T : RootedFiniteRefinementTower) :
    Nonempty (CoherentThread T.toFiniteRefinementTower) := by
  exact ⟨{
    thread := canonicalThreadFrom T.toFiniteRefinementTower (firstRoot T)
    coherent := canonicalThreadFrom_coherent T.toFiniteRefinementTower (firstRoot T)
  }⟩

/-- Cleaner function-level formulation of the same existence theorem. -/
theorem rooted_selection_thread
    (T : RootedFiniteRefinementTower) :
    ∃ s : (n : Nat) → T.Carrier n,
      ∀ n, T.predecessor n (s (n + 1)) = s n := by
  refine ⟨canonicalThreadFrom T.toFiniteRefinementTower (firstRoot T), ?_⟩
  exact canonicalThreadFrom_coherent T.toFiniteRefinementTower (firstRoot T)

/-- Structured infinite choice for explicit finite refinement towers. -/
theorem structured_infinite_choice
    (T : RootedFiniteRefinementTower) :
    ∃ s : (n : Nat) → T.Carrier n,
      ∀ n, T.predecessor n (s (n + 1)) = s n := by
  exact rooted_selection_thread T

end CoherenceCalculus
