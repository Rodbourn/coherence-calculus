import CoherenceCalculus.Foundation.HorizonCore

/-!
# Foundation.OrientationCore

Minimal orientation-only examples for the active rebuilt spine.

The manuscript's opening example uses a four-vertex path graph together with a
two-block coarse observation. The active foundation does not rebuild the old
scalar-valued graph layer, so this module records only the combinatorial path
and the corresponding state-level block-coarsening projection.
-/

namespace CoherenceCalculus

/-- Minimal finite directed graph data for orientation examples. -/
structure FiniteDirectedGraph where
  vertexCount : Nat
  edges : List (Nat × Nat)

/-- The canonical four-vertex path `0 -> 1 -> 2 -> 3`. -/
def pathGraph4 : FiniteDirectedGraph where
  vertexCount := 4
  edges := [(0, 1), (1, 2), (2, 3)]

/-- Active state-level surrogate for the manuscript's two-block averaging
picture: the first block `{0,1}` is collapsed to its left representative, and
the second block `{2,3}` is collapsed similarly. -/
def blockAverageProj4 : Projection where
  toFun := fun x =>
    { c0 := x.c0
      c1 := x.c0
      c2 := x.c2
      c3 := x.c2 }
  map_add := by
    intro x y
    apply State.ext <;> rfl
  map_zero := rfl
  idem := by
    intro x
    apply State.ext <;> rfl

end CoherenceCalculus
