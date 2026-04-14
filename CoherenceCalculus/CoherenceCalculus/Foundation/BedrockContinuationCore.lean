import CoherenceCalculus.Foundation.NatCore

/-!
# Foundation.BedrockContinuationCore

Explicit bedrock continuation grammar above the primitive/counting layer.

This file keeps the chapter-1 exactification language honest on the active
import-free spine. It does not introduce a global continuation selector or any
new axiom command. Instead it records:

- incidence extension as explicit local data
- terminality as a named Constancy-lift predicate
- closure-defect data as a pointed preordered carrier
- termination as the zero-defect criterion
- nonretroactive exactification as the continuation interface built above that
  criterion

The theorem surface proves only the immediate consequences of those explicit
interfaces.
-/

namespace CoherenceCalculus

/-- Bedrock incidence grammar with an explicit extension relation and a
Constancy-lift predicate. -/
structure IncidenceSystem where
  Incidence : Type
  extendsRel : Incidence → Incidence → Prop
  extends_refl : ∀ I : Incidence, extendsRel I I
  extends_trans :
    ∀ {I J K : Incidence}, extendsRel I J → extendsRel J K → extendsRel I K
  constancyLift : Incidence → Prop

/-- Manuscript-facing alias for the incidence extension relation. -/
def incidenceExtension
    (S : IncidenceSystem) (I J : S.Incidence) : Prop :=
  S.extendsRel I J

/-- Strict extension in the explicit incidence grammar. -/
def strictIncidenceExtension
    (S : IncidenceSystem) (I J : S.Incidence) : Prop :=
  S.extendsRel I J ∧ I ≠ J

/-- Extension is a preorder by construction of the explicit incidence grammar. -/
theorem extension_is_preorder (S : IncidenceSystem) :
    (∀ I : S.Incidence, incidenceExtension S I I) ∧
      (∀ {I J K : S.Incidence},
        incidenceExtension S I J →
        incidenceExtension S J K →
        incidenceExtension S I K) := by
  refine ⟨?_, ?_⟩
  · intro I
    exact S.extends_refl I
  · intro I J K hIJ hJK
    exact S.extends_trans hIJ hJK

/-- Constancy lift on an incidence in the explicit bedrock grammar. -/
def ConstancyLift
    (S : IncidenceSystem) (I : S.Incidence) : Prop :=
  S.constancyLift I

/-- An incidence is terminal exactly when Constancy lifts to it as a whole. -/
def TerminalIncidence
    (S : IncidenceSystem) (I : S.Incidence) : Prop :=
  ConstancyLift S I

/-- Terminality persists along an extension chain in the explicit incidence
grammar: the terminal subincidence remains terminal and remains embedded in the
later incidence. -/
theorem terminal_subincidence_inherited
    (S : IncidenceSystem)
    {K I J : S.Incidence}
    (hKI : incidenceExtension S K I)
    (hIJ : incidenceExtension S I J)
    (hterm : TerminalIncidence S K) :
    incidenceExtension S K J ∧ TerminalIncidence S K := by
  exact ⟨S.extends_trans hKI hIJ, hterm⟩

/-- Pointed preordered carrier for the closure-defect surface. -/
structure ClosureDefectSpace where
  Carrier : Type
  le : Carrier → Carrier → Prop
  zero : Carrier

/-- Explicit closure-defect assignment on an incidence grammar. -/
structure ClosureDefectData (S : IncidenceSystem) where
  space : ClosureDefectSpace
  defect : S.Incidence → space.Carrier

/-- Manuscript-facing alias for the closure-defect assignment. -/
def closureDefect
    {S : IncidenceSystem} (D : ClosureDefectData S) :
    S.Incidence → D.space.Carrier :=
  D.defect

/-- Exactifying continuation class: strict extensions of the current
incidence in the given grammar. -/
def ExactifyingContinuationClass
    (S : IncidenceSystem) (I : S.Incidence) :
    S.Incidence → Prop :=
  strictIncidenceExtension S I

/-- Explicit termination interface on the active bedrock lane: zero closure
defect marks exactly the terminal incidences. -/
structure TerminationData (S : IncidenceSystem)
    extends ClosureDefectData S where
  terminal_iff_zero :
    ∀ I : S.Incidence,
      TerminalIncidence S I ↔ defect I = space.zero

/-- Terminality is exactly the vanishing of the declared closure defect. -/
theorem terminal_iff_zero_defect
    {S : IncidenceSystem}
    (T : TerminationData S)
    (I : S.Incidence) :
    TerminalIncidence S I ↔ T.defect I = T.space.zero :=
  T.terminal_iff_zero I

/-- Terminal incidences carry zero closure defect. -/
theorem terminal_implies_zero_defect
    {S : IncidenceSystem}
    (T : TerminationData S)
    (I : S.Incidence)
    (hterminal : TerminalIncidence S I) :
    T.defect I = T.space.zero :=
  (terminal_iff_zero_defect T I).1 hterminal

/-- Zero closure defect forces terminality. -/
theorem zero_defect_implies_terminal
    {S : IncidenceSystem}
    (T : TerminationData S)
    (I : S.Incidence)
    (hzero : T.defect I = T.space.zero) :
    TerminalIncidence S I :=
  (terminal_iff_zero_defect T I).2 hzero

/-- Any nonterminal incidence carries nonzero closure defect. -/
theorem nonterminal_has_nonzero_defect
    {S : IncidenceSystem}
    (T : TerminationData S)
    (I : S.Incidence)
    (hnonterminal : ¬ TerminalIncidence S I) :
    T.defect I ≠ T.space.zero := by
  intro hzero
  exact hnonterminal (zero_defect_implies_terminal T I hzero)

/-- Explicit nonretroactive exactification interface on the active bedrock
lane. It extends the termination interface by forcing strict continuation of
every unresolved incidence. -/
structure NonretroactiveExactificationData (S : IncidenceSystem)
    extends TerminationData S where
  nonterminal_continues :
    ∀ I : S.Incidence,
      defect I ≠ space.zero →
        ∃ J : S.Incidence, ExactifyingContinuationClass S I J
  zero_defect_extension_strict :
    ∀ {I J : S.Incidence},
      incidenceExtension S I J →
      defect I ≠ space.zero →
      defect J = space.zero →
      ExactifyingContinuationClass S I J

/-- A nonterminal incidence has nonzero closure defect and therefore a nonempty
  exactifying continuation class. -/
theorem nonterminal_incidences_continue
    {S : IncidenceSystem}
    (E : NonretroactiveExactificationData S)
    (I : S.Incidence)
    (hnonterminal : ¬ TerminalIncidence S I) :
    E.defect I ≠ E.space.zero ∧
      ∃ J : S.Incidence, ExactifyingContinuationClass S I J := by
  have hdefect : E.defect I ≠ E.space.zero :=
    nonterminal_has_nonzero_defect E.toTerminationData I hnonterminal
  exact ⟨hdefect, E.nonterminal_continues I hdefect⟩

/-- Zero defect cannot arise in place: once a later incidence closes exactly,
the intervening change is a strict extension of the original one. -/
theorem zero_defect_cannot_arise_in_place
    {S : IncidenceSystem}
    (E : NonretroactiveExactificationData S)
    {I J : S.Incidence}
    (hIJ : incidenceExtension S I J)
    (hdefect : E.defect I ≠ E.space.zero)
    (hzero : E.defect J = E.space.zero) :
    ExactifyingContinuationClass S I J :=
  E.zero_defect_extension_strict hIJ hdefect hzero

end CoherenceCalculus
