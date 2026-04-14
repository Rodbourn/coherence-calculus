import CoherenceCalculus.Foundation.VariationalSelectionCore
import CoherenceCalculus.Foundation.TransportOrderSelectionCore

/-!
# Foundation.BridgeTransportCore

Manuscript-facing realized transport-order and channel-transport interfaces for
the Chapter 7 bridge program.

This module deliberately stays structural. It packages:

- realized classes whose selected transport bases carry explicit transport-order
  data
- selected channel transport systems on observer graphs

No continuum analysis, gauge theory, or hidden representation machinery is
introduced here.
-/

namespace CoherenceCalculus

/-- A realized class is transport-order disciplined when each realization
carries an explicit transport-order filtered admissible family of selected
transport bases together with a distinguished minimal-order class and a chosen
realized equivalence relation making the minimal subclass singleton modulo that
relation. -/
structure TransportOrderDisciplinedRealizedClass (Index Time : Type)
    extends AdmissibleRealizedClass Index Time where
  transportIndex : Index → Type
  transportFamily :
    ∀ i : Index,
      TransportOrderFilteredFamily (transportIndex i) (datum i).realization.tower
  distinguishedClass :
    ∀ i : Index,
      distinguishedTransportOrderClass (transportFamily i)
  realizedEquivalence :
    ∀ i : Index, transportIndex i → transportIndex i → Prop
  realizedEquivalence_equiv :
    ∀ i : Index, Equivalence (realizedEquivalence i)
  minimal_singleton :
    ∀ i : Index,
      SingletonModulo
        (minimalAdmissibleTransportSubclass
          (transportFamily i)
          (distinguishedClass i))
        (realizedEquivalence i)

/-- In a transport-order disciplined realized class, the minimal admissible
transport order is forced modulo the chosen realized equivalence relation. -/
theorem realized_transport_order_forcing
    {Index Time : Type}
    (cls : TransportOrderDisciplinedRealizedClass Index Time) :
    ∀ i : Index,
      transportOrderForced
        (cls.transportFamily i)
        (cls.distinguishedClass i)
        (cls.realizedEquivalence i) := by
  intro i
  exact
    (minimal_admissible_transport_order
      (cls.transportFamily i)
      (cls.distinguishedClass i)).2
      (cls.realizedEquivalence i)
      (cls.realizedEquivalence_equiv i)
      (cls.minimal_singleton i)

/-- A selected channel transport system is a finite observer graph together
with selected channel fibers and transport maps compatible with the chosen
selected-law symmetry data. The compatibility condition is kept explicit as a
supplied proposition on the packaged data. -/
structure SelectedChannelTransportSystem (Time Vertex : Type) where
  realization : SelectionDatum Time
  edge : Vertex → Vertex → Prop
  fiber : Vertex → Type
  transport :
    ∀ {x y : Vertex}, edge x y → fiber y → fiber x
  symmetryCompatible : Prop

end CoherenceCalculus
