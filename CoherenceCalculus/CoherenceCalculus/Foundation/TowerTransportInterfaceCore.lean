import CoherenceCalculus.Foundation.ResolventInterfaceCore
import CoherenceCalculus.Foundation.TransportOrderSelectionCore

/-!
# Foundation.TowerTransportInterfaceCore

Manuscript-facing tower-transport interfaces for the Chapter 4 transport and
rigidity surface.

This module keeps the same policy as the rest of the rebuilt spine:

- definitions are packaged explicitly on the active additive-state layer
- theorem surfaces are thin wrappers that extract consequences from explicit
  local data
- no Hilbert-space, Lie-group, or spectral imports are introduced
-/

namespace CoherenceCalculus

/-- The quadratic transport operator attached to a one-step transport base. -/
structure QuadraticTransportOperator where
  transportBase : AddMap
  quadraticTransport : AddMap
  transportEnergyLaw : Prop

/-- Symmetry, phase, and adjoint compatibility data for the transport recursion
operator attached to a chosen one-step base. -/
structure TransportRecursionCompatibilityData (Symm : Type) where
  transportBase : AddMap
  action : Symm → AddMap
  phase : AddMap
  symmetryCompatibility : Prop
  phaseCompatibility : Prop
  adjointCompatibility : Prop
  symmetryCompatibility_valid : symmetryCompatibility
  phaseCompatibility_valid : phaseCompatibility
  adjointCompatibility_valid : adjointCompatibility

/-- The recursion operator inherits exactly the compatibility properties
recorded in the explicit package. -/
theorem transport_recursion_compatibility
    {Symm : Type} (data : TransportRecursionCompatibilityData Symm) :
    data.symmetryCompatibility ∧
      data.phaseCompatibility ∧
      data.adjointCompatibility := by
  exact ⟨data.symmetryCompatibility_valid, data.phaseCompatibility_valid,
    data.adjointCompatibility_valid⟩

/-- Manuscript-facing isotropic transport channel data. -/
structure IsotropicTransportChannel (Symm : Type) where
  transportBase : AddMap
  action : Symm → AddMap
  orthogonalAction : Prop
  irreducibleRealModule : Prop
  transportCommutes :
    ∀ g : Symm, ∀ x : State,
      action g (transportBase x) = transportBase (action g x)

/-- Explicit scalarization data for an isotropic transport channel. -/
structure IsotropicQuadraticTransportData (Symm : Type) where
  channel : IsotropicTransportChannel Symm
  scalarCoeff : Nat
  quadraticScalarization : Prop
  uniqueScalarCoeff : Prop
  hasQuadraticScalarization : quadraticScalarization
  hasUniqueScalarCoeff : uniqueScalarCoeff

/-- An isotropic transport channel carries the packaged scalar quadratic law. -/
theorem isotropic_quadratic_transport
    {Symm : Type} (data : IsotropicQuadraticTransportData Symm) :
    data.quadraticScalarization ∧ data.uniqueScalarCoeff := by
  exact ⟨data.hasQuadraticScalarization, data.hasUniqueScalarCoeff⟩

/-- The isotropic one-step channel packages both scalar quadratic transport and
the canonical reversible recursion law. -/
theorem isotropic_one_step_quadratic_coefficient
    {Symm : Type} (data : IsotropicQuadraticTransportData Symm) :
    data.quadraticScalarization ∧
      (∀ x : SequenceTransportSpace,
        inTransportKernel data.channel.transportBase x ↔
          ∀ n : BilateralIndex,
            x (bilateralSucc n) =
              State.sub (data.channel.transportBase (x n)) (x (bilateralPred n))) := by
  refine ⟨data.hasQuadraticScalarization, ?_⟩
  intro x
  exact reversible_transport_recursion data.channel.transportBase x

/-- Manuscript-facing sphere-transitive transport channel data. -/
structure SphereTransitiveTransportChannel (Symm : Type) where
  transportBase : AddMap
  action : Symm → AddMap
  orthogonalAction : Prop
  sphereTransitive : Prop
  transportCommutes :
    ∀ g : Symm, ∀ x : State,
      action g (transportBase x) = transportBase (action g x)

/-- Explicit irreducibility consequence for a sphere-transitive transport
channel. -/
structure SphereTransitiveIrreducibilityData (Symm : Type) where
  channel : SphereTransitiveTransportChannel Symm
  irreducibilityForced : Prop
  hasIrreducibilityForced : irreducibilityForced

/-- Sphere-transitive transport channels export the packaged irreducibility
consequence. -/
theorem sphere_transitive_implies_irreducible
    {Symm : Type} (data : SphereTransitiveIrreducibilityData Symm) :
    data.irreducibilityForced := by
  exact data.hasIrreducibilityForced

/-- Explicit scalar quadratic transport data for a sphere-transitive channel. -/
structure SphereTransitiveQuadraticTransportData (Symm : Type) where
  channel : SphereTransitiveTransportChannel Symm
  scalarCoeff : Nat
  quadraticScalarization : Prop
  uniqueScalarCoeff : Prop
  hasQuadraticScalarization : quadraticScalarization
  hasUniqueScalarCoeff : uniqueScalarCoeff

/-- Sphere-transitive channels export the packaged scalar quadratic law. -/
theorem sphere_transitive_quadratic_transport
    {Symm : Type} (data : SphereTransitiveQuadraticTransportData Symm) :
    data.quadraticScalarization ∧ data.uniqueScalarCoeff := by
  exact ⟨data.hasQuadraticScalarization, data.hasUniqueScalarCoeff⟩

/-- Manuscript-facing full-orthogonal transport channel data. -/
structure FullOrthogonalTransportChannel where
  transportBase : AddMap
  fullOrthogonalAction : Prop
  transportCommutesWithAllOrthogonal : Prop

/-- Explicit sphere-transitive consequence for a full-orthogonal transport
channel. -/
structure FullOrthogonalSphereTransitiveData where
  channel : FullOrthogonalTransportChannel
  sphereTransitiveForced : Prop
  hasSphereTransitiveForced : sphereTransitiveForced

/-- Full orthogonal covariance exports the packaged sphere-transitive
consequence. -/
theorem full_orthogonal_implies_sphere_transitive
    (data : FullOrthogonalSphereTransitiveData) :
    data.sphereTransitiveForced := by
  exact data.hasSphereTransitiveForced

/-- Explicit scalar quadratic transport data for a full-orthogonal channel. -/
structure FullOrthogonalQuadraticTransportData where
  channel : FullOrthogonalTransportChannel
  scalarCoeff : Nat
  quadraticScalarization : Prop
  uniqueScalarCoeff : Prop
  hasQuadraticScalarization : quadraticScalarization
  hasUniqueScalarCoeff : uniqueScalarCoeff

/-- Full orthogonal covariance exports the packaged scalar quadratic law. -/
theorem full_orthogonal_quadratic_transport
    (data : FullOrthogonalQuadraticTransportData) :
    data.quadraticScalarization ∧ data.uniqueScalarCoeff := by
  exact ⟨data.hasQuadraticScalarization, data.hasUniqueScalarCoeff⟩

/-- Manuscript-facing metric-isotropic quadratic transport data. -/
structure MetricIsotropicQuadraticTransport where
  quadraticTransport : AddMap
  scalarCoeff : Nat
  metricIsotropic : Prop
  scalarQuadraticLaw : Prop
  hasScalarQuadraticLaw : scalarQuadraticLaw

/-- Metric-isotropic quadratic transport exports the packaged scalar law. -/
theorem metric_isotropic_quadratic_scalar
    (data : MetricIsotropicQuadraticTransport) :
    data.scalarQuadraticLaw := by
  exact data.hasScalarQuadraticLaw

/-- Explicit scalar transport data derived from a metric-isotropic quadratic
transport operator. -/
structure MetricIsotropicTransportData where
  transport : QuadraticTransportOperator
  metricIsotropic : MetricIsotropicQuadraticTransport
  scalarTransportLaw : Prop
  hasScalarTransportLaw : scalarTransportLaw

/-- Metric isotropy exports the packaged scalar transport law. -/
theorem metric_isotropic_transport
    (data : MetricIsotropicTransportData) :
    data.scalarTransportLaw := by
  exact data.hasScalarTransportLaw

/-- Manuscript-facing tight isotropic direction-frame data. -/
structure TightIsotropicDirectionFrame (Direction Symm : Type) where
  projection : Direction → AddMap
  action : Symm → AddMap
  transitiveDirectionAction : Prop
  rankOneOrthogonalProjections : ∀ _ : Direction, Prop
  tightFrameLaw : Prop

/-- Manuscript-facing direction-adapted quadratic transport data. -/
structure DirectionAdaptedQuadraticTransport (Direction Symm : Type) where
  frame : TightIsotropicDirectionFrame Direction Symm
  quadraticTransport : AddMap
  directionAdapted : Prop
  quadraticTransportEquivariant : Prop

/-- Explicit scalarization consequence for a transitive direction-adapted
quadratic transport operator. -/
structure TransitiveDirectionIsotropyData (Direction Symm : Type) where
  data : DirectionAdaptedQuadraticTransport Direction Symm
  scalarCoeff : Nat
  scalarQuadraticLaw : Prop
  uniqueScalarCoeff : Prop
  hasScalarQuadraticLaw : scalarQuadraticLaw
  hasUniqueScalarCoeff : uniqueScalarCoeff

/-- Transitive direction isotropy exports the packaged scalar quadratic law. -/
theorem transitive_direction_isotropy
    {Direction Symm : Type}
    (data : TransitiveDirectionIsotropyData Direction Symm) :
    data.scalarQuadraticLaw ∧ data.uniqueScalarCoeff := by
  exact ⟨data.hasScalarQuadraticLaw, data.hasUniqueScalarCoeff⟩

/-- Explicit scalar transport data derived from a direction-frame quadratic
transport package. -/
structure DirectionFrameQuadraticCoefficientData (Direction Symm : Type) where
  data : DirectionAdaptedQuadraticTransport Direction Symm
  scalarCoeff : Nat
  scalarTransportLaw : Prop
  uniqueScalarCoeff : Prop
  hasScalarTransportLaw : scalarTransportLaw
  hasUniqueScalarCoeff : uniqueScalarCoeff

/-- Direction-frame quadratic transport exports the packaged scalar transport
law. -/
theorem direction_frame_quadratic_coefficient
    {Direction Symm : Type}
    (data : DirectionFrameQuadraticCoefficientData Direction Symm) :
    data.scalarTransportLaw ∧ data.uniqueScalarCoeff := by
  exact ⟨data.hasScalarTransportLaw, data.hasUniqueScalarCoeff⟩

/-- Manuscript-facing quadratic transport rigidity package. -/
structure QuadraticTransportRigidityPackage where
  transportBase : AddMap
  isotropicCase : Prop
  sphereTransitiveCase : Prop
  fullOrthogonalCase : Prop
  metricIsotropicCase : Prop
  directionFrameCase : Prop
  rigidCase :
    isotropicCase ∨
      sphereTransitiveCase ∨
      fullOrthogonalCase ∨
      metricIsotropicCase ∨
      directionFrameCase
  scalarCoeff : Nat
  scalarQuadraticLaw : Prop
  uniqueScalarCoeff : Prop
  hasScalarQuadraticLaw : scalarQuadraticLaw
  hasUniqueScalarCoeff : uniqueScalarCoeff

/-- Quadratic transport rigidity exports the packaged scalar quadratic law. -/
theorem quadratic_transport_rigidity
    (data : QuadraticTransportRigidityPackage) :
    data.scalarQuadraticLaw ∧ data.uniqueScalarCoeff := by
  exact ⟨data.hasScalarQuadraticLaw, data.hasUniqueScalarCoeff⟩

/-- Manuscript-facing no-preferred-direction quadratic transport package. -/
structure NoPreferredDirectionQuadraticTransport where
  rigidity : QuadraticTransportRigidityPackage

/-- No preferred direction at quadratic order exports the packaged scalar
quadratic law. -/
theorem no_preferred_direction_quadratic_transport
    (data : NoPreferredDirectionQuadraticTransport) :
    data.rigidity.scalarQuadraticLaw ∧ data.rigidity.uniqueScalarCoeff := by
  exact quadratic_transport_rigidity data.rigidity

/-- Explicit orbit-generated direction-frame data. -/
structure OrbitGeneratedDirectionFrameData (Direction Symm : Type) where
  frame : TightIsotropicDirectionFrame Direction Symm
  frameGeneratedFromOrbit : Prop
  frameConstantFormula : Prop
  hasFrameGeneratedFromOrbit : frameGeneratedFromOrbit
  hasFrameConstantFormula : frameConstantFormula

/-- Orbit-generated direction frames export the packaged frame and constant
formula. -/
theorem orbit_generated_direction_frame
    {Direction Symm : Type}
    (data : OrbitGeneratedDirectionFrameData Direction Symm) :
    data.frameGeneratedFromOrbit ∧ data.frameConstantFormula := by
  exact ⟨data.hasFrameGeneratedFromOrbit, data.hasFrameConstantFormula⟩

/-- Minimal-order admissible candidates control the order profile of every
exact Schur transport-jet coefficient. -/
theorem minimal_transport_order_controls_jet
    {Index : Type} {T : HorizonTower}
    (F : TransportOrderFilteredFamily Index T)
    (d : distinguishedTransportOrderClass F)
    (arith : TowerOrderArithmeticDatum T)
    {h n : Nat}
    {idx : Index}
    (hmin : minimalAdmissibleTransportSubclass F d idx) :
    towerTransportOrderAtMost T
      (schur_transport_jet (T.π h) (F.candidate idx) n)
      ((n + 1) * d.order) := by
  exact (schur_transport_jet_order T arith (F.candidate idx) (h := h) hmin.2).2.2 n

/-- Explicit order-one forcing datum for the minimal admissible transport-order
class. -/
structure OrderOneForcingCriterionDatum
    {Index : Type} {T : HorizonTower}
    (F : TransportOrderFilteredFamily Index T)
    (d : distinguishedTransportOrderClass F) where
  chosenEquivalence : Index → Index → Prop
  chosenEquivalence_equiv : Equivalence chosenEquivalence
  minimalSingleton :
    SingletonModulo (minimalAdmissibleTransportSubclass F d) chosenEquivalence
  orderOneForced : d.order = 1

/-- The distinguished admissible transport-order class is order one once that
conclusion has been supplied explicitly. -/
theorem order_one_forced_transport_order
    {Index : Type} {T : HorizonTower}
    {F : TransportOrderFilteredFamily Index T}
    {d : distinguishedTransportOrderClass F}
    (data : OrderOneForcingCriterionDatum F d) :
    d.order = 1 := by
  exact data.orderOneForced

/-- The minimal admissible subclass is forced modulo the chosen equivalence
relation in an order-one forcing package. -/
theorem order_one_forcing_forced_class
    {Index : Type} {T : HorizonTower}
    {F : TransportOrderFilteredFamily Index T}
    {d : distinguishedTransportOrderClass F}
    (data : OrderOneForcingCriterionDatum F d) :
    transportOrderForced F d data.chosenEquivalence := by
  exact
    (minimal_admissible_transport_order F d).2
      data.chosenEquivalence
      data.chosenEquivalence_equiv
      data.minimalSingleton

/-- Manuscript-facing transport-generated admissible-family data. -/
structure TransportGeneratedAdmissibleFamily (Index : Type) (T : HorizonTower) where
  family : TransportOrderFilteredFamily Index T
  distinguishedClass : distinguishedTransportOrderClass family
  representative : AddMap
  minimalSingletonModulo : Prop
  orderOneForced : distinguishedClass.order = 1
  noPreferredDirection : NoPreferredDirectionQuadraticTransport

/-- Transport generation exports the forced one-step order, the packaged scalar
quadratic law, and the canonical reversible recursion law for the chosen
representative. -/
theorem transport_generation_forces_scalar_recursion
    {Index : Type} {T : HorizonTower}
    (data : TransportGeneratedAdmissibleFamily Index T) :
    data.distinguishedClass.order = 1 ∧
      data.noPreferredDirection.rigidity.scalarQuadraticLaw ∧
      (∀ x : SequenceTransportSpace,
        inTransportKernel data.representative x ↔
          ∀ n : BilateralIndex,
            x (bilateralSucc n) =
              State.sub (data.representative (x n)) (x (bilateralPred n))) := by
  refine ⟨data.orderOneForced, data.noPreferredDirection.rigidity.hasScalarQuadraticLaw, ?_⟩
  intro x
  exact reversible_transport_recursion data.representative x

end CoherenceCalculus
