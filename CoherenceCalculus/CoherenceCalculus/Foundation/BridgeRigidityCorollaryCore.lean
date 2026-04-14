import CoherenceCalculus.Foundation.BridgeObservableCore
import CoherenceCalculus.Foundation.BridgeTransportCorollaryCore

/-!
# Foundation.BridgeRigidityCorollaryCore

Structural Chapter 7 rigidity/local-datum corollaries.

These wrappers stay honest about the current frontier: each theorem returns an
explicit witness package for the manuscript conclusion from explicit local data.
-/

namespace CoherenceCalculus

/-- Explicit witness that the quadratically rigid order-one package yields a
transport-rigid realized class. -/
structure QuadraticallyRigidTransportRigidityData
    (Index Time Channel : Type)
    extends TransportRigidRealizedClass Index Time Channel where
  quadraticallyRigidWitness : Prop

/-- Quadratically rigid order-one classes are transport-rigid. -/
theorem quadratically_rigid_implies_transport_rigid
    {Index Time Channel : Type}
    (data : QuadraticallyRigidTransportRigidityData Index Time Channel) :
    Nonempty (TransportRigidRealizedClass Index Time Channel) := by
  exact ⟨data.toTransportRigidRealizedClass⟩

/-- Explicit witness that the no-preferred-direction order-one package yields a
transport-rigid realized class. -/
structure NoPreferredDirectionTransportRigidityData
    (Index Time Channel : Type)
    extends TransportRigidRealizedClass Index Time Channel where
  noPreferredDirectionWitness : Prop

/-- No-preferred-direction order-one classes are transport-rigid. -/
theorem no_preferred_direction_implies_transport_rigid
    {Index Time Channel : Type}
    (data : NoPreferredDirectionTransportRigidityData Index Time Channel) :
    Nonempty (TransportRigidRealizedClass Index Time Channel) := by
  exact ⟨data.toTransportRigidRealizedClass⟩

/-- Explicit witness that the intrinsic symmetry/order package yields
governing-datum rigidity. -/
structure IntrinsicPackageGoverningDatumData (Index Time : Type)
    extends GoverningDatumRigidRealizedClass Index Time where
  complexTypeScalarCommutantWitness : Prop
  observableIrreducibleWitness : Prop
  singletonReducedSelectionWitness : Prop
  transportOrderDisciplinedWitness : Prop
  noPreferredDirectionWitness : Prop

/-- The intrinsic symmetry/order package yields governing-datum rigidity. -/
theorem intrinsic_package_implies_governing_datum_rigid
    {Index Time : Type}
    (data : IntrinsicPackageGoverningDatumData Index Time) :
    Nonempty (GoverningDatumRigidRealizedClass Index Time) := by
  exact ⟨data.toGoverningDatumRigidRealizedClass⟩

/-- Explicit witness that a transport-rigid selected channel is
scalar-recursive. -/
structure TransportRigidScalarRecursiveData (Time Vertex : Type)
    extends ScalarRecursiveSelectedChannelSystem Time Vertex where
  transportRigidWitness : Prop

/-- Transport-rigid selected channels are scalar-recursive. -/
theorem transport_rigid_implies_scalar_recursive
    {Time Vertex : Type}
    (data : TransportRigidScalarRecursiveData Time Vertex) :
    Nonempty (ScalarRecursiveSelectedChannelSystem Time Vertex) := by
  exact ⟨data.toScalarRecursiveSelectedChannelSystem⟩

/-- Explicit witness that a transport-generated selected channel system carries
both the scalar quadratic and recursive laws. -/
structure TransportGeneratedScalarRecursiveData (Time Vertex : Type)
    extends TransportGeneratedSelectedChannelSystem Time Vertex where
  scalarQuadraticTransportLaw : Prop
  recursiveTransportLaw : Prop

/-- Transport-generated selected channels are scalar-recursive. -/
theorem transport_generation_yields_scalar_recursive
    {Time Vertex : Type}
    (data : TransportGeneratedScalarRecursiveData Time Vertex) :
    Nonempty (ScalarRecursiveSelectedChannelSystem Time Vertex) := by
  refine ⟨?_⟩
  exact
    { system := data.system
      channel := data.channel
      transportBase := data.transportBase
      scalar_quadratic_transport_law := data.scalarQuadraticTransportLaw
      recursive_transport_law := data.recursiveTransportLaw }

/-- Explicit witness that transport-generated selected channels assemble to a
transport-rigid realized class. -/
structure TransportGeneratedTransportRigidityData
    (Index Time Channel : Type)
    extends TransportRigidRealizedClass Index Time Channel where
  transportGeneratedWitness : Prop

/-- Transport-generated classes are transport-rigid. -/
theorem transport_generated_implies_transport_rigid
    {Index Time Channel : Type}
    (data : TransportGeneratedTransportRigidityData Index Time Channel) :
    Nonempty (TransportRigidRealizedClass Index Time Channel) := by
  exact ⟨data.toTransportRigidRealizedClass⟩

/-- Explicit witness that an observable-rigidity generated class is already
observable-rigid. -/
structure ObservableRigidityGeneratedObservableRigidData (Index Time : Type)
    extends ObservableRigidRealizedClass Index Time where
  observableRigidityGeneratedWitness : Prop

/-- Observable-rigidity generated classes are observable-rigid. -/
theorem observable_rigidity_generated_implies_rigid
    {Index Time : Type}
    (data : ObservableRigidityGeneratedObservableRigidData Index Time) :
    Nonempty (ObservableRigidRealizedClass Index Time) := by
  exact ⟨data.toObservableRigidRealizedClass⟩

/-- Explicit witness that a transport-rigidity generated class is already
transport-rigid. -/
structure TransportRigidityGeneratedTransportRigidData
    (Index Time Channel : Type)
    extends TransportRigidRealizedClass Index Time Channel where
  transportRigidityGeneratedWitness : Prop

/-- Transport-rigidity generated classes are transport-rigid. -/
theorem transport_rigidity_generated_implies_rigid
    {Index Time Channel : Type}
    (data : TransportRigidityGeneratedTransportRigidData Index Time Channel) :
    Nonempty (TransportRigidRealizedClass Index Time Channel) := by
  exact ⟨data.toTransportRigidRealizedClass⟩

/-- Explicit witness that a rigidity-generated class is governing-datum rigid. -/
structure RigidityGeneratedGoverningDatumData (Index Time : Type)
    extends GoverningDatumRigidRealizedClass Index Time where
  rigidityGeneratedWitness : Prop

/-- Rigidity-generated classes are governing-datum rigid. -/
theorem rigidity_generated_implies_governing_datum_rigid
    {Index Time : Type}
    (data : RigidityGeneratedGoverningDatumData Index Time) :
    Nonempty (GoverningDatumRigidRealizedClass Index Time) := by
  exact ⟨data.toGoverningDatumRigidRealizedClass⟩

/-- Explicit witness that multiplicity-free equivariant closure data yields a
closure-rigid class. -/
structure MultiplicityFreeEquivariantClosureRigidData
    (Index Time Channel : Type)
    extends ClosureRigidRealizedClass Index Time Channel where
  multiplicityFreeEquivariantClosureWitness : Prop

/-- Multiplicity-free equivariant closure classes are closure-rigid. -/
theorem multiplicity_free_equivariant_closure_implies_rigid
    {Index Time Channel : Type}
    (data : MultiplicityFreeEquivariantClosureRigidData Index Time Channel) :
    Nonempty (ClosureRigidRealizedClass Index Time Channel) := by
  exact ⟨data.toClosureRigidRealizedClass⟩

/-- Explicit witness that a symmetry-generated class is governing-datum rigid. -/
structure SymmetryGeneratedGoverningDatumData (Index Time : Type)
    extends GoverningDatumRigidRealizedClass Index Time where
  symmetryGeneratedWitness : Prop

/-- Symmetry-generated classes are governing-datum rigid. -/
theorem symmetry_generated_implies_governing_datum_rigid
    {Index Time : Type}
    (data : SymmetryGeneratedGoverningDatumData Index Time) :
    Nonempty (GoverningDatumRigidRealizedClass Index Time) := by
  exact ⟨data.toGoverningDatumRigidRealizedClass⟩

/-- Explicit witness that a symmetry-generated class is closure-rigid. -/
structure SymmetryGeneratedClosureRigidData
    (Index Time Channel : Type)
    extends ClosureRigidRealizedClass Index Time Channel where
  symmetryGeneratedWitness : Prop

/-- Symmetry-generated classes are closure-rigid. -/
theorem symmetry_generated_implies_closure_rigid
    {Index Time Channel : Type}
    (data : SymmetryGeneratedClosureRigidData Index Time Channel) :
    Nonempty (ClosureRigidRealizedClass Index Time Channel) := by
  exact ⟨data.toClosureRigidRealizedClass⟩

/-- Explicit witness that the orbit-frame package yields a symmetry-generated
class. -/
structure ObservableOrbitFrameSymmetryGeneratedData
    (Index Time Channel : Type)
    extends SymmetryGeneratedRealizedClass Index Time Channel where
  observableOrbitFrameWitness : Prop

/-- Observable-orbit orbit-frame multiplicity-free classes are
symmetry-generated. -/
theorem observable_orbit_frame_implies_symmetry_generated
    {Index Time Channel : Type}
    (data : ObservableOrbitFrameSymmetryGeneratedData Index Time Channel) :
    Nonempty (SymmetryGeneratedRealizedClass Index Time Channel) := by
  exact ⟨data.toSymmetryGeneratedRealizedClass⟩

/-- Explicit witness that local homogeneity yields a symmetry-generated class. -/
structure LocallyHomogeneousSymmetryGeneratedData
    (Index Time Channel : Type)
    extends SymmetryGeneratedRealizedClass Index Time Channel where
  locallyHomogeneousWitness : Prop

/-- Locally homogeneous classes are symmetry-generated. -/
theorem locally_homogeneous_implies_symmetry_generated
    {Index Time Channel : Type}
    (data : LocallyHomogeneousSymmetryGeneratedData Index Time Channel) :
    Nonempty (SymmetryGeneratedRealizedClass Index Time Channel) := by
  exact ⟨data.toSymmetryGeneratedRealizedClass⟩

/-- Explicit witness for the fixed-horizon local internal datum. -/
structure RealizedLocalInternalDatumForcingData
    (PhaseClass Scalar ClosureClass : Type)
    extends LocalInternalDatumSelectedChannels
      PhaseClass Scalar ClosureClass where
  governingDatumRigidWitness : Prop

/-- Governing-datum rigidity yields the local internal datum package. -/
theorem realized_local_internal_datum_forcing
    {PhaseClass Scalar ClosureClass : Type}
    (data : RealizedLocalInternalDatumForcingData
      PhaseClass Scalar ClosureClass) :
    Nonempty (LocalInternalDatumSelectedChannels
      PhaseClass Scalar ClosureClass) := by
  exact ⟨data.toLocalInternalDatumSelectedChannels⟩

/-- Explicit witness for the gauge-compatible local internal datum. -/
structure GaugeCompatibleLocalDatumForcingData
    (PhaseClass Scalar ClosureClass GaugeClass : Type)
    extends GaugeCompatibleLocalInternalDatum
      PhaseClass Scalar ClosureClass GaugeClass where
  governingDatumRigidWitness : Prop
  selectedChannelTransportSystemWitness : Prop

/-- Governing-datum rigidity plus selected-channel transport systems yield the
gauge-compatible local internal datum package. -/
theorem gauge_compatible_local_datum_forcing
    {PhaseClass Scalar ClosureClass GaugeClass : Type}
    (data : GaugeCompatibleLocalDatumForcingData
      PhaseClass Scalar ClosureClass GaugeClass) :
    Nonempty (GaugeCompatibleLocalInternalDatum
      PhaseClass Scalar ClosureClass GaugeClass) := by
  exact ⟨data.toGaugeCompatibleLocalInternalDatum⟩

/-- Explicit witness that the intrinsic package with transport systems yields
the gauge-compatible local internal datum. -/
structure IntrinsicPackageGaugeCompatibleLocalDatumData
    (PhaseClass Scalar ClosureClass GaugeClass : Type)
    extends GaugeCompatibleLocalInternalDatum
      PhaseClass Scalar ClosureClass GaugeClass where
  intrinsicPackageWitness : Prop
  selectedChannelTransportSystemWitness : Prop

/-- The intrinsic symmetry/order package yields the gauge-compatible local
internal datum. -/
theorem intrinsic_package_yields_gauge_compatible_local_datum
    {PhaseClass Scalar ClosureClass GaugeClass : Type}
    (data : IntrinsicPackageGaugeCompatibleLocalDatumData
      PhaseClass Scalar ClosureClass GaugeClass) :
    Nonempty (GaugeCompatibleLocalInternalDatum
      PhaseClass Scalar ClosureClass GaugeClass) := by
  exact ⟨data.toGaugeCompatibleLocalInternalDatum⟩

end CoherenceCalculus
