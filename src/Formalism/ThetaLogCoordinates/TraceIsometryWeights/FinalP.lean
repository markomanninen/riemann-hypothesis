module

public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.InvInv
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.InvInt
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.HomRelationHolds
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.SchurTraceOfHomInv
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.TypeInt
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.LatticeBasisPolynomial
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.OrthogonalIsomorphismHolds
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.CommProjectionHolds
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.PolLeISupIsoW
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.Discharge

@[expose] public section

namespace Formalism.InvariantFactorPaths.PW.Top

theorem invInv : InvInv := invariant_inverse_holds
theorem invNat : InvNat := invariant_natural_holds
theorem homInv : HomInv := homInv_of invInv
theorem schurTrace : SchurTrace := schurTrace_of invInv
theorem typeInt : TypeInt := typeInt_of invNat homInv schurTrace
theorem divInt : DivInt := divided_integral_holds
theorem latBasisPol : LatBasisPol := lattice_basis_polynomial
theorem projP : ProjP := projection_lattice_holds
theorem commP : CommP := comm_projection_holds
theorem intP : IntP := intP_of typeInt latBasisPol
theorem dischargeP : DischargeP := dischargeP_of projP commP intP

end Formalism.InvariantFactorPaths.PW.Top
