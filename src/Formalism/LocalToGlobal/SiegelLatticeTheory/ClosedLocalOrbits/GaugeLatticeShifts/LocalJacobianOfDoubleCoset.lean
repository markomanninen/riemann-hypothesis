module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BigCellMulVecWb
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ExistsPowMulPredGe
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HpkExHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HpkMulVecEs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SecWbHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IsClosedSLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SigmaFiniteOfB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProdIccRange
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MulVecMapMem

@[expose] public section

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

theorem transEx_holds (hHC : HaarCorr) (hW : CoordW) : TransEx := fun hH _ =>
  jacExGood_of_N (jacExGoodN_of_hpkEx_of_pFrame_of_haarCorr hH pFrame_holds hHC zBig bigMem_holds hW secWb_holds)

theorem local_jacobian_of_double_coset (h1 : DiagDCLoc) (hR : RightInvS) (hHC : HaarCorr) (hW : CoordW) : JacLoc :=
  jacLoc_of_ex h1 hR (degRed_holds hR (transEx_holds hHC hW hpkEx_holds hR))

theorem jacLoc_of_rightInv_haarCorr (hR : RightInvS) (hHC : HaarCorr) (hW : CoordW) : JacLoc :=
  local_jacobian_of_double_coset Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.DiagDCLoc_holds hR hHC hW

theorem jacLoc_of_rightInv_setCorr (hR : RightInvS) (hSC : SetCorr) (hW : CoordW) : JacLoc :=
  jacLoc_of_rightInv_haarCorr hR (haarCorr_of hSC) hW

theorem jacLoc_of_setCorr' (hSC : SetCorr) (hW : CoordW) : JacLoc :=
  jacLoc_of_rightInv_setCorr (rightInvS_of hSC (haarCorr_of hSC)) hSC hW

theorem jacLoc_of_setCorr (hSC : SetCorr) : JacLoc :=
  jacLoc_of_setCorr' hSC coordW_holds

theorem jacLoc_holds : JacLoc :=
  jacLoc_of_setCorr setCorr_holds

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates
