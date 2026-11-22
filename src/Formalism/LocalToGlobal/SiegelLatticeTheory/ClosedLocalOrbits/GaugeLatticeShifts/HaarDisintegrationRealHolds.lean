module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductFormulaHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SecMeasLocHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepRealHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HaarDisintegrationOfLocal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalJacobianOfDoubleCoset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NHLocHolds

@[expose] public section

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

theorem haar_disintegration_real_holds : HaarDisintegrationReal := by
  have hR : JacobianCoordinates.JL.RightInvS :=
    JacobianCoordinates.JL.rightInvS_of JacobianCoordinates.JL.setCorr_holds (JacobianCoordinates.JL.haarCorr_of JacobianCoordinates.JL.setCorr_holds)
  have hU : JacobianCoordinates.UnimodLoc := hR
  exact UnitaryIsometries.haar_disintegration_of_local ProductExactness.product_formula_holds JacobianCoordinates.JL.jacLoc_holds ProductExactness.SecMeasLoc_holds hU
    NilradicalHermitianFrames.NH.NHLoc_holds ProductExactness.StepReal_holds

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
