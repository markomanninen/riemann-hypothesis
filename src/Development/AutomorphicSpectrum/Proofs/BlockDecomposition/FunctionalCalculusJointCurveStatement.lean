module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusJointCurve
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functional_calculus_joint_curve : PositivityTheory.RgBcC.Fc.CurveJoint := by
  first | exact @GlobalTheory.CompanionTheory.CurveJ.curveJoint | exact GlobalTheory.CompanionTheory.CurveJ.curveJoint | (intros; apply GlobalTheory.CompanionTheory.CurveJ.curveJoint <;> assumption)
