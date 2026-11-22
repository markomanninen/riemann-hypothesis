module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCColumnLatticeOfOrthonormalFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrPt
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTraceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFacts

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSelfDualC_columnLattice_of_orthonormalFrame : ∀ {D : D7} (S : HSp D) (B : GL (Fin S.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1 → IsSelfDualC S (colLat B) := by
  first | exact @GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal | exact GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal | (intros; apply GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal <;> assumption)
