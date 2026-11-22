module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthonormalFrameFinitePartMemCompletedLattice
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
theorem _root_.GlobalTheory.T.orthonormalFrame_finitePart_mem_completedLattice : ∀ {D : D7} (S T : HSp D) (B : GL (Fin S.rank) D.host.E) (B' : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1 → ∀ M : Matrix (Fin T.rank) (Fin S.rank) D.host.E, (∀ i j, M i j ∈ D.host.AA) → GlobalTheory.VacUnique.finRat S T (-(B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1)) ∈ latO S T (colLat B : Set (Fin S.rank → D.host.E)) (colLat B' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  first | exact @GlobalTheory.FrameLat.frame_finRat_mem_latO | exact GlobalTheory.FrameLat.frame_finRat_mem_latO | (intros; apply GlobalTheory.FrameLat.frame_finRat_mem_latO <;> assumption)
