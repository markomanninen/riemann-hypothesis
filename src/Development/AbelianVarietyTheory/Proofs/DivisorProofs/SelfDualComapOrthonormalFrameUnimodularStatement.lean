module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualComapOrthonormalFrameUnimodular
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalUnitaryMoveSelfDualToSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCColumnLatticeOfOrthonormalFrame
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_comap_orthonormalFrame_unimodular : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 → IsSelfDualC V Λ →
    (Formalism.L2.Pj.GenLat.mk (Λ.comap ((Matrix.mulVecLin fr.1).restrictScalars (𝓞 D.host.E)))).Unimod := by
  first | exact @GlobalTheory.FramePull.unimod_comap_frame | exact GlobalTheory.FramePull.unimod_comap_frame | (intros; apply GlobalTheory.FramePull.unimod_comap_frame <;> assumption)
