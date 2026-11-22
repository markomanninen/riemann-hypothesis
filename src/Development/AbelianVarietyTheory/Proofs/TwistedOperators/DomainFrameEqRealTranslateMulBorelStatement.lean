module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DomainFrameEqRealTranslateMulBorel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelThetaSpan
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsVacuaAndMultipliers
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAdelicMatrix
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilPairLevelTrivialMapsLevelVectorStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelDatumVectorEqThetaOfTestFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTrivialAtLevelUnitaryTransportSelfDualStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevelStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeriesStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLawsStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompAtOfFin
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariantStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.domain_frame_eq_real_translate_mul_borel : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ x ∈ C.X.dom, ∃ a ∈ GinfC T, ∃ b ∈ Bor C.X.Ψ T.rank, x = rmul (C.xB (C.mvB a B)) b := by
  first | exact @GlobalTheory.FrameDecomp.frame_decomp | exact GlobalTheory.FrameDecomp.frame_decomp | (intros; apply GlobalTheory.FrameDecomp.frame_decomp <;> assumption)
