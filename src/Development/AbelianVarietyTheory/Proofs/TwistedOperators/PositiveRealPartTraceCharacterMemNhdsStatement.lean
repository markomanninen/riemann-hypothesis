module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PositiveRealPartTraceCharacterMemNhds
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionMixedCoordinateBumpMulCoreStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTargetBumpMulCoreThetaExistsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionDeterminedByMixedCoordinatesStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positiveRealPart_traceCharacter_mem_nhds : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (n ρ : ℕ) (L : Mx D ρ n) (x : Mx D n ρ), {z : Mx D n ρ | 0 < (star (psiE ψ (upSum (L ⬝ (z - x))))).re} ∈ nhds x := by
  first | exact @GlobalTheory.PosNhdsChar.posNhds | exact GlobalTheory.PosNhdsChar.posNhds | (intros; apply GlobalTheory.PosNhdsChar.posNhds <;> assumption)
