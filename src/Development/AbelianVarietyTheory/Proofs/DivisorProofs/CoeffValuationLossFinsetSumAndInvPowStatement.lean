module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffValuationLossFinsetSumAndInvPow
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralUnfoldingVariablesMemFieldRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemVarLat

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffValuationLoss_finsetSum_and_invPow : ∀ {D : D7} (w : PlL D),
    (∀ {ι : Type} (s : Finset ι) (z : ι → ℂ) (a : ℝ), (∀ i ∈ s, LossLe w (z i) a) → LossLe w (∑ i ∈ s, z i) a) ∧
    ∀ q M : ℕ, 0 < q → LossLe w ((((q : ℝ)⁻¹ ^ M : ℝ)) : ℂ) ((M : ℝ) * (vw w ((q : ℕ) : D.what₂.LL) : ℝ)) := by
  first | exact @GlobalTheory.LossSum.lossLe_sum_and_pow | exact GlobalTheory.LossSum.lossLe_sum_and_pow | (intros; apply GlobalTheory.LossSum.lossLe_sum_and_pow <;> assumption)
