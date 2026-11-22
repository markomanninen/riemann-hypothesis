module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPlaceValuationResidueFieldCardEqZeroOfNotMe
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
theorem _root_.GlobalTheory.T.coeffPlace_valuation_residueFieldCard_eq_zero_of_not_mem : ∀ {D : D7} (P : Pl D.host.E) (w : PlL D), ((Formalism.EigenvalueLevelCeiling.plc P : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal →
    vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) = 0 := by
  first | exact @GlobalTheory.UnfoldLoss.ResCardAway.vw_resCard_eq_zero | exact GlobalTheory.UnfoldLoss.ResCardAway.vw_resCard_eq_zero | (intros; apply GlobalTheory.UnfoldLoss.ResCardAway.vw_resCard_eq_zero <;> assumption)
