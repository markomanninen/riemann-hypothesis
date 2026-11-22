module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareRatioValuationWithoutNormFormula
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_ratio_valuation_without_norm_formula : (∀ D, GlobalTheory.NormSum.Inp D) → LNe → TorEx → BotSmall → BotExT → NormBig → BotNe → TriEx → Tower → BotConst → Refl → RhoLow → OneSqSt := by
  first | exact @GlobalTheory.SqTop.OneSqNoSmall.oneSqSt_of_claims' | exact GlobalTheory.SqTop.OneSqNoSmall.oneSqSt_of_claims' | (intros; apply GlobalTheory.SqTop.OneSqNoSmall.oneSqSt_of_claims' <;> assumption)
