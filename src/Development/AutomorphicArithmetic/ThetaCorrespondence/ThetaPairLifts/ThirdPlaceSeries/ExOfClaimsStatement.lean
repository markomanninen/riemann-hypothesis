module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulVecEqOfBasis
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExOfClaims

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsFunctionIn_of_sqRatio_range : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → GlobalTheory.RowClaim.SumOKK → GlobalTheory.RowClaim.SumRatK → GlobalTheory.RowClaim.ConstK → (_root_.GlobalTheory.BigTop.Fun.CharacterAtPoint fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ i j t, GlobalTheory.RowTest.sqRatio ch i j t ∈ Set.range D.what₂.embLL) → GlobalTheory.NormSum.IntSt → FieldDat → TorEx → DenEx → BotEx → BotSmall → _root_.GlobalTheory.BigTop.Fun.ExistsFunctionIn @Fld @Comparison₂ := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.ex_of_claims_alt | exact _root_.GlobalTheory.BigTop.Fun.ex_of_claims_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.ex_of_claims_alt <;> assumption)
end
