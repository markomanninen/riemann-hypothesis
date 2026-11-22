module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaValuesAtNegIntUnique
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds

@[expose] public section

open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialZeta_values_at_neg_int_unique : ∀ {E : Type} [Field E] [NumberField E] {k : ℕ}, 2 ≤ k → ∀ {z z' : ClassGroup (GlobalTheory.CMVal.OF E) → ℚ}, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZetaVals k z → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZetaVals k z' → z = z' := by
  first | exact @GlobalTheory.ZetaValUnique.classZetaVals_unique | exact GlobalTheory.ZetaValUnique.classZetaVals_unique | (intros; apply GlobalTheory.ZetaValUnique.classZetaVals_unique <;> assumption)
