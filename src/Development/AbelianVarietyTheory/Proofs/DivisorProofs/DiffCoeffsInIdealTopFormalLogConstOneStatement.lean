module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffCoeffsInIdealTopFormalLogConstOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHasPAdicPowerSeriesValueOfDiffCoeffsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueAddSmulMapStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueMapOfContinuousEvaluatioStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicEvaluationSubstCompatibleThickeningStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueSubMemPdIdealStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNaturaStatement

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diffCoeffsInIdeal_top_formalLog_constOne : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q] (σ : Type) (g : MvPowerSeries σ B), constantCoeff g = 1 → DIn (⊤ : Ideal B) (formalLog (map (algebraMap B Q) g)) := by
  first | exact @GlobalTheory.QLog.dIn_top_formalLog_map | exact GlobalTheory.QLog.dIn_top_formalLog_map | (intros; apply GlobalTheory.QLog.dIn_top_formalLog_map <;> assumption)
