module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRowLevelWithAnalyticFactsOfSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGVanish
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP

@[expose] public section

open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsRowLevelWithAnalyticFacts_of_steps : TieOfCtx → StepChoiceConstantsC → StepAnalyticP → StepAnalyticConstantsP := by
  first | exact @GlobalTheory.NGRow.exists_row_level_analytic | exact GlobalTheory.NGRow.exists_row_level_analytic | (intros; apply GlobalTheory.NGRow.exists_row_level_analytic <;> assumption)
