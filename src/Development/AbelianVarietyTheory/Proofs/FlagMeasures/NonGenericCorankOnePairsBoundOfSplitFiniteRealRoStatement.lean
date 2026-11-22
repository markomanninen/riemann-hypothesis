module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericCorankOnePairsBoundOfSplitFiniteRealRo
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGVanish
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP

@[expose] public section

open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonGenericCorankOnePairsBound_of_splitFiniteRealRow : NGCut2P → RowNGP := by
  first | exact @GlobalTheory.NGRow.rowNG_of_cut2P | exact GlobalTheory.NGRow.rowNG_of_cut2P | (intros; apply GlobalTheory.NGRow.rowNG_of_cut2P <;> assumption)
