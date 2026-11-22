module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CorankOneNonGenericRowBoundClosed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGVanish
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP

@[expose] public section

open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.corankOneNonGenericRowBound_closed : PI.VolStabS.MassDataS.SWXS → StepChoiceConstantsC → StepPinExists → Formalism.L2.SG.NGVanish.FormNGC → StepThmBPinnedP → RowNGP := by
  first | exact @GlobalTheory.NGRowClose.close | exact GlobalTheory.NGRowClose.close | (intros; apply GlobalTheory.NGRowClose.close <;> assumption)
