module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericFamilyStepOfSiegelWeil
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqFam
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude

@[expose] public section

open GlobalTheory.SnFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFamilyStep_of_siegelWeil : PI.VolStabS.MassDataS.SWXS → Formalism.L2.SG.Pf.MainEqFam.StepFamG := by
  first | exact @GlobalTheory.SnFamTop.stepFamG_of_SWXS | exact GlobalTheory.SnFamTop.stepFamG_of_SWXS | (intros; apply GlobalTheory.SnFamTop.stepFamG_of_SWXS <;> assumption)
