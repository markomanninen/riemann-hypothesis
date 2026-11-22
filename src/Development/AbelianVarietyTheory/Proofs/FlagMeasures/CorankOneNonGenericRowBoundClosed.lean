module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGVanish
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CorankOnePairsNonGenericRowBoundOfRemainingPremiStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NongenericRowStatementsOfFamilyStatementsStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyRowWeightSumUnfoldingIdentityProofStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGenericMassPositiveBoundedProofStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGroupSumFactorsRowWeightAmplitudeProofStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyLocalObjectsExistAtTermsProofStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericCorankOneTermsFamilyCutByDefectStatement

@[expose] public section

open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow

namespace GlobalTheory.NGRowClose

theorem rowNGP_of_formNGVanish (hSW : PI.VolStabS.MassDataS.SWXS) (hC : StepChoiceConstantsC)
    (hP : StepPinExists) (hF : Formalism.L2.SG.NGVanish.FormNGC) (hB : StepThmBPinnedP) :
    RowNGP := by
  obtain ⟨h5, hw, h4, he⟩ := GlobalTheory.T.nongeneric_row_statements_of_family_statements GlobalTheory.T.non_generic_corank_one_terms_family_cut_by_defect
  exact GlobalTheory.T.corankOnePairsNonGenericRowBound_of_remaining_premises hC hP hF hB (h5 GlobalTheory.T.familyRowWeightSumUnfoldingIdentity) (hw (GlobalTheory.T.familyGenericMassPositiveBounded_proof hSW))
    (h4 GlobalTheory.T.familyGroupSumFactorsRowWeightAmplitude_proof) (he GlobalTheory.T.familyLocalObjectsExistAtTerms_proof)

theorem close : PI.VolStabS.MassDataS.SWXS → StepChoiceConstantsC → StepPinExists →
    Formalism.L2.SG.NGVanish.FormNGC → StepThmBPinnedP → RowNGP :=
  fun hSW hC hP hF hB => rowNGP_of_formNGVanish hSW hC hP hF hB

end GlobalTheory.NGRowClose
