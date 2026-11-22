module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.CovMain
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.QuotObjLink
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelNonemptyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfCompactB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibreStatement
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PFinModel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PFinCover
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PRepAll
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PRepMul
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PPtAll
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PGrpFin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PCrtMul
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PCrtProj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PIdealInd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PPlaceOf

@[expose] public section

namespace UpperTheory.Gal.Int.Geo.CovMain

open UpperTheory.Gal.FiniteEtaleModels in
theorem mIn : MIn :=
  { ex := @GlobalTheory.T.harrisTaylorIntegralModel_nonempty,
    proj := @GlobalTheory.UPel.HT.Model.isProjOver_of_compactB,
    cmp := @GlobalTheory.T.exists_open_closed_immersion_genModel_to_fibre,
    finModel := finModel_holds (finCover_holds
      (repAll_holds idealInd_holds (repMul_holds crtMul_holds crtProj_holds))
      (ptAll_holds idealInd_holds crtMul_holds) grpFin_holds),
    placeOf := placeOf_holds,
    cong := crystallineComparison.Mod.congKS_link,
    corr := crystallineComparison.Mod.corrBC_holds crystallineComparison.Mod.quotObj_link }

theorem ksCong_holds : KSCong := kSCong_of mIn
theorem stdEx_holds : StdEx := stdEx_of mIn
theorem ksCover_holds : KSCover := kSCover_of mIn

end UpperTheory.Gal.Int.Geo.CovMain
