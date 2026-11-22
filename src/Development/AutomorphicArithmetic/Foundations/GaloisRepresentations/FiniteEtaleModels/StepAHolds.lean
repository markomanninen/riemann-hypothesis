module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BaseOnto
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.StepAOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.CoreAOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ADictP
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ASysExt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ATrEtaK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ATrKer
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.AGalOfKer
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ATrPull
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ATrSame
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ALevTr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ALevRe
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ABetaH
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ABetaLat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ANumSplit

@[expose] public section

open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.FiniteEtaleModels

theorem stepA_holds (h₁ : MultUnit) (h₂ : LatGen) (h₃ : ClsEx) (h₄ : TrEta) (h₅ : TrBack) (h₆ : QComp) : StepA :=
  stepA_of (dictP_holds h₁) sysExt_holds trEtaK_holds trKer_holds galOfKer_holds betaH_holds (betaLat_holds h₂) numSplit_holds
    (coreA_of trPull trSame_holds levTr_holds levRe_holds h₃) h₄ h₅ h₆

end UpperTheory.Gal.FiniteEtaleModels
