module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLAdicRationalCohomologyGaloisCoverInvariStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonSecOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdPropertiesStatement
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.VFinHolds
public import Development.EtaleCohomology.WeilConjectures.AbsContPf
public import Development.EtaleCohomology.WeilConjectures.ChevPf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JSplitDesc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JCharVan
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JCorrUniq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JVBcS
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtsOfSplits
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFEtBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtTr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtnGood
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtGood
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalInv

@[expose] public section

namespace UpperTheory.Gal.G3

theorem etnGood' : EtnGood := pEtnGood (pFEtBasic pPtsOfSplits) pEtTr

theorem corrUniq_holds : CorrUniq := jCorrUniq (pEtGood etnGood') jSplitDesc jCharVan

theorem vBcS_holds : VBcS := jVBcS

theorem vInv_holds : GlobalTheory.GalV.VInv := fun l _ _ _ f _ _ _ G _ a ha hiso n i => GlobalTheory.T.pullbackLAdicRationalCohomology_galoisCover_invariants l f G a ha hiso n i

end UpperTheory.Gal.G3
