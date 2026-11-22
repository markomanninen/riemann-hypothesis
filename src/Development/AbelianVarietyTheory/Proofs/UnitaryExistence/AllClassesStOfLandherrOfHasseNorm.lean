module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AllClassesOccur
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientPrincipalTripleStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm

@[expose] public section

theorem GlobalTheory.allClassesSt_of_landherr_of_hasseNorm :
    GlobalTheory.Published.LandherrSt → GlobalTheory.Published.HasseNormSt → GlobalTheory.AllClassesSt :=
  fun hL hN => GlobalTheory.all_classes_occur hL hN GlobalTheory.abelianSchemeLaws_all.1 (GlobalTheory.T.exists_heckeQuotient_principal_triple GlobalTheory.abelianSchemeLaws_all.1)

theorem GlobalTheory.allClassesSt_of_hasseNorm : GlobalTheory.Published.HasseNormSt → GlobalTheory.AllClassesSt :=
  fun hN => GlobalTheory.allClassesSt_of_landherr_of_hasseNorm
    (GlobalTheory.Published.landherrSt_of_landherr (GlobalTheory.LocalQuad.landherr_of_hasseNormSt hN)) hN
