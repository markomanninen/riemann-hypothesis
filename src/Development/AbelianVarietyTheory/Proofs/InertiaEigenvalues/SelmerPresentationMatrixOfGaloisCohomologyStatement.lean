module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerPresentationMatrixOfGaloisCohomology
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selmerPresentationMatrix_of_galois_cohomology : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), ThmS bkP := by
  first | exact @GlobalTheory.SelFun.oneMatrix_of_galoisCohomology | exact GlobalTheory.SelFun.oneMatrix_of_galoisCohomology | (intros; apply GlobalTheory.SelFun.oneMatrix_of_galoisCohomology <;> assumption)
