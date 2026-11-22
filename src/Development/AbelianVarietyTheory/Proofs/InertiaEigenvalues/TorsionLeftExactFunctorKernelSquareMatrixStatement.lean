module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionLeftExactFunctorKernelSquareMatrix
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_left_exact_functor_kernel_square_matrix : KernelRep := by
  first | exact @GlobalTheory.KRep.kernelRep | exact GlobalTheory.KRep.kernelRep | (intros; apply GlobalTheory.KRep.kernelRep <;> assumption)
