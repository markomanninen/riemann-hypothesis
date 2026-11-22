module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisationPointEigenSystemMem
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localisationPointEigenSystem_mem : ∀ (D : D7) (M : MtFam D), AVTied D M → ∀ (i : D.nd.Loc) (x : D.nd.X i), ptSys D i x ∈ EigSet (M.loc i) (D.nd.l i) (D.nd.Q i) := by
  first | exact @GlobalTheory.PointEigen.ptSys_mem_eigSet | exact GlobalTheory.PointEigen.ptSys_mem_eigSet | (intros; apply GlobalTheory.PointEigen.ptSys_mem_eigSet <;> assumption)
