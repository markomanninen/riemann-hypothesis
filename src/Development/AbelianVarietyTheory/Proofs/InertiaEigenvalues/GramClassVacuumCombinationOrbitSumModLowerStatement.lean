module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GramClassVacuumCombinationOrbitSumModLower
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramClass_vacuumCombination_orbitSum_mod_lower : ∀ (D : D7) (M : MtFam D), AVTied D M → ∀ i : D.nd.Loc, ClassSum (M.loc i) → TypeOrth D i := by
  first | exact @GlobalTheory.TypeOrthClassSum.typeOrth_of_classSum | exact GlobalTheory.TypeOrthClassSum.typeOrth_of_classSum | (intros; apply GlobalTheory.TypeOrthClassSum.typeOrth_of_classSum <;> assumption)
