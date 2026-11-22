module

public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohCmp
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohField
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohMu
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTate
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohFin

@[expose] public section

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace CompanionTheory.LocalTateOrthogonality.Gcoh

theorem top_tate : Formalism.GaloisCohomology.LocalTateDualityK := tate_of gcRep gc0 gc1 gc2 gcField gcMu

theorem top_locfin : Formalism.GaloisCohomology.LocalFinitenessK := locfin_of gcField

end CompanionTheory.LocalTateOrthogonality.Gcoh
