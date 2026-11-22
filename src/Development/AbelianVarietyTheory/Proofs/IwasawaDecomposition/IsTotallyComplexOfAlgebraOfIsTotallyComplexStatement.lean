module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTotallyComplexOfAlgebraOfIsTotallyComplex
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTotallyComplex_of_algebra_of_isTotallyComplex : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [_root_.NumberField.IsTotallyComplex E], IsTotallyComplex K := by
  first | exact @GlobalTheory.isTotallyComplex_of_algebra | exact GlobalTheory.isTotallyComplex_of_algebra | (intros; apply GlobalTheory.isTotallyComplex_of_algebra <;> assumption)
