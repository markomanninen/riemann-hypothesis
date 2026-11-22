module

public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.NormVanishOfParts
public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.RemovableFinset
public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.EsymmZero
public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.LineFinite
public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.SymmGrowth
public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.SymmVanish
public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.SymmDiff
public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.Section

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Norm

universe u

theorem normVanish_of_holoSection (hsec : holoSectionStatement.{u}) : normVanishStatement.{u} :=
  normVanish_of_parts lineVanish esymmZero (symmDiff_of_holoSection hsec) symmVanish symmGrowth
    lineFinite

theorem normVanish : normVanishStatement.{u} := normVanish_of_holoSection holoSection

end ReciprocityTheory.L2DbarEstimates.Norm
