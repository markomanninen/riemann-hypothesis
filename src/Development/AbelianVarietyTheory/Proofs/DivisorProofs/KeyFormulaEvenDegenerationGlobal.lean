module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaEvenDegenerationGlobalOfLocalUnitsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaUnitOverNormalBaseOfFamilyUnitOfTraitsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUnitTraitsOfUniformisedTraitsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUnitUniformisedOfAbsValueOneStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUniformisedFourierFrameAbsOneStatement

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEvenClosing

theorem keyGlob : KeyGlob := by
  obtain ⟨κ, hH, hF, -, hT, -, hU, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  have h4 : MBLow.Rule4 κ := ⟨hH, hF, hT, hU⟩
  exact GlobalTheory.T.key_formula_even_degeneration_global_of_local_units κ hH hF (GlobalTheory.T.keyFormulaUnitOverNormalBase_of_familyUnit_of_traits κ hU (GlobalTheory.T.keyValue_unit_traits_of_uniformised_traits κ (GlobalTheory.T.keyValue_unit_uniformised_of_absValueOne κ (GlobalTheory.T.key_value_uniformised_fourier_frame_abs_one κ h4))))

end GlobalTheory.KeyEvenClosing
