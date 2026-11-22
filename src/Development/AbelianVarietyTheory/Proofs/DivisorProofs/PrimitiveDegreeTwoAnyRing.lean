module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegreeTwoExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveClassDegreeTwoStructureSheafVanishStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianStructureCohomologyStatementStatement

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem primE2_any_ring : PrimitiveExtendedDegTwoVanish := by
  apply GlobalTheory.T.primitive_degree_two_extension
  apply GlobalTheory.T.additiveClassDegreeTwo_structureSheaf_vanish
  intro R _ A _ g hA hs
  exact ⟨(GlobalTheory.T.abelian_structure_cohomology_statement R A g hA hs).1,
    (GlobalTheory.T.abelian_structure_cohomology_statement R A g hA hs).2.1⟩

end GlobalTheory.Obs
