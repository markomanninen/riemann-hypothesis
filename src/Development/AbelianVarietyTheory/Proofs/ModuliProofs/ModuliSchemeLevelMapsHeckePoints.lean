module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevelStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianSchemeStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHeckeQuotientPointModuli
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapsClosed
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHoldStatement

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.moduliScheme_levelMaps_heckePoints : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.N1 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.N1
  exact ⟨_root_.GlobalTheory.Moduli.moduli_scheme_exists, fun E _ _ _ H D hD =>
    ⟨_root_.GlobalTheory.levelMaps_closed _root_.GlobalTheory.abelianSchemeLaws_all.1 E H D hD,
      _root_.GlobalTheory.heckePoints_of_laws _root_.GlobalTheory.abelianSchemeLaws_all.1
        _root_.GlobalTheory.AbLaw.CubeAssembly.cube_gen E H D hD⟩⟩

end GlobalTheory
