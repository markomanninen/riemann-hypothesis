module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ThetaUnifAVOfLaws
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditionalStatement

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.thetaUnifAV_all : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ThetaUnifAV := by
  obtain ⟨h, -⟩ := _root_.GlobalTheory.abelianSchemeLaws_all
  exact _root_.GlobalTheory.thetaUnifAV_of_laws h.cube h.mulN h.weil h.weilNondeg h.globalSectionsRank

end GlobalTheory
