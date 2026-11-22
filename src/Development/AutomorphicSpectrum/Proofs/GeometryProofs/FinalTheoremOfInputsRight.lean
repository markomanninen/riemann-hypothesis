module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyPosOfHodgeTateInputsStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmpHodgeTiedHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComparisonOfInputsAvoidanceStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmpPairOfInputsStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerVolumeTheoremStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinalTheoremOfInputsLeftStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilSt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrdinaryCurveStatementHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PtEqOneOfGZero

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem goodTower_volume_of_reduced : (PartI ∧ N1ab ∧ N1c ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ToroidalLevelCompatibility (D := D) ∧ ToroidalHeckeCompatibility (D := D)) → KeyFormula → GlobalTheory.Published.SemiAbelianHomExtension → GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → HT.FarguesHodgeTate → Flat.GagaSections → GroundTheory.Heights₂.Heights.LineOfLargeDegree.Statement → PB.Inputs → Prov.HS → Prov.An → Prov.ZhangDimensionPushDownGrassmannianHeightBounds → ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.AvoidStatement → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → ThetaUnifAV → Top.GoodTowerExistsX ∧ Top.VolumeTheoremX := by
  intro hM hKF hSA hNS hResK hFHT hGaga hLLD hPB hHS hAn hNine hPts hAvoid hQ hZ hTheta
  have hGiven : Top.Given :=
    ⟨hM, hKF, hSA, hNS, hResK, GlobalTheory.T.semi_abelian_statement_holds, hFHT, hGaga,
      (GlobalTheory.T.slope_bound_of_line_large_degree hLLD).1, hPB, hHS, hAn, hNine,
      GlobalTheory.T.antisymmetric_perturbation_holds⟩
  have hW : Out.WeilSt := GlobalTheory.CompanionTheory.Ar.Link.weilSt
  have hHTD : GR.HodgeTateDatumStatement := GlobalTheory.CompanionTheory.Ar.GR.Top.main
  have hOrd : GR.OrdinaryCurveStatement := GlobalTheory.T.ordinary_curve_statement_holds
  have hFam : Num.FamilyExistsPos := GlobalTheory.T.family_pos_of_hodge_tate_inputs hFHT hQ hZ hHTD hOrd
  have hCmpSt : Cmp.CmpSt := GlobalTheory.T.comparison_of_inputs_avoidance hPB hAvoid hResK
  have hTied : HodgeComparisonCompatibility := GlobalTheory.T.CmpHodgeTied_holds
  have hPair : Cmp.CmpPair := GlobalTheory.T.cmpPair_of_inputs hPB hCmpSt hTied hTheta
  exact GlobalTheory.T.good_tower_volume_theorem hGiven hPts hAvoid hW hFam hPair

end GlobalTheory.CompanionTheory.Ar.Top
