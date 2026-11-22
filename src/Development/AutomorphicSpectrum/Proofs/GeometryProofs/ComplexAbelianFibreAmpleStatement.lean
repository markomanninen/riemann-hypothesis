module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexAbelianFibreAmple
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExpChartCoordinatesStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaMultiplierNormalFormStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsThetaBasisOfFactorStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionsFiniteDimStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentSpaceEquivHolUnifStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifCompareIsogenyStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelComplexBaseChange
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PFibreMahlerForms

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_abelian_fibre_ample : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ), ∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' D.t (emb σ)), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.FibrePol.exists_fibre_pol | exact GlobalTheory.CompanionTheory.Ar.Sl.FibrePol.exists_fibre_pol | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.FibrePol.exists_fibre_pol <;> assumption)
