module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LevClauses
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniquePoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemePointObject
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ModuliNonemptyOfObj
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPrincipalDim
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TorsionFieldOfDefinition

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem torsion_defined_over_numberField : ∀ (L : Type) [Field L] [NumberField L] (σ : L →+* ℂ) (P : Out.PolAV (Sp L)) (n : ℕ), 0 < n → ∃ (F : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ F) (e : L →+* F), (∀ x, ((e x : F) : ℂ) = σ x) ∧ ∀ x : Over.mk (spMap σ) ⟶ P.A, x ^ n = 1 → ∃ y : Sp F ⟶ P.A.left, y ≫ P.A.hom = spMap e ∧ spMap (algebraMap F ℂ) ≫ y = x.left :=
  @PositivityTheory.Xgn.torsion_field_of_definition

end GlobalTheory.CompanionTheory.Ar
