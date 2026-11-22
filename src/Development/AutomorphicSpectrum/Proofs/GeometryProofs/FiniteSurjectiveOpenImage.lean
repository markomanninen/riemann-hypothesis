module

public import Mathlib
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FiniteSurjectiveImageOpen
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.Strat

theorem preimage_le_of_finite_surjective : ∀ (Z Z' : Scheme.{0}) [IsIntegral Z] [IsIntegral Z'] (π : Z' ⟶ Z), IsFinite π → Surjective π → ∀ V : Z'.Opens, (V : Set Z').Nonempty → ∃ U : Z.Opens, (U : Set Z).Nonempty ∧ π ⁻¹ᵁ U ≤ V :=
  PositivityTheory.Xgn.finite_surjective_image_open

end GlobalTheory.CompanionTheory.Ar.Strat
