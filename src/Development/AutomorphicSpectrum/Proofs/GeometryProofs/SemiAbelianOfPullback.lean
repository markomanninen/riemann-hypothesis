module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsVBOneOfChartGenerators
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentSectionAdditiveStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualMapSnd
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar

theorem isSemiAbelian_of_isGrpPullback : ∀ (X X' : Scheme.{0}) (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G']
    [IsCommMonObj G'] (f : X' ⟶ X) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → IsSemiAbelian G →
    IsSemiAbelian G' := by
  intro X X' G _ G' _ _ f φ h hG
  obtain ⟨e, he, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  exact GlobalTheory.isSemiAbelian_of_grpIso e (IsSemiAbelian.pullback f G hG)

end GlobalTheory.CompanionTheory.Ar
