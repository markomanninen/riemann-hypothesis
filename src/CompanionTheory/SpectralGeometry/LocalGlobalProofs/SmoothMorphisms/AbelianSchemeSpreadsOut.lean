module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.ExistsFgSmoothOfRelativeDimension
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.AbelianSchemeModelBaseChangeSubalgebra
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.AbelianSchemeSpreadsOutFiniteTypeSubringImports

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem isCommMonObj_of_iso {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] {M N : C}
    [MonObj M] [MonObj N] [IsCommMonObj N] (e : M ≅ N) [IsMonHom e.hom] : IsCommMonObj M where
  mul_comm := by
    rw [← cancel_mono e.hom, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm N]

theorem isAbelianScheme_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G]
    [GrpObj (Over.mk (pullback.snd G.hom f))] (φ : pullback G.hom f ⟶ G.left)
    (h : IsGrpPullback (Over.mk (pullback.snd G.hom f)) G f φ) (hG : IsAbelianScheme G) :
    IsAbelianScheme (Over.mk (pullback.snd G.hom f)) := by
  obtain ⟨e, he, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  have := hG.comm
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  refine ⟨isCommMonObj_of_iso e, ?_, ?_, ?_⟩
  · show Smooth (pullback.snd G.hom f); infer_instance
  · show IsProper (pullback.snd G.hom f); infer_instance
  · show GeometricallyConnected (pullback.snd G.hom f); infer_instance

end GlobalTheory.CompanionTheory.Ar.Approx
