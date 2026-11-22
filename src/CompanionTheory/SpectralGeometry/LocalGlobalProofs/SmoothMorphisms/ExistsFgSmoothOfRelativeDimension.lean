module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

def dimLocus {X S : Scheme.{0}} (p : X ⟶ S) (g : ℕ) : X.Opens :=
  ⨆ U : {U : X.Opens // SmoothOfRelativeDimension g (U.ι ≫ p)}, U.1

theorem smoothOfRelativeDimension_snd {X S T : Scheme.{0}} (p : X ⟶ S) (b : T ⟶ S) (g : ℕ)
    (h : pullback.fst p b ⁻¹ᵁ dimLocus p g = ⊤) : SmoothOfRelativeDimension g (pullback.snd p b) := by
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g)
    (fun U : {U : X.Opens // SmoothOfRelativeDimension g (U.ι ≫ p)} => pullback.fst p b ⁻¹ᵁ U.1)
    (top_le_iff.1 fun y _ => ?_) fun U => ?_
  · have hy : pullback.fst p b y ∈ dimLocus p g := h.ge (Set.mem_univ y)
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨U, hU⟩
  · exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      ((isPullback_morphismRestrict _ U.1).paste_vert (IsPullback.of_hasPullback _ _)) U.2

theorem preimage_dimLocus_eq_top {X S T : Scheme.{0}} (p : X ⟶ S) [Smooth p] (b : T ⟶ S) (g : ℕ)
    (h : SmoothOfRelativeDimension g (pullback.snd p b)) :
    pullback.fst p b ⁻¹ᵁ dimLocus p g = ⊤ := by
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨n, W, hW, d⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim p (pullback.fst p b y)
  obtain rfl : n = g := ReciprocityTheory.ChartRestriction.G.H1.dim_base (IsPullback.of_hasPullback p b) d h y hW
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, d⟩, hW⟩


open GlobalTheory.Spread in
theorem exists_fg_smoothOfRelativeDimension : ∀ (k V : Type) [CommRing k] [IsNoetherianRing k]
    [CommRing V] [Algebra k V] (X : Scheme.{0}) (p : X ⟶ Sp k) (g : ℕ), Smooth p → QuasiCompact p →
    SmoothOfRelativeDimension g (pullback.snd p (spMap (algebraMap k V))) →
    ∃ R : Subalgebra k V, R.FG ∧ SmoothOfRelativeDimension g (pullback.snd p (spMap (algebraMap k R))) := by
  intro k V _ _ _ _ X p g hs hq h
  classical
  have : QuasiCompact p := hq
  let s : (Finset V)ᵒᵖ := .op ∅
  let π : (GlobalTheory.Spread.bcDiagram p V).obj s ⟶ X := pullback.fst p _
  have hπ : (GlobalTheory.Spread.bcCone p V).π.app s ≫ π = pullback.fst p _ :=
    GlobalTheory.Spread.bcMap_fst _ _
  obtain ⟨j, f, hj⟩ := exists_map_eq_top (GlobalTheory.Spread.bcDiagram p V)
    (GlobalTheory.Spread.bcCone p V) (GlobalTheory.Spread.isLimitBcCone p V)
    (π ⁻¹ᵁ dimLocus p g) (by
      rw [← Scheme.Hom.comp_preimage, hπ]
      exact preimage_dimLocus_eq_top p _ g h)
  refine ⟨Algebra.adjoin k (j.unop : Set V), Subalgebra.fg_adjoin_finset _,
    smoothOfRelativeDimension_snd p _ g ?_⟩
  have e : (GlobalTheory.Spread.bcDiagram p V).map f ≫ π = pullback.fst p _ :=
    GlobalTheory.Spread.bcMap_fst _ _
  rwa [← Scheme.Hom.comp_preimage, e] at hj

end GlobalTheory.CompanionTheory.Ar.Approx
