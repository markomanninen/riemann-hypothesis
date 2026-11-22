module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFrameSubBasis
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_frame_sub_basis : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (V' : Submodule Ω E) (q : Cpt ξ) (g n : ℕ) (b : Fin g → E) (ix : Fin n → Fin g), Function.Injective ix → LinearIndependent Ω b → L q = Submodule.span (regAt ξ q) (Set.range b) → V' = Submodule.span Ω (Set.range (b ∘ ix)) → (L.inter V').IsFrameAt (b ∘ ix) q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SubFrame.isFrameAt_comp | exact GlobalTheory.CompanionTheory.Ar.SubFrame.isFrameAt_comp | (intros; apply GlobalTheory.CompanionTheory.Ar.SubFrame.isFrameAt_comp <;> assumption)
