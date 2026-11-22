module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CubicalTripleTrivial
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsAbLift
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalBundlePairingCompatiblePullback
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonDegAtOfSabMap

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.UU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubical_triple_trivial : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → TorusExtension G → ∀ (v : Γ((G ⊗ G ⊗ G).left, ⊤)ˣ), (∀ (T : Over (Sp K)) (x y : T ⟶ G), (lift (1 : T ⟶ G) (lift x y)).left.appTop.hom v.val = 1 ∧ (lift x (lift (1 : T ⟶ G) y)).left.appTop.hom v.val = 1 ∧ (lift x (lift y (1 : T ⟶ G))).left.appTop.hom v.val = 1) → ∀ x y w : 𝟙_ (Over (Sp K)) ⟶ G, (lift x (lift y w)).left.appTop.hom v.val = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CubeUnit.eq_one_at_rational_points | exact GlobalTheory.CompanionTheory.Ar.CubeUnit.eq_one_at_rational_points | (intros; apply GlobalTheory.CompanionTheory.Ar.CubeUnit.eq_one_at_rational_points <;> assumption)
