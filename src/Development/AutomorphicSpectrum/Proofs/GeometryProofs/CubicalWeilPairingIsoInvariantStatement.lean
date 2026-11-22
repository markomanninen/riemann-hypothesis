module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CubicalWeilPairingIsoInvariant
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
theorem _root_.GlobalTheory.T.cubical_weil_pairing_iso_invariant : ∀ (G : Over (Sp ℂ)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → TorusExtension G → ∀ (L₁ L₂ : RigLB G) (c₁ : CubicalStr G L₁) (c₂ : CubicalStr G L₂), LBIso L₁.L L₂.L → ∀ (N : ℕ) (x y : 𝟙_ (Over (Sp ℂ)) ⟶ G) (ζ : Γ(Sp ℂ, ⊤)ˣ), CubWeil c₁ N x y ζ → CubWeil c₂ N x y ζ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CubIso.cubWeil_of_lbIso | exact GlobalTheory.CompanionTheory.Ar.CubIso.cubWeil_of_lbIso | (intros; apply GlobalTheory.CompanionTheory.Ar.CubIso.cubWeil_of_lbIso <;> assumption)
