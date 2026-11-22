module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixRight
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hol_unif_period_matrix_right : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M B ψ) (b : Fin n → ℂ) (P : AbPart t (spMap (ψ b))) (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), b ∈ B → IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsPrincipal P.tB → GlobalTheory.CompanionTheory.Ar.QuotLoc.IsAbLift e b P φ u ℓ → (∀ y ∈ e.per b, ℓ y ∈ u.Λ) ∧ ∀ p ∈ u.Λ, ∃ y ∈ e.per b, ℓ y = p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotLoc.periods_map_onto_lattice | exact GlobalTheory.CompanionTheory.Ar.QuotLoc.periods_map_onto_lattice | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotLoc.periods_map_onto_lattice <;> assumption)
