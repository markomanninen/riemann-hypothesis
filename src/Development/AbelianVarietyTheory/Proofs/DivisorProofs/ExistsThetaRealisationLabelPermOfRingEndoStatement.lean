module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaRealisationLabelPermOfRingEndo
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalEndOfEighthPowerOfPolAVPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisOfPolAVPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisationModelFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithBaseFiniteContainingRootOfUnity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationPullbackStable
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFractionRingOfForallDiv
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemOfPolarisedLevel

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaRealisation_label_perm_of_ringEndo : ∀ {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] (S₁ : ThetaSys o₁ Ω₁) (S₂ : ThetaSys o₂ Ω₂) (ρ₁ : S₁.Real) (ρ₂ : S₂.Real) (om : S₁.R →+* S₂.R) (φ : ρ₂.P.A.left ⟶ ρ₁.P.A.left), IsGrpPullback ρ₂.P.A ρ₁.P.A (spMap om) φ → ∀ τ : S₂.R →+* S₂.R, τ.comp om = om → ∃ gl : S₂.Gam →+ S₂.Gam, ∀ a, (ρ₂.pt (gl a)).left ≫ φ = spMap τ ≫ (ρ₂.pt a).left ≫ φ := by
  first | exact @GlobalTheory.Poinc.labelHom_of_comp_eq | exact GlobalTheory.Poinc.labelHom_of_comp_eq | (intros; apply GlobalTheory.Poinc.labelHom_of_comp_eq <;> assumption)
