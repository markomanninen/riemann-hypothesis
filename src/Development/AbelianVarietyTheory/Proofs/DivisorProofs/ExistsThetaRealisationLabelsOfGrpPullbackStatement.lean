module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaRealisationLabelsOfGrpPullback
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
theorem _root_.GlobalTheory.T.exists_thetaRealisation_labels_of_grpPullback : ∀ {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] (S₁ : ThetaSys o₁ Ω₁) (S₂ : ThetaSys o₂ Ω₂) (ρ₁ : S₁.Real) (ρ₂ : S₂.Real) (om : S₁.R →+* S₂.R) (φ : ρ₂.P.A.left ⟶ ρ₁.P.A.left) (d : ℕ), IsGrpPullback ρ₂.P.A ρ₁.P.A (spMap om) φ → S₂.r * S₂.N = S₁.r * S₁.N * d → ∃ lam : S₁.Gam →+ S₂.Gam, (∀ a, (ρ₂.pt (lam a)).left ≫ φ = spMap om ≫ (ρ₁.pt a).left) ∧ ∀ a', ∃ a, lam a = d • a' := by
  first | exact @GlobalTheory.Poinc.PullLab.exists_lab_of_isGrpPullback | exact GlobalTheory.Poinc.PullLab.exists_lab_of_isGrpPullback | (intros; apply GlobalTheory.Poinc.PullLab.exists_lab_of_isGrpPullback <;> assumption)
