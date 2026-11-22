module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoOfAmpleDeterminantFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_of_ampleDeterminantFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z Z₁ Z₂ : Scheme.{0}) [IsLocallyNoetherian Z] (z : Z ⟶ Sp ℤ) (t : SAB H Z) (t₁ : SAB H Z₁) (t₂ : SAB H Z₂) (f₁ : Z ⟶ Z₁) (f₂ : Z ⟶ Z₂) (_ : SABMap t t₁ f₁) (_ : SABMap t t₂ f₂) (N : ℕ) (A₁ : GlobalTheory.LN.AmpFrames t₁.G t₁.PP.L N) (A₂ : GlobalTheory.LN.AmpFrames t₂.G t₂.PP.L N), IsNormalScheme Z → Flat z → genericPoints Z ⊆ abLocus t.G → A₁.r = A₂.r → A₁.s = A₂.s → LBIso (A₁.A.pull f₁) (A₂.A.pull f₂) := by
  first | exact @GlobalTheory.FrameCmp.lbIso_of_ampFrames | exact GlobalTheory.FrameCmp.lbIso_of_ampFrames | (intros; apply GlobalTheory.FrameCmp.lbIso_of_ampFrames <;> assumption)
