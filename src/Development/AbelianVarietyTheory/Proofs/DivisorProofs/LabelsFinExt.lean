module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrExtensionQkPointsRational
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PsiGenOnInteriorOfPsiUnitOn
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.LabExt

open GlobalTheory.ArcPull GlobalTheory.TorusExt

theorem qkExt_refl {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {C : Type} [Field C]
    [Algebra (FractionRing R) C] {k : ℕ} (p : QkPt D C k) : QkExt (RingHom.id C) p p := by
  have e : spMap (RingHom.id C) = 𝟙 _ := Spec.map_id _
  refine ⟨rfl, by rw [e, Category.id_comp], fun χ => ?_⟩
  rw [e]
  exact corr_of_val D.P.isLB fun y J hJ =>
    ((val_pull hJ _ _ _).trans (congrArg (fun r => val (p.g.s χ) r y J) (Category.id_comp _))).symm

section Lab

variable {R R₁ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [IsDomain R₁] {ρ : R →+* R₁}
  {D : DegPre R} {D₁ : DegPre R₁} [Algebra (FractionRing R) (Kb R₁)]

variable {A : PolAV (Sp (FractionRing R))} {A₁ : PolAV (Sp (FractionRing R₁))}

end Lab

end GlobalTheory.LabExt
