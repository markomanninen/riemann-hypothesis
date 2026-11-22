module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BrauerDegreeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneInductionPrincipleStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducedRepresentationCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneOfFiniteImageStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultiplicativeVirtualCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalExtensionOfFiniteIndexWeilSubgroupStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupRestriction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSumTwistCompat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Whittaker

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Loc

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

section WDLemmas

theorem lpOfChar_lpTwist {p q r : Weil h →* ℂˣ} (hp : GlobalTheory.WeilDeligne.IsSmooth p)
    (hq : GlobalTheory.WeilDeligne.IsSmooth q) (hr : GlobalTheory.WeilDeligne.IsSmooth r) (e : ∀ σ, p σ * q σ = r σ) :
    (WD.lpOfChar h p hp).lpTwist q hq = WD.lpOfChar h r hr := by
  rw [WD.lpOfChar, WD.lpTwist_mk, WD.lpOfChar]
  refine WD.sound ⟨LinearEquiv.refl ℂ _, fun σ v => ?_, fun v => rfl⟩
  funext i
  simp only [LinearEquiv.refl_apply, WDRep.twist_ρ, WDRep.ofChars_ρ, LinearMap.smul_apply, Pi.smul_apply,
    diagEnd_apply, smul_eq_mul, ← e σ, Units.val_mul]
  ring

end WDLemmas

end PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

end
