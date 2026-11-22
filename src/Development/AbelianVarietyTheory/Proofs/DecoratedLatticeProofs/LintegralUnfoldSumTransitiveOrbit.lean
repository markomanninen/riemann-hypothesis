module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TsumSetIntegralFundamentalDomainEqZeroByOrbits

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ENNReal Pointwise

namespace GlobalTheory
namespace Unf

theorem lintegral_integral_unfold_transitive : ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant] (Γ : Subgroup H) [Countable Γ] (Y : Type) [Countable Y] [MulAction Γ Y] (y₀ : Y), (∀ y, ∃ γ : Γ, γ • y₀ = y) → ∀ (𝓕 𝓖 : Set H), IsFundamentalDomain Γ 𝓕 ν → IsFundamentalDomain ((MulAction.stabilizer Γ y₀).map Γ.subtype) 𝓖 ν → ∀ Φ : Y → H → ℂ, (∀ y, Measurable (Φ y)) → (∀ (γ : Γ) y h, Φ (γ • y) ((γ : H) * h) = Φ y h) → (∫⁻ h in 𝓖, ‖Φ y₀ h‖ₑ ∂ν = ∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν) ∧ (∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν ≠ ⊤ → ∫ h in 𝓖, Φ y₀ h ∂ν = ∫ h in 𝓕, ∑' y, Φ y h ∂ν) := by
  intro H _ _ _ ν _ Γ _ Y _ _ y₀ htr 𝓕 𝓖 hF hG Φ hΦ hinv
  set S : Subgroup H := (MulAction.stabilizer Γ y₀).map Γ.subtype with hSdef
  haveI : Countable S := by
    have hle : S ≤ Γ := Subgroup.map_subtype_le _
    exact Function.Injective.countable (Subgroup.inclusion_injective hle)
  choose σ hσ using htr
  have hO : ∀ γ : Γ, γ • y₀ ∈ (Set.univ : Set Y) := fun _ => Set.mem_univ _
  have hσ' : ∀ a : (Set.univ : Set Y), σ a • y₀ = a := fun a => hσ a
  let pull (g : H) : Set H := (fun h => g * h) ⁻¹' 𝓕
  have hnull (g : H) : NullMeasurableSet (pull g) ν :=
    hF.nullMeasurableSet.preimage (measurePreserving_mul_left ν g).quasiMeasurePreserving
  have hpull (c : Γ) : pull (c : H) = c⁻¹ • 𝓕 := by
    ext x
    simp [pull, Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
  have hG' : IsFundamentalDomain S (⋃ y : Y, pull (σ y : H)) ν := by
    refine ⟨.iUnion (fun y => hnull _), ?_, ?_⟩
    · filter_upwards [hF.ae_covers] with x ⟨γ, hγ⟩
      have hs : (σ (γ • y₀))⁻¹ * γ ∈ MulAction.stabilizer Γ y₀ := by
        rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, hσ]
      refine ⟨⟨Γ.subtype ((σ (γ • y₀))⁻¹ * γ), Subgroup.mem_map_of_mem _ hs⟩,
        Set.mem_iUnion.2 ⟨γ • y₀, ?_⟩⟩
      simpa [pull, Subgroup.smul_def, mul_assoc] using hγ
    · rintro ⟨_, s, hs, rfl⟩ ⟨_, t, ht, rfl⟩ hst
      have hset : ∀ (u : Γ) (hu : u ∈ MulAction.stabilizer Γ y₀) (a : Y),
          (⟨Γ.subtype u, Subgroup.mem_map_of_mem _ hu⟩ : S) • pull (σ a : H) =
            (σ a * u⁻¹)⁻¹ • 𝓕 := by
        intro u hu a
        ext x
        simp [Set.mem_smul_set_iff_inv_smul_mem, pull, Subgroup.smul_def, mul_assoc]
      simp only [Function.onFun, Set.smul_set_iUnion, hset s hs, hset t ht]
      refine AEDisjoint.iUnion_left_iff.2 fun a => AEDisjoint.iUnion_right_iff.2 fun b => ?_
      refine hF.aedisjoint (inv_injective.ne fun h => hst ?_)
      have hab : a = b := by
        have h1 := congrArg (· • y₀) h
        simp only [mul_smul] at h1
        rwa [inv_smul_eq_iff.2 hs.symm, inv_smul_eq_iff.2 ht.symm, hσ, hσ] at h1
      subst hab
      have : s = t := inv_injective (mul_left_cancel h)
      subst this
      rfl
  have hinvS : ∀ (s : S) (h : H), Φ y₀ (s • h) = Φ y₀ h := by
    rintro ⟨s, hs⟩ h
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hs
    have := hinv t y₀ h
    rw [show t • y₀ = y₀ from ht] at this
    simpa [Subgroup.smul_def] using this
  have hfun : ∀ (y : Y) (h : H), Φ y ((σ y : H) * h) = Φ y₀ h := fun y h => by
    have := hinv (σ y) y₀ h
    rwa [hσ y] at this
  have hlint : ∀ y : Y, ∫⁻ h in pull (σ y : H), ‖Φ y₀ h‖ₑ ∂ν
      = ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν := fun y => by
    rw [← (measurePreserving_mul_left ν (σ y : H)).setLIntegral_comp_preimage_emb (measurableEmbedding_mulLeft (σ y : H)) (fun h => ‖Φ y h‖ₑ) 𝓕]
    simp only [hfun, pull]
  have hint : ∀ y : Y, ∫ h in pull (σ y : H), Φ y₀ h ∂ν
      = ∫ h in 𝓕, Φ y h ∂ν := fun y => by
    rw [← (measurePreserving_mul_left ν (σ y : H)).setIntegral_preimage_emb (measurableEmbedding_mulLeft (σ y : H)) (Φ y) 𝓕]
    simp only [hfun, pull]
  have hd : Pairwise (Function.onFun (AEDisjoint ν) fun y : Y =>
      pull (σ y : H)) := by
    intro a b hab
    dsimp only [Function.onFun]
    rw [hpull, hpull]
    refine hF.aedisjoint (inv_injective.ne fun h => hab ?_)
    rw [← hσ a, ← hσ b, h]
  have hL1 : ∫⁻ h in 𝓖, ‖Φ y₀ h‖ₑ ∂ν
      = ∫⁻ h in ⋃ y : Y, pull (σ y : H), ‖Φ y₀ h‖ₑ ∂ν :=
    hG.setLIntegral_eq hG' (fun h => ‖Φ y₀ h‖ₑ) (fun s h => by simp only [hinvS])
  have hL2 : ∫⁻ h in ⋃ y : Y, pull (σ y : H), ‖Φ y₀ h‖ₑ ∂ν
      = ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν := by
    rw [lintegral_iUnion₀ (fun y => hnull _) hd]
    simp only [hlint]
  have hL3 : ∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν = ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν :=
    lintegral_tsum fun y => (hΦ y).enorm.aemeasurable
  have hmain : ∫⁻ h in 𝓖, ‖Φ y₀ h‖ₑ ∂ν = ∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν := by
    rw [hL1, hL2, hL3]
  refine ⟨hmain, fun hfin => ?_⟩
  have hfin' : ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν ≠ ⊤ := by rwa [← hL3]
  have hI : IntegrableOn (Φ y₀) (⋃ y : Y, pull (σ y : H)) ν := by
    refine ⟨(hΦ y₀).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, hL2]
    exact lt_top_iff_ne_top.2 hfin'
  have hI1 : ∫ h in 𝓖, Φ y₀ h ∂ν
      = ∫ h in ⋃ y : Y, pull (σ y : H), Φ y₀ h ∂ν :=
    hG.setIntegral_eq hG' (fun s h => hinvS s h)
  rw [hI1, integral_iUnion_ae (fun y => hnull _) hd hI]
  simp only [hint]
  exact (integral_tsum (fun y => (hΦ y).aestronglyMeasurable) hfin').symm

end Unf
end GlobalTheory
