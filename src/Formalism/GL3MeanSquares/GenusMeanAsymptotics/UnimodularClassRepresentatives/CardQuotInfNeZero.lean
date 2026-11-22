module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FormRightMem
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardEqRelIndex

@[expose] public section

open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem card_quot_inf_ne_zero {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₂ : Submodule.IsFullLattice K M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    Nat.card (↥(locF 𝔭 M₁) ⧸ (locF 𝔭 M₁ ⊓ locF 𝔭 M₂).submoduleOf (locF 𝔭 M₁)) ≠ 0 := by
  obtain ⟨r, hr⟩ := IA.exists_pow_smul h𝔭 hM₁ hM₂
  rw [IA.card_eq_relIndex h𝔭 hr]
  exact IA.relIndex_ne_zero hM₁ hM₂ 𝔭

theorem card_quot_inf_mul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsFullLattice K M₁)
    (hM₁i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₁)
    (hM₂ : Submodule.IsFullLattice K M₂)
    (hM₂i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    Nat.card (↥(locF 𝔭 M₁) ⧸ (locF 𝔭 M₁ ⊓ locF 𝔭 M₂).submoduleOf (locF 𝔭 M₁)) *
        Ideal.absNorm 𝔭 ^ vd h (locF 𝔭 M₁) 𝔭 =
      Nat.card (↥(locF 𝔭 M₂) ⧸ (locF 𝔭 M₁ ⊓ locF 𝔭 M₂).submoduleOf (locF 𝔭 M₂)) *
        Ideal.absNorm 𝔭 ^ vd h (locF 𝔭 M₂) 𝔭 := by
  obtain ⟨r₁, hr₁⟩ := IA.exists_pow_smul h𝔭 hM₁.toIsLattice hM₂
  obtain ⟨r₂, hr₂⟩ := IA.exists_pow_smul h𝔭 hM₂.toIsLattice hM₁
  have e₁ := IA.card_eq_relIndex h𝔭 hr₁
  have e₂ := IA.card_eq_relIndex h𝔭 hr₂
  rw [inf_comm (locF 𝔭 M₂) (locF 𝔭 M₁)] at e₂
  have hAB : vd h (M₁ ⊓ locF 𝔭 M₂) 𝔭 = vd h (M₂ ⊓ locF 𝔭 M₁) 𝔭 := by
    rw [← localizedQuotients.vd_locF hF h (M₁ ⊓ locF 𝔭 M₂) h𝔭,
      ← localizedQuotients.vd_locF hF h (M₂ ⊓ locF 𝔭 M₁) h𝔭,
      IA.locF_inf 𝔭 h𝔭.isPrime M₁ M₂, IA.locF_inf 𝔭 h𝔭.isPrime M₂ M₁, inf_comm]
  rw [e₁, e₂, localizedQuotients.vd_locF hF h M₁ h𝔭, localizedQuotients.vd_locF hF h M₂ h𝔭,
    IA.vd_mul hF hK hs hd hM₁ hM₁i hM₂ h𝔭, IA.vd_mul hF hK hs hd hM₂ hM₂i hM₁ h𝔭, hAB]

end Formalism.HermitianLattices.Ext.L3.LIOrb
