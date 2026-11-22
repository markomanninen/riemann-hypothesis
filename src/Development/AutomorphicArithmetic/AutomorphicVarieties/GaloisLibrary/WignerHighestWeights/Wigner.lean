module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.MsetSep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.QdetIntertw
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.ActOpApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.AlphaReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.AltFlip
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.InfAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.TensDer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.wigner : GlobalTheory.Published.WignerVanishingGL := by
  intro E _ _ _ a π Ξ m m' hm hm' hne
  obtain ⟨τ, hτ⟩ := Function.ne_iff.1 hne
  obtain ⟨u, hu⟩ : ∃ u : ℂ, ((m τ).map (u + ·)).prod ≠ ((m' τ).map (u + ·)).prod := by
    by_contra h
    exact hτ (msetSep _ _ fun u => not_not.1 fun h' => h ⟨u, h'⟩)
  obtain ⟨a1, a2, a3⟩ := tensA E a π Ξ
  obtain ⟨b1, b2, b3⟩ := tensB E a π Ξ
  obtain ⟨α, hα⟩ := alphaReal E a _ (tensorK π Ξ) (lieA π Ξ) (lieB π Ξ) a1 b1 (lieA_commute π Ξ) a2 b2 τ _ _ _
    (a3 τ _ (hm τ) u) (b3 τ _ (hm' τ) u) hu
  exact homot E a _ (tensorK π Ξ) (tensorLie π Ξ) α hα (infAbs E a _ _ _ (tensDer E a π Ξ))
