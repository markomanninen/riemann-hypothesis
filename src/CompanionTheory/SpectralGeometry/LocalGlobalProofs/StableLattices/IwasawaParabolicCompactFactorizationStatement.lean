module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwasawaParabolicCompactFactorization

@[expose] public section

open Matrix
open CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

theorem GlobalTheory.T.iwasawa_parabolic_compact_factorization :
    ∀ (n : ℕ) (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ), IsGrad ε A →
      ∀ g : S7.UJ ε, ∃ (x : PSub ε A) (k : S7.KG ε), g = (x : S7.UJ ε) * (k : S7.UJ ε) :=
  GlobalTheory.CompanionTheory.UGeo.iwasawa_psub
