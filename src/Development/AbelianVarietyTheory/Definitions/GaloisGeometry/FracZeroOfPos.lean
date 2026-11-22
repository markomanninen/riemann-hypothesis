module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {d : ℕ}

def pw (f : Fin d → R) : Submonoid R := Submonoid.powers (∏ j, f j)

def omitted (f : Fin d → R) (M : Type) [AddCommGroup M] [Module R M] : Submodule R (LocalizedModule (pw f) M) :=
  Submodule.span R {z | ∃ (j : Fin d) (k : ℕ) (m : M), z = LocalizedModule.mk (f j ^ k • m) ⟨(∏ l, f l) ^ k, by exact ⟨k, rfl⟩⟩}

abbrev LC (f : Fin d → R) (M : Type) [AddCommGroup M] [Module R M] : Type :=
  LocalizedModule (pw f) M ⧸ omitted f M

def frac (f : Fin d → R) {M : Type} [AddCommGroup M] [Module R M] (m : M) (k : ℕ) : LC f M :=
  Submodule.Quotient.mk (LocalizedModule.mk m ⟨(∏ l, f l) ^ k, by exact ⟨k, rfl⟩⟩)

theorem frac_prod_smul (f : Fin d → R) (m : M) (k : ℕ) : frac f ((∏ l, f l) • m) (k + 1) = frac f m k := by
  unfold frac
  congr 1
  rw [LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, smul_smul, pow_succ]

theorem frac_zero_of_pos (f : Fin d → R) (hd : 0 < d) (m : M) : frac f m 0 = 0 := by
  unfold frac
  rw [Submodule.Quotient.mk_eq_zero]
  apply Submodule.subset_span
  exact ⟨⟨0, hd⟩, 0, m, by simp⟩

def IsRes {B : Type} [CommRing B] [Algebra ℂ B] (s : Fin d → B) (e : B →ₐ[ℂ] MvPowerSeries (Fin d) ℂ)
    (ρ : LC s (Om ℂ B d) →ₗ[ℂ] ℂ) : Prop :=
  (∀ j, e (s j) = MvPowerSeries.X j) ∧
  (∀ ω : Om ℂ B d, ∃ h : B, ω = h • exteriorPower.ιMulti B d fun j => D ℂ B (s j)) ∧
  ∀ (k : ℕ) (h : B), ρ (frac s (h • exteriorPower.ιMulti B d fun j => D ℂ B (s j)) (k + 1)) =
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm fun _ => k) (e h)

namespace IsRes

variable {B : Type} [CommRing B] [Algebra ℂ B] {s : Fin d → B} {e : B →ₐ[ℂ] MvPowerSeries (Fin d) ℂ}
  {ρ : LC s (Om ℂ B d) →ₗ[ℂ] ℂ}

end IsRes

end GlobalTheory.W1

namespace GlobalTheory.W1.Ex

def rho0 (s : Fin 0 → ℂ) : LC s (Om ℂ ℂ 0) →ₗ[ℂ] ℂ :=
  (Submodule.liftQ (omitted s (Om ℂ ℂ 0))
    ((exteriorPower.zeroEquiv ℂ Ω[ℂ⁄ℂ]).toLinearMap ∘ₗ
      LocalizedModule.lift (pw s) LinearMap.id (fun u => by
        obtain ⟨n, hn⟩ := u.2
        have : (u : ℂ) = 1 := by simpa using hn.symm
        rw [this, map_one]; exact isUnit_one))
    (by
      have : omitted s (Om ℂ ℂ 0) = ⊥ := by
        unfold omitted
        rw [Submodule.span_eq_bot]
        rintro z ⟨j, _, _, _⟩
        exact j.elim0
      rw [this]; exact bot_le))

end GlobalTheory.W1.Ex
