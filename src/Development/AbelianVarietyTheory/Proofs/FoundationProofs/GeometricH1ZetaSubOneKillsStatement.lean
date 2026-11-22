module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricH1ZetaSubOneKills
public import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow

@[expose] public section

open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_h1_zeta_sub_one_kills : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (k j : ℕ), 1 ≤ j → ∀ c : Gal p Ω → Ω, IntegralLocallyConstCochainModPow k (Ggeo p Ω ⊓ ⨅ n, Gn T n) c →
  (∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, Cong (p := p) k (c (g * h)) (c g + g (c h))) →
  Cob1 k (Ggeo p Ω ⊓ ⨅ n, Gn T n) (fun g => (T.ζ j - 1) * c g) := by
  intro p _ hp2 Ω _ _ hΩ T k j hj c hc hcoc
  classical
  let H := Ggeo p Ω ⊓ ⨅ n, Gn T n
  have uniform : ∃ S : Finset Ω, ∀ g ∈ H, ∀ h ∈ H,
      (∀ x ∈ S, h x = g x) → Cong (p := p) k (c h) (c g) := by
    have localTests : ∀ g : Gal p Ω, ∃ S : Finset Ω,
        (g ∈ H → ∀ h ∈ H, (∀ x ∈ S, h x = g x) → Cong (p := p) k (c h) (c g)) ∧
        (g ∉ H → ∀ h ∈ H, ¬ ∀ x ∈ S, h x = g x) := by
      intro g
      by_cases hg : g ∈ H
      · obtain ⟨S, hS⟩ := hc.2 g hg
        exact ⟨S, fun _ => hS, fun h => (h hg).elim⟩
      · obtain ⟨a, hga, ha⟩ := TateGeo.exists_moved T hg
        refine ⟨{a}, fun h => (hg h).elim, fun _ h hh agree => hga ?_⟩
        exact (agree a (Finset.mem_singleton_self a)).symm.trans (ha h hh)
    choose S hlocal hsep using localTests
    obtain ⟨F, hF⟩ := GlobalTheory.T.finite_galois_approximation p Ω hΩ S
    refine ⟨F.biUnion S, fun g hg h hh agree => ?_⟩
    obtain ⟨g₀, hg₀F, hg₀⟩ := hF g
    have hg₀H : g₀ ∈ H := by
      by_contra h
      exact hsep g₀ h g hg hg₀
    have hg' := hlocal g₀ hg₀H g hg hg₀
    have hh' := hlocal g₀ hg₀H h hh (fun x hx =>
      (agree x (Finset.mem_biUnion.mpr ⟨g₀, hg₀F, hx⟩)).trans (hg₀ x hx))
    simpa [Cong] using Basic.cong_sub hh' hg'
  obtain ⟨S, hS⟩ := uniform
  obtain ⟨y, E, hy, hEH, hu, hsum⟩ :=
    GlobalTheory.T.smallTraces_subgroup_galois_towerTop p Ω hp2 hΩ T H inf_le_right S j hj
  let x : Ω := ∑ g ∈ E, g y * c g
  have hx : IsInt (p := p) x := by
    refine IsIntegral.sum _ fun g hg => ?_
    exact (IsIntegral.map g.toAlgHom hy).mul (hc.1 g (hEH g hg))
  refine ⟨-x, hx.neg, fun h hh => ?_⟩
  have hσ : ∀ g ∈ E, ∃ g' ∈ E, h (g y) = g' y ∧ ∀ s ∈ S, h (g s) = g' s := by
    intro g hg
    obtain ⟨g', ⟨hg', hy', hs'⟩, -⟩ := hu (h * g) (H.mul_mem hh (hEH g hg))
    exact ⟨g', hg', hy', hs'⟩
  choose! σ hσE hσy hσS using hσ
  have hσinj : Set.InjOn σ E := by
    intro g₁ hg₁ g₂ hg₂ e
    apply (hu g₁ (hEH g₁ hg₁)).unique ⟨hg₁, rfl, fun _ _ => rfl⟩
    refine ⟨hg₂, h.injective ?_, fun s hs => h.injective ?_⟩
    · rw [hσy g₁ hg₁, hσy g₂ hg₂, e]
    · rw [hσS g₁ hg₁ s hs, hσS g₂ hg₂ s hs, e]
  have himage : E.image σ = E :=
    Finset.eq_of_subset_of_card_le (by simpa only [Finset.image_subset_iff] using hσE)
      (by rw [Finset.card_image_of_injOn hσinj])
  have hperm : ∑ g ∈ E, σ g y * c (σ g) = x := by
    rw [← Finset.sum_image (f := fun g' => g' y * c g') hσinj, himage]
  have hhx : h x = ∑ g ∈ E, h (g y) * h (c g) := by
    simp only [x, map_sum, map_mul]
  have hζ : h (T.ζ j) = T.ζ j := (((TateGeo.mem_geoTop_iff T h).mp hh).2 j).1
  have hsumh : ∑ g ∈ E, h (g y) = T.ζ j - 1 := by
    rw [← map_sum, hsum, map_sub, map_one, hζ]
  have termCong : ∀ g ∈ E, Cong (p := p) k (h (g y) * h (c g))
      (σ g y * c (σ g) - h (g y) * c h) := by
    intro g hg
    have hgH := hEH g hg
    obtain ⟨a, ha, ea⟩ := hcoc h hh g hgH
    obtain ⟨b, hb, eb⟩ := hS (σ g) (hEH _ (hσE g hg)) (h * g) (H.mul_mem hh hgH) (hσS g hg)
    refine ⟨h (g y) * (b - a), (IsIntegral.map h.toAlgHom (IsIntegral.map g.toAlgHom hy)).mul (hb.sub ha), ?_⟩
    rw [← hσy g hg]
    linear_combination h (g y) * (eb - ea)
  have sumCong (s : Finset (Gal p Ω)) (f f' : Gal p Ω → Ω)
      (hs : ∀ g ∈ s, Cong (p := p) k (f g) (f' g)) :
      Cong (p := p) k (∑ g ∈ s, f g) (∑ g ∈ s, f' g) := by
    induction s using Finset.induction_on with
    | empty => simpa using Basic.cong_refl (p := p) k (0 : Ω)
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact Basic.cong_add (hs a (Finset.mem_insert_self a s))
        (ih fun g hg => hs g (Finset.mem_insert_of_mem hg))
  have total := sumCong E _ _ termCong
  rw [← hhx, Finset.sum_sub_distrib, hperm, ← Finset.sum_mul, hsumh] at total
  obtain ⟨z, hz, e⟩ := total
  refine ⟨z, hz, ?_⟩
  show (T.ζ j - 1) * c h - (h (-x) - -x) = _
  rw [map_neg]
  linear_combination e
