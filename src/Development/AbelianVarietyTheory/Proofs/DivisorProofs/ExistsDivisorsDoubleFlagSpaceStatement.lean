module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorsDoubleFlagSpace
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_divisors_doubleFlagSpace : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (gr : Root m → Y.Dv), ∀ B ∈ E'.S (genericPoint Y.X), (∀ (y : Y.X) (x : Root m), ∃ A ∈ E'.S y, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t) → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → AlmostLow τ a b (B.map W.α₁ * (B.map W.α₂)⁻¹) → ∃ (D₁ D₂ : Root m → CartierDiv W.Z) (Θ : CartierDiv W.Z), (∀ x, IsPull W.p₁ (D₁ x) (gr x)) ∧ (∀ x, IsPull W.p₂ (D₂ x) (gr x)) ∧ (∀ x, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ → toPic (D₁ x) = toPic (D₂ x)) ∧ toPic (D₁ ⟨τ, a⟩) + toPic (D₁ ⟨τ, b⟩) = toPic (D₂ ⟨τ, a⟩) + toPic (D₂ ⟨τ, b⟩) ∧ toPic Θ = toPic (D₂ ⟨τ, b⟩) - toPic (D₁ ⟨τ, a⟩) ∧ Θ.Eff ∧ (Θ.supp : Set W.Z) = Set.range W.δ := by
  intro F _ X Y ι _ m E E' φ f hf gr B hB hgr W hα τ a b hab hC
  choose D₁ hD₁ using fun x => GlobalTheory.T.exists_cartierDivisor_pullback_of_dominant W.Z Y.X W.p₁ (gr x)
  choose D₂ hD₂ using fun x => GlobalTheory.T.exists_cartierDivisor_pullback_of_dominant W.Z Y.X W.p₂ (gr x)
  have hC0 : Par 0 ⊤ (B.map W.α₁ * (B.map W.α₂)⁻¹) := fun σ =>
    ⟨fun _ _ => trivial, hC.1 σ, trivial, fun i j hi => absurd hi (by simp)⟩
  obtain ⟨hCd, hCm, -⟩ := GlobalTheory.T.almostLowerTriangular_diag_minor_isUnit ι m τ a b hab _ ⊤ _ hC hC0
  have K := fun (z : W.Z) {A₁ A₂ : Mat m Y.Fn} (hA₁ : A₁ ∈ E'.S (W.p₁ z)) (hA₂ : A₂ ∈ E'.S (W.p₂ z)) =>
    GlobalTheory.FlagPush.DivOn.key hf hB hgr W hα hab hC hD₁ hD₂ z hA₁ hA₂
  have hne : a ≠ b := fun h => by rw [h] at hab; omega
  have hΘ : ∀ (z : W.Z) {A₁ A₂ : Mat m Y.Fn} (hA₁ : A₁ ∈ E'.S (W.p₁ z)) (hA₂ : A₂ ∈ E'.S (W.p₂ z)),
      ∃ g : W.Z.functionFieldˣ, (g : W.Z.functionField) = (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) τ a b ∧
        (D₂ ⟨τ, b⟩ - D₁ ⟨τ, a⟩ + CartierDiv.principal (Units.mk0 _ hC.2.1)).IsEqn z g := fun z A₁ A₂ hA₁ hA₂ => by
    obtain ⟨t₁, t₂, q₁, q₂, -, -, -, e, -⟩ := K z hA₁ hA₂
    refine ⟨_, ?_, ((q₂ ⟨τ, b⟩).sub (q₁ ⟨τ, a⟩)).add (CartierDiv.isEqn_principal _ z)⟩
    rw [e, Units.val_mul, Units.val_div_eq_div_val, Units.val_mk0]
    ring
  refine ⟨D₁, D₂, D₂ ⟨τ, b⟩ - D₁ ⟨τ, a⟩ + CartierDiv.principal (Units.mk0 _ hC.2.1), hD₁, hD₂, fun x hxa hxb => ?_,
    ?_, ?_, fun z => ?_, ?_⟩
  · have e : D₂ x + CartierDiv.principal (Units.mk0 _ (hCd x hxa hxb).1) = D₁ x :=
      CartierDiv.ext_of_isEqn fun z => by
        obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
        obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
        obtain ⟨t₁, t₂, q₁, q₂, -, hu, -⟩ := K z hA₁ hA₂
        refine ⟨_, (q₂ x).add (CartierDiv.isEqn_principal _ z), (q₁ x).iff_unitAt.2 ?_⟩
        convert hu x hxa hxb using 1
        rw [Units.val_mul, Units.val_mk0]
        ring
    rw [← e, map_add (f := _), toPic_principal, add_zero]
  · have e : D₂ ⟨τ, a⟩ + D₂ ⟨τ, b⟩ + CartierDiv.principal (Units.mk0 _ hCm) = D₁ ⟨τ, a⟩ + D₁ ⟨τ, b⟩ :=
      CartierDiv.ext_of_isEqn fun z => by
        obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
        obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
        obtain ⟨t₁, t₂, q₁, q₂, -, -, hu, -⟩ := K z hA₁ hA₂
        refine ⟨_, ((q₂ _).add (q₂ _)).add (CartierDiv.isEqn_principal _ z), ((q₁ _).add (q₁ _)).iff_unitAt.2 ?_⟩
        convert hu using 1
        simp only [Units.val_mul, Units.val_mk0]
        ring
    rw [← map_add (f := _), ← map_add (f := _), ← e, map_add _ (_ + _), toPic_principal, add_zero]
  · rw [map_add (f := _), toPic_principal, add_zero, map_sub]
  · obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
    obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
    obtain ⟨g, e, hg⟩ := hΘ z hA₁ hA₂
    obtain ⟨t₁, t₂, -, -, -, -, -, -, hr⟩ := K z hA₁ hA₂
    exact ⟨g, hg, by rw [one_mul, e]; exact hr⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
      obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
      obtain ⟨g, e, hg⟩ := hΘ z hA₁ hA₂
      obtain ⟨t₁, t₂, -, -, hal, -⟩ := K z hA₁ hA₂
      refine GlobalTheory.T.mem_range_diagonal_of_not_unit_transitionEntry F X Y ι m E E' φ f hf W hα τ a b z A₁ hA₁ A₂ hA₂ hal ?_
      rw [← e]
      exact hg.mem_supp_iff.1 hz
    · rintro ⟨y, rfl⟩
      obtain ⟨A, hA⟩ := E'.nonempty y
      have e₁ : W.p₁ (W.δ y) = y := by rw [← Scheme.Hom.comp_apply, W.δ₁]; rfl
      have e₂ : W.p₂ (W.δ y) = y := by rw [← Scheme.Hom.comp_apply, W.δ₂]; rfl
      obtain ⟨g, e, hg⟩ := hΘ (W.δ y) (A₁ := A) (A₂ := A) (by rw [e₁]; exact hA) (by rw [e₂]; exact hA)
      refine hg.mem_supp_iff.2 ?_
      rw [e]
      exact GlobalTheory.T.not_isUnit_offDiagonal_transition_on_commonSection F X Y ι m E E' φ f hf W hα τ a b hne y A hA
