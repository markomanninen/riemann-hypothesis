module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifyingMapSymplecticLevelEquivariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFinitePresentationOfIsQProjOver

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem existsUnique_of_openImmersion : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) (M : Model b N) (Y₀ Y : Scheme.{0}) (i : Y₀ ⟶ Y) (s₀ : Y₀ ⟶ M.X) (s : Y ⟶ M.X) (σ₀ : Y₀ ⟶ Sp R) (σ : Y ⟶ Sp R) (o o' : Obj b N σ) (o₀ o₀' : Obj b N σ₀) (m : ObjMap o₀ o i) (m' : ObjMap o₀' o' i) (ψ₀ : o₀.A ⟶ o₀'.A) (ψ : o.A ⟶ o'.A), IsOpenImmersion i → i ≫ s = s₀ → m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ → (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) → (∀ (S : Scheme.{0}) (x : S ⟶ M.X) (o₁ o₁' : Obj b N (x ≫ M.s)) (m₁ : ObjMap o₁ M.univ x) (ψ₁ : o₁.A ⟶ o₁'.A), IsUnit ((p : ℕ) : Γ(S, ⊤)) → IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : S ⟶ Y₀, y ≫ s₀ = x ∧ ∃ (m₀ : ObjMap o₁ o₀ y) (m₂ : ObjMap o₁' o₀' y), m₀.φ ≫ ψ₀.left = ψ₁.left ≫ m₂.φ) → ∀ (S : Scheme.{0}) (x : S ⟶ M.X) (o₁ o₁' : Obj b N (x ≫ M.s)) (m₁ : ObjMap o₁ M.univ x) (ψ₁ : o₁.A ⟶ o₁'.A), IsUnit ((p : ℕ) : Γ(S, ⊤)) → IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : S ⟶ Y, y ≫ s = x ∧ ∃ (m₀ : ObjMap o₁ o y) (m₂ : ObjMap o₁' o' y), m₀.φ ≫ ψ.left = ψ₁.left ≫ m₂.φ := by
  intro p _ D R _ b N _ _ r w j c M Y₀ Y i s₀ s σ₀ σ o o' o₀ o₀' m m' ψ₀ ψ _ his hsq hfac hU S x o₁ o₁' m₁ ψ₁
    hp hisog htj
  have comp_map {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
      {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁}
      {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : ObjMap o₁ o₂ f) (h₂ : ObjMap o₂ o₃ g) :
      ∃ m : ObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
    have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
      constructor
      · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
      · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
    have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
      intro c
      rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
    have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
      intro y
      rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
    have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
    have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
      LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
    have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
      LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
    exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩
  obtain ⟨y₀, ⟨hy₀, m₀, m₂, hsq₀⟩, huniq⟩ := hU S x o₁ o₁' m₁ ψ₁ hp hisog htj
  obtain ⟨a, ha⟩ := comp_map m₀ m
  obtain ⟨b, hb⟩ := comp_map m₂ m'
  refine ⟨y₀ ≫ i, ⟨by rw [Category.assoc, his, hy₀], a, b, ?_⟩, ?_⟩
  · rw [ha, hb]
    rw [Category.assoc, hsq, ← Category.assoc, hsq₀, Category.assoc]
  · rintro y ⟨hy, n₀, n₂, hsqn⟩
    obtain ⟨f₀, rfl⟩ := hfac S y hp
    obtain ⟨k₀, hk₀⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ n₀ m
    obtain ⟨k₂, hk₂⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ n₂ m'
    have hsqk : k₀.φ ≫ ψ₀.left = ψ₁.left ≫ k₂.φ := by
      apply m'.cart.1.hom_ext
      · rw [Category.assoc, Category.assoc, ← hsq, ← Category.assoc, hk₀, hsqn, ← hk₂]
      · rw [Category.assoc, Over.w ψ₀, k₀.cart.1.w, Category.assoc, k₂.cart.1.w, ← Category.assoc, Over.w ψ₁]
    have e := huniq f₀ ⟨by rw [← his, ← Category.assoc]; exact hy, k₀, k₂, hsqk⟩
    rw [e]

end GlobalTheory.UPel.HT.ES
