module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U]


variable (A U) in
@[ext] structure Th where

  x : A

  f : A → U

variable {ν ν' : A → U} {N : ℕ} {g h : Th A U}

end Alg

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} {T T' : Over S} (σ : T' ⟶ T) (z : T'.left)
  (J : (T'.left ⟶ A.left) → L.L.ι)

def IsGeo (k : ℕ) (x : T ⟶ A) (g : Th (T' ⟶ A) (T'.left.presheaf.stalk z)ˣ) : Prop :=
  g.x = σ ≫ x ∧ ∃ (K : Type) (_ : Fintype K) (φ : K → ((T ⊗ A).left ⟶ A.left)) (ε : K → ℤ) (u : LB.Gen (LB.LinComb L.L φ ε)),
    u.IsGen ∧ (∀ (U : Type) [CommGroup U] (h : ((T ⊗ A).left ⟶ A.left) → U), ∏ i, h (φ i) ^ ε i =
      h (snd T A).left ^ k * (h ((fst T A ≫ x) * snd T A).left ^ k)⁻¹) ∧ ∀ y, val u (lift σ y).left z J = g.f y

variable {σ z J} (hJ : Good L.L z J) {k : ℕ} {x x' : T ⟶ A} {g g' : Th (T' ⟶ A) (T'.left.presheaf.stalk z)ˣ}
include hJ


theorem nu_pull (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {K₁ : Type} [Fintype K₁] {φ₁ : K₁ → (A.left ⟶ A.left)} {ε₁ : K₁ → ℤ}
    (ν : LB.Gen (LB.LinComb L.L φ₁ ε₁)) (hν : ν.IsGen)
    (hF₁ : ∀ {T : Over S} (y : T ⟶ A) (U : Type) [CommGroup U] (h : (T.left ⟶ A.left) → U), ∏ i, h (y.left ≫ φ₁ i) ^ ε₁ i =
      h y.left * (h y⁻¹.left)⁻¹) {a : ℕ} (f : A ⟶ A) [IsMonHom f] {K₀ : Type} [Fintype K₀]
    {φ₀ : K₀ → (A.left ⟶ A.left)} {ε₀ : K₀ → ℤ} (δ : LB.Gen (LB.LinComb L.L φ₀ ε₀)) (hδ : δ.IsGen)
    (hF₀ : ∀ {T : Over S} (y : T ⟶ A) (U : Type) [CommGroup U] (h : (T.left ⟶ A.left) → U), ∏ i, h (y.left ≫ φ₀ i) ^ ε₀ i =
      h y.left ^ k * (h (y ≫ f).left ^ a)⁻¹) : ∃ κ, ∀ y : T' ⟶ A, val ν y.left z J ^ k =
      κ * (val δ y.left z J * (val δ y⁻¹.left z J)⁻¹ * val ν (y ≫ f).left z J ^ a) := by
  have pw : ∀ (n : ℕ) (y : T' ⊗ A ⟶ A) (U : Type) [CommGroup U] (h : ((T' ⊗ A).left ⟶ A.left) → U),
      ∏ i, h (y.left ≫ φ₁ i) ^ ((n : ℤ) * ε₁ i) = (h y.left * (h y⁻¹.left)⁻¹) ^ n := fun n y U _ h => by
    rw [← hF₁ y U h, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => by rw [mul_comm, zpow_mul, zpow_natCast]
  let P : ∀ (n : ℕ) (y : T' ⊗ A ⟶ A), LB.Gen (LB.LinComb L.L (fun i => y.left ≫ φ₁ i) fun i => (n : ℤ) * ε₁ i) :=
    fun n y => ⟨fun j => (LB.pullGen L.L _ _ ν y.left).s j ^ n⟩
  have vP : ∀ n y (r : T'.left ⟶ _), val (P n y) r z J = val ν (r ≫ y.left) z J ^ n := fun n y r =>
    (map_pow _ _ _).trans (congrArg (· ^ n) (val_pull hJ ν y.left r))
  have gP : ∀ n y, (P n y).IsGen := fun n y => isGen_of_gm _ fun w j j' h h' => (map_pow _ _ _).trans
    ((congrArg (· ^ n) (gen_trans (pullGen_isGen _ _ _ _ hν y.left) (𝟙 _) w h h')).trans ((mul_pow _ _ _).trans
      (congrArg₂ (· * ·) (by
        rw [trF, trF, ← Finset.prod_pow]
        exact Finset.prod_congr rfl fun i _ => by rw [mul_comm, zpow_mul, zpow_natCast]) (map_pow _ _ _).symm)))
  have key := fun y => ratio_const hG hA L.isLB (fun U _ h => by
      refine (prod_sum₂ (K := K₀ ⊕ K₀) (K' := K₁) (U := U) _ (prod_sum₂ (K := K₀) (K' := K₀) (U := U) _ (hF₀ (snd T' A) U h)
        (prod_neg _ _ (hF₀ (snd T' A)⁻¹ U h))) (pw a (snd T' A ≫ f) U h)).trans (Eq.trans ?_ (pw k (snd T' A) U h).symm)
      rw [GrpObj.inv_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow]
      module) (gP k (snd T' A)) (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hδ (snd T' A).left)
        (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hδ (snd T' A)⁻¹.left))) (gP a (snd T' A ≫ f))) (𝟙 T') y hJ
  exact ⟨_, fun y => ((vP k _ _).trans (by rw [← Over.comp_left, lift_snd])).symm.trans ((eq_mul_inv_of_mul_eq (key y)).trans
    ((_root_.mul_assoc _ _ _).trans ((mul_comm _ _).trans (congrArg₂ (· * ·) rfl (by
      rw [val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, vP, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left,
        lift_snd, GrpObj.comp_inv, lift_snd, lift_snd_assoc])))))⟩

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
