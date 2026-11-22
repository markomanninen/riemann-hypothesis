module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective

@[expose] public section

noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory

namespace GlobalTheory.PDivGroup.Test

open PDiv

variable {p : ℕ} {O : Type} [CommRing O]


open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory in
variable {p : ℕ} {O : Type} [CommRing O] in
theorem _root_.GlobalTheory.PDivGroup.Test.mulP_injective (G : _root_.GlobalTheory.PDivGroup p O) (n : ℕ) :
    Function.Injective (G.mulP n) := by
  intro x y hxy
  have hinj := _root_.GlobalTheory.CartierDual.map_injective_of_surjective (G.dual_mulP_surjective n)
  have hx := _root_.GlobalTheory.CartierDual.map_map_bidual (G.mulP n) x
  have hy := _root_.GlobalTheory.CartierDual.map_map_bidual (G.mulP n) y
  rw [hxy, ← hy] at hx
  exact (_root_.GlobalTheory.CartierDual.bidual O (G.A n)).injective (hinj hx)

theorem hodgeTate_values [Fact p.Prime] (hp : ¬ IsUnit (p : O)) :
    (∀ t, hodgeTate (mu p O) t = 0) ∧ hodgeTate (const p O) (constGen p O) ≠ 0 := by
  refine ⟨fun t => Subsingleton.elim _ _, fun h => dlogT_ne_zero p O hp ?_⟩
  rw [hodgeTate_eq_omegaMap, ← dualHom_constHom, show constHom _ (constGen p O) = 𝟙 _ by
    rw [← LinearEquiv.eq_symm_apply, constHom_symm_apply, tateMap_id], dualHom_id,
    Category.id_comp] at h
  have h2 := LinearMap.congr_fun (omegaMap_comp (mu p O).bidual.hom (mu p O).bidual.inv) (dlogT p O)
  rw [Iso.hom_inv_id, omegaMap_id, LinearMap.id_apply, LinearMap.comp_apply] at h2
  rw [h2]
  exact (congrArg _ h).trans (map_zero _)

section Prod

variable (A B : Type) [CommRing A] [CommRing B] [Bialgebra O A] [Bialgebra O B]

def inl : A →ₐc[O] A ⊗[O] B :=
  (Bialgebra.TensorProduct.map (BialgHom.id O A) (Bialgebra.unitBialgHom O B)).comp
    (Bialgebra.TensorProduct.rid O O A).symm.toBialgHom

def inr : B →ₐc[O] A ⊗[O] B :=
  (Bialgebra.TensorProduct.map (Bialgebra.unitBialgHom O A) (BialgHom.id O B)).comp
    (Bialgebra.TensorProduct.lid O B).symm.toBialgHom

variable {A B}

theorem inl_apply (a : A) : inl (O := O) A B a = a ⊗ₜ 1 :=
  congrArg (fun y : B => a ⊗ₜ[O] y) (map_one (Bialgebra.unitBialgHom O B))

theorem inr_apply (b : B) : inr (O := O) A B b = 1 ⊗ₜ b :=
  congrArg (fun y : A => y ⊗ₜ[O] b) (map_one (Bialgebra.unitBialgHom O A))

theorem pts_ext {E : Type} [CommRing E] [Algebra O E] {x y : WithConv (A ⊗[O] B →ₐ[O] E)}
    (h1 : pointsMap E (inl A B) x = pointsMap E (inl A B) y)
    (h2 : pointsMap E (inr A B) x = pointsMap E (inr A B) y) : x = y := by
  refine ofConv_injective (Algebra.TensorProduct.ext' fun a b => ?_)
  have e1 : x.ofConv (inl A B a) = y.ofConv (inl A B a) := DFunLike.congr_fun (congrArg ofConv h1) a
  have e2 : x.ofConv (inr A B b) = y.ofConv (inr A B b) := DFunLike.congr_fun (congrArg ofConv h2) b
  have e : a ⊗ₜ[O] b = inl A B a * inr A B b := by simp [inl_apply, inr_apply]
  rw [e, map_mul, map_mul, e1, e2]

end Prod

@[reducible] def prod (G H : PDivGroup p O) : PDivGroup p O where
  height := G.height + H.height
  A n := G.A n ⊗[O] H.A n
  rank_eq n q := by
    rw [rankAtStalk_tensorProduct, Pi.mul_apply, G.rank_eq, H.rank_eq, mul_add, pow_add]
  res n := Bialgebra.TensorProduct.map (G.res n) (H.res n)
  res_surjective n := TensorProduct.map_surjective (g := (G.res n).toLinearMap) (g' := (H.res n).toLinearMap) (G.res_surjective n) (H.res_surjective n)
  ker_res n := by
    refine le_antisymm (fun a ha => ?_) ?_
    · let π := Ideal.Quotient.mkₐ O
        (torsionIdeal (R := O) (A := G.A (n + 1) ⊗[O] H.A (n + 1)) (p ^ n))
      have h1 := (torsionIdeal_le_ker_iff (p ^ n) π).1
        fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
      obtain ⟨y, hy⟩ := (G.exists_comp_res_iff n (pointsMap _ (inl _ _) (toConv π)).ofConv).2
        (by rw [toConv_ofConv, ← map_pow, h1, map_one])
      obtain ⟨z, hz⟩ := (H.exists_comp_res_iff n (pointsMap _ (inr _ _) (toConv π)).ofConv).2
        (by rw [toConv_ofConv, ← map_pow, h1, map_one])
      have h2 : (Algebra.TensorProduct.lift y z fun _ _ => .all _ _).comp
          (Bialgebra.TensorProduct.map (G.res n) (H.res n) :
            G.A (n + 1) ⊗[O] H.A (n + 1) →ₐ[O] G.A n ⊗[O] H.A n) = π :=
        Algebra.TensorProduct.ext' fun a b => by
          have e1 : y (G.res n a) = π (inl _ _ a) := DFunLike.congr_fun hy a
          have e2 : z (H.res n b) = π (inr _ _ b) := DFunLike.congr_fun hz b
          change y (G.res n a) * z (H.res n b) = _
          rw [e1, e2, ← map_mul, inl_apply, inr_apply]
          simp
      have h3 := (DFunLike.congr_fun h2 a).symm
      rw [AlgHom.comp_apply] at h3
      erw [show Bialgebra.TensorProduct.map (G.res n) (H.res n) a = 0 from ha, map_zero] at h3
      exact Ideal.Quotient.eq_zero_iff_mem.1 h3
    · refine (torsionIdeal_le_ker_iff (p ^ n) (Bialgebra.TensorProduct.map (G.res n) (H.res n) :
          G.A (n + 1) ⊗[O] H.A (n + 1) →ₐ[O] G.A n ⊗[O] H.A n)).2 (pts_ext ?_ ?_)
      · rw [map_pow, map_one]
        refine (G.exists_comp_res_iff n _).1 ⟨(inl (O := O) (G.A n) (H.A n)).toAlgHom, AlgHom.ext fun a => ?_⟩
        change inl _ _ (G.res n a) = Bialgebra.TensorProduct.map (G.res n) (H.res n) (inl _ _ a)
        simp [inl_apply]
      · rw [map_pow, map_one]
        refine (H.exists_comp_res_iff n _).1 ⟨(inr (O := O) (G.A n) (H.A n)).toAlgHom, AlgHom.ext fun a => ?_⟩
        change inr _ _ (H.res n a) = Bialgebra.TensorProduct.map (G.res n) (H.res n) (inr _ _ a)
        simp [inr_apply]

end GlobalTheory.PDivGroup.Test
