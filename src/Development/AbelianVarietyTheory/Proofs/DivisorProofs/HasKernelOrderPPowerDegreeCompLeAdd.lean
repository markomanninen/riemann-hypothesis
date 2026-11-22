module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHopfIdealKerIdealOfBialgHom

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory

namespace PDiv

theorem finrank_quot_kerIdeal_comp_le {k A B C : Type} [Field k] [CommRing A] [CommRing B]
    [CommRing C] [HopfAlgebra k A] [HopfAlgebra k B] [HopfAlgebra k C] [Module.Finite k A]
    [Module.Finite k B] (ψ : B →ₐc[k] A) (φ : C →ₐc[k] B) :
    Module.finrank k (A ⧸ kerIdeal (ψ.comp φ)) ≤
      Module.finrank k (A ⧸ kerIdeal ψ) * Module.finrank k (B ⧸ kerIdeal φ) := by
  have hHopf (X Y : Type) [CommRing X] [CommRing Y] [HopfAlgebra k X]
      [HopfAlgebra k Y] (f : Y →ₐc[k] X) : (kerIdeal f).IsHopfIdeal k := by
    refine {
    counit_eq_zero := by
      intro x hx
      exact (kerIdeal_le_ker_iff f (counitAlgHom k X)).2 (fun c => by simp) hx
    map_mkQ_comul_eq_zero := by
      intro x hx
      have h0 := (kerIdeal_le_ker_iff f (Ideal.Quotient.mkₐ k (kerIdeal f))).1
        fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
      have h : kerIdeal f ≤ RingHom.ker
          ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal f))
            (Ideal.Quotient.mkₐ k (kerIdeal f))).comp (comulAlgHom k X)) := by
        refine (kerIdeal_le_ker_iff f _).2 fun c => ?_
        have key : ∀ t : Y ⊗[k] Y, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal f))
            (Ideal.Quotient.mkₐ k (kerIdeal f)) (pullbackTwo f t) =
            algebraMap k _ (counit (R := k)
              (TensorProduct.lid k Y (LinearMap.rTensor Y (counit (R := k) (A := Y)) t))) := by
          intro t
          induction t with
          | add x y hx hy => simp only [map_add (f := _), hx, hy]
          | tmul x y =>
            rw [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul,
              TensorProduct.lid_tmul, map_smul]
            erw [h0, h0]
            simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, smul_tmul',
              smul_smul, mul_comm]
        rw [AlgHom.comp_apply, comulAlgHom_apply, ← pullTwo_comul, key, rTensor_counit_comul,
          TensorProduct.lid_tmul, one_smul]
      exact h hx
    antipode_mem := by
      intro x hx
      have h : kerIdeal f ≤ (kerIdeal f).comap (HopfAlgebra.antipodeAlgHom k X) := by
        refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
        have ha' : counit (R := k) a = 0 := ha
        change HopfAlgebra.antipode k (f a) ∈ kerIdeal f
        rw [← bialgHom_map_antipode]
        exact Ideal.mem_map_of_mem (f : Y →ₐ[k] X) (by simp [RingHom.mem_ker, ha'])
      exact h hx
    }
  haveI := hHopf A C (ψ.comp φ)
  haveI := hHopf B C φ
  let πA : A →ₐc[k] A ⧸ kerIdeal (ψ.comp φ) := Bialgebra.Quotient.mkBialgHom (kerIdeal (ψ.comp φ))
  let πB : B →ₐc[k] B ⧸ kerIdeal φ := Bialgebra.Quotient.mkBialgHom (kerIdeal φ)
  have hπA : Function.Surjective πA := Ideal.Quotient.mk_surjective
  have hπB : Function.Surjective πB := Ideal.Quotient.mk_surjective
  have hA : ∀ c, πA (ψ (φ c)) = algebraMap k _ (counit c) :=
    (kerIdeal_le_ker_iff (ψ.comp φ) (πA : A →ₐ[k] A ⧸ kerIdeal (ψ.comp φ))).1
      fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  have h1 : kerIdeal φ ≤ RingHom.ker (πA.comp ψ : B →ₐ[k] A ⧸ kerIdeal (ψ.comp φ)) :=
    (kerIdeal_le_ker_iff φ _).2 fun c => hA c
  let m' : (B ⧸ kerIdeal φ) →ₐc[k] A ⧸ kerIdeal (ψ.comp φ) :=
    liftSurj πB hπB (πA.comp ψ) fun b hb => h1 (Ideal.Quotient.eq_zero_iff_mem.1 hb)
  have hm' : ∀ b, m' (πB b) = πA (ψ b) := fun b =>
    liftSurj_apply πB hπB (πA.comp ψ) (fun b hb => h1 (Ideal.Quotient.eq_zero_iff_mem.1 hb)) b
  let q : A →ₐ[k] (A ⧸ kerIdeal (ψ.comp φ)) ⧸ kerIdeal m' :=
    (Ideal.Quotient.mkₐ k (kerIdeal m')).comp (πA : A →ₐ[k] A ⧸ kerIdeal (ψ.comp φ))
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective.comp hπA
  have h0 := (kerIdeal_le_ker_iff m' (Ideal.Quotient.mkₐ k (kerIdeal m'))).1
    fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  have h4 : kerIdeal ψ ≤ RingHom.ker q := (kerIdeal_le_ker_iff ψ q).2 fun b => by
    change Ideal.Quotient.mkₐ k (kerIdeal m') (πA (ψ b)) = _
    rw [← hm', h0, CoalgHomClass.counit_comp_apply]
  let q'' : (A ⧸ kerIdeal ψ) →ₐ[k] (A ⧸ kerIdeal (ψ.comp φ)) ⧸ kerIdeal m' :=
    Ideal.Quotient.liftₐ (kerIdeal ψ) q h4
  have hq'' : Function.Surjective q''.toLinearMap := fun x => by
    obtain ⟨a, rfl⟩ := hq x
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  rw [finrank_eq_ker_mul_range k _ _ m']
  exact Nat.mul_le_mul (LinearMap.finrank_le_finrank_of_surjective hq'')
    (LinearMap.finrank_range_le _)

end PDiv

namespace Dieu

theorem hasLogDeg_comp_le : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K) (a b c : ℕ),
    HasLogDeg f a → HasLogDeg g b → HasLogDeg (f ≫ g) c → c ≤ a + b := by
  intro p _ k _ _ G H K f g a b c ⟨N₁, h₁⟩ ⟨N₂, h₂⟩ ⟨N₃, h₃⟩
  let n := max N₁ (max N₂ N₃)
  have e₁ := h₁ n (le_max_left _ _)
  have e₂ := h₂ n (le_trans (le_max_left _ _) (le_max_right _ _))
  have e₃ := h₃ n (le_trans (le_max_right _ _) (le_max_right _ _))
  have hle := finrank_quot_kerIdeal_comp_le (f.app n) (g.app n)
  rw [← comp_app, e₃, e₁, e₂, ← pow_add] at hle
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 hle

end Dieu

end GlobalTheory
