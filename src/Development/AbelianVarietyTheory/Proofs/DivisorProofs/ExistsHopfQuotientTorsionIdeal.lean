module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHopfIdealKerIdealOfBialgHom

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory.PDiv

theorem exists_hopf_quotient_torsionIdeal :
    ∀ (O : Type) [CommRing O] (B : Type) [CommRing B] [HopfAlgebra O B] [IsCocomm O B] (n : ℕ),
      ∃ (D : Type) (_ : CommRing D) (_ : HopfAlgebra O D) (_ : IsCocomm O D) (π : B →ₐc[O] D),
        Function.Surjective π ∧ RingHom.ker π = torsionIdeal (R := O) (A := B) n := by
  intro O _ B _ _ _ n
  let I := torsionIdeal (R := O) (A := B) n
  have : I.IsHopfIdeal O :=
    isHopfIdeal_kerIdeal_of_bialgHom O B B (mulBy (R := O) (A := B) n)
  let π : B →ₐc[O] B ⧸ I := Bialgebra.Quotient.mkBialgHom _
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have cocomm : IsCocomm O (B ⧸ I) :=
    { comm_comp_comul := LinearMap.ext fun b => by
        obtain ⟨a, rfl⟩ := hπ b
        have h : ∀ t : B ⊗[O] B,
            TensorProduct.comm O (B ⧸ I) (B ⧸ I)
                (TensorProduct.map (π : B →ₗ[O] B ⧸ I) (π : B →ₗ[O] B ⧸ I) t) =
            TensorProduct.map (π : B →ₗ[O] B ⧸ I) (π : B →ₗ[O] B ⧸ I)
              (TensorProduct.comm O B B t) := by
          intro t
          induction t with
          | add x y hx hy => simp only [map_add (f := _), hx, hy]
          | tmul x y => simp
        change TensorProduct.comm O (B ⧸ I) (B ⧸ I) (comul (π a)) = comul (π a)
        rw [← CoalgHomClass.map_comp_comul_apply π a, h, comm_comul] }
  exact ⟨B ⧸ I, inferInstance, inferInstance,
    cocomm, π, hπ,
    Ideal.ext fun _ => Ideal.Quotient.eq_zero_iff_mem⟩

end GlobalTheory.PDiv
