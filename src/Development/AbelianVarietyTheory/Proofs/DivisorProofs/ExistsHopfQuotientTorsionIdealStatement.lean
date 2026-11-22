module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHopfQuotientTorsionIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing

@[expose] public section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hopf_quotient_ker_eq_torsionIdeal :
    ∀ (O : Type) [CommRing O] (B : Type) [CommRing B] [HopfAlgebra O B] [IsCocomm O B] (n : ℕ),
      ∃ (D : Type) (_ : CommRing D) (_ : HopfAlgebra O D) (_ : IsCocomm O D) (π : B →ₐc[O] D),
        Function.Surjective π ∧ RingHom.ker π = torsionIdeal (R := O) (A := B) n := by
  intro O _ B _ _ _ n
  let I := torsionIdeal (R := O) (A := B) n
  have : I.IsHopfIdeal O :=
    isHopfIdeal_kerIdeal_of_bialgHom O B B (mulBy (R := O) (A := B) n)
  let π : B →ₐc[O] B ⧸ I := Bialgebra.Quotient.mkBialgHom I
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have cocomm : IsCocomm O (B ⧸ I) := by
    constructor
    ext b
    obtain ⟨a, rfl⟩ := hπ b
    change TensorProduct.comm O (B ⧸ I) (B ⧸ I) (comul (π a)) = comul (π a)
    rw [← CoalgHomClass.map_comp_comul_apply π a, ← TensorProduct.map_comm, comm_comul]
  exact ⟨B ⧸ I, inferInstance, inferInstance, cocomm, π, hπ,
    Ideal.ext fun _ => Ideal.Quotient.eq_zero_iff_mem⟩
