module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HopfHeightOnePrimitiveEqZeroOfZeroDifferentialStatement

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv.FrobKerPrim

theorem mem_frobKerIdeal_of_cobOne (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p]
    [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H] (b : H)
    (_hb : counit (R := K) b = 0) (hd : dUnit (R := K) b = 0)
    (hc : Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (frobKerIdeal p K H))
      (Ideal.Quotient.mkₐ K (frobKerIdeal p K H)) (cobOne K H b) = 0) :
    b ∈ frobKerIdeal p K H := by
  have hadd {A : Type} [CommRing A] (h : (p : A) = 0) (x y : A) :
      (x + y) ^ p = x ^ p + y ^ p := by
    rw [add_pow_prime_eq (Fact.out : p.Prime), h]; simp
  have hcast (A : Type) [CommRing A] [Algebra K A] : (p : A) = 0 := by
    rw [← map_natCast (algebraMap K A), CharP.cast_eq_zero, map_zero]
  have hmk (x : H) : Ideal.Quotient.mkₐ K (frobKerIdeal p K H) x ^ p =
      algebraMap K _ (counit (R := K) x) ^ p := by
    have hx : x - algebraMap K H (counit (R := K) x) ∈ augIdeal K H := by
      simp [RingHom.mem_ker]
    have h0 : Ideal.Quotient.mkₐ K (frobKerIdeal p K H)
        ((x - algebraMap K H (counit (R := K) x)) ^ p) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal hx)
    have e : x = (x - algebraMap K H (counit (R := K) x)) + algebraMap K H (counit (R := K) x) := by ring
    conv_lhs => rw [e, ← map_pow, hadd (hcast H), map_add, h0, zero_add, map_pow, AlgHom.commutes]
  have hmap (t : H ⊗[K] H) :
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (frobKerIdeal p K H))
        (Ideal.Quotient.mkₐ K (frobKerIdeal p K H)) t ^ p =
      (1 : H ⧸ frobKerIdeal p K H) ⊗ₜ[K] (Ideal.Quotient.mkₐ K (frobKerIdeal p K H)
        (TensorProduct.lid K H (LinearMap.rTensor H (counit (R := K) (A := H)) t)) ^ p) := by
    induction t with
    | add x y hx hy =>
      simp only [map_add (f := _)]
      rw [hadd (hcast _), hadd (hcast _), hx, hy, tmul_add]
    | tmul x y =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_pow, hmk,
        LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul, smul_pow, ← map_pow,
        Algebra.algebraMap_eq_smul_one, smul_tmul]
  haveI : (frobKerIdeal p K H).IsHopfIdeal K := {
    counit_eq_zero x hx := frobKerIdeal_le_augIdeal (Fact.out : p.Prime).ne_zero K H hx
    map_mkQ_comul_eq_zero x hx := by
      have h : frobKerIdeal p K H ≤ RingHom.ker
          ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (frobKerIdeal p K H))
            (Ideal.Quotient.mkₐ K (frobKerIdeal p K H))).comp (comulAlgHom K H)) := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨a, ha, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker, map_pow, AlgHom.comp_apply, hmap,
          comulAlgHom_apply, rTensor_counit_comul, TensorProduct.lid_tmul, one_smul, ← map_pow]
        have : Ideal.Quotient.mkₐ K (frobKerIdeal p K H) (a ^ p) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal ha)
        rw [this, tmul_zero]
      exact h hx
    antipode_mem x hx := by
      have h : frobKerIdeal p K H ≤ (frobKerIdeal p K H).comap (HopfAlgebra.antipodeAlgHom K H) := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨a, ha, rfl⟩
        rw [SetLike.mem_coe, Ideal.mem_comap, map_pow]
        apply pow_mem_frobKerIdeal
        have ha' : counit (R := K) a = 0 := ha
        simp [RingHom.mem_ker, ha']
      exact h hx }
  set J := frobKerIdeal p K H with hJ
  let π : H →ₐc[K] H ⧸ J := Bialgebra.Quotient.mkBialgHom J
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  haveI : IsCocomm K (H ⧸ J) := by
    constructor
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hπ y
    have h1 := pullTwo_comul π x
    simp only [LinearMap.comp_apply]
    rw [← h1]
    simp only [pullbackTwo]
    have h2 := TensorProduct.map_comm (π : H →ₗ[K] H ⧸ J) (π : H →ₗ[K] H ⧸ J) (comul x)
    rw [comm_comul] at h2
    exact h2.symm
  have hpow : ∀ a ∈ augIdeal K (H ⧸ J), a ^ p = 0 := by
    intro a ha
    obtain ⟨x, rfl⟩ := hπ a
    have hx : x ∈ augIdeal K H := ha
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal hx)
  have hc' : cobOne K (H ⧸ J) (π b) = 0 := by
    rw [← pullTwo_cobOne]
    exact hc
  have hd' : dUnit (R := K) (π b) = 0 := by
    rw [← cotMap_d, hd, map_zero]
  have h0 := GlobalTheory.T.hopf_height_one_primitive_eq_zero_of_zero_differential p K (H ⧸ J) hpow (π b) hc' hd'
  exact Ideal.Quotient.eq_zero_iff_mem.1 h0

end GlobalTheory.PDiv.FrobKerPrim
