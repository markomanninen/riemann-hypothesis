module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHopfIdealKerIdealOfBialgHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCocommOfSurjective

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDiv.FrobKerInter

theorem isHopfIdeal_sup {k A : Type} [CommRing k] [CommRing A] [HopfAlgebra k A]
    (I J : Ideal A) [I.IsHopfIdeal k] [J.IsHopfIdeal k] : (I ⊔ J).IsHopfIdeal k := by
  refine Ideal.IsHopfIdeal.mk (toIsCoideal := ⟨?_, ?_⟩) ?_
  · intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    have h1 := Submodule.IsCoideal.counit_eq_zero (I := I.restrictScalars k) hy
    have h2 := Submodule.IsCoideal.counit_eq_zero (I := J.restrictScalars k) hz
    rw [map_add (f := _), h1, h2, add_zero]
  · intro x hx
    set K := (I ⊔ J).restrictScalars k
    have key : ∀ (L : Ideal A) [L.IsHopfIdeal k], L ≤ I ⊔ J → ∀ y ∈ L,
        TensorProduct.map K.mkQ K.mkQ (comul (R := k) y) = 0 := by
      intro L _ hL y hy
      have hle : L.restrictScalars k ≤ K := fun a ha => hL ha
      have e : K.mkQ = (Submodule.mapQ (L.restrictScalars k) K LinearMap.id hle) ∘ₗ
          (L.restrictScalars k).mkQ := by
        rw [Submodule.mapQ_mkQ, LinearMap.comp_id]
      rw [e, TensorProduct.map_comp, LinearMap.comp_apply,
        Submodule.IsCoideal.map_mkQ_comul_eq_zero (I := L.restrictScalars k) hy, map_zero]
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _), map_add (f := _), key I le_sup_left y hy, key J le_sup_right z hz, add_zero]
  · intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (Ideal.IsHopfIdeal.antipode_mem (R := k) hy)
      (Ideal.IsHopfIdeal.antipode_mem (R := k) hz)

theorem exists_quotient_kerIdeal_sup_frobKerIdeal : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H), ∃ (C : Type) (_ : CommRing C) (_ : HopfAlgebra k C) (_ : IsCocomm k C) (_ : Module.Finite k C) (π : G.A 1 →ₐc[k] C), Function.Surjective π ∧ RingHom.ker π = kerIdeal (q.app 1) ⊔ frobKerIdeal p k (G.A 1) ∧ (∀ a ∈ augIdeal k C, a ^ p = 0) ∧ frobKerIdeal p k (G.A 1) ≤ augIdeal k (G.A 1) ^ 2 := by
  intro p hp k _ _ G H q
  have : (kerIdeal (q.app 1)).IsHopfIdeal k := isHopfIdeal_kerIdeal_of_bialgHom k _ _ (q.app 1)
  have : (frobKerIdeal p k (G.A 1)).IsHopfIdeal k := by
    let J := frobKerIdeal p k (G.A 1)
    let f := Ideal.Quotient.mkₐ k J
    refine Ideal.IsHopfIdeal.mk (toIsCoideal := ⟨?_, ?_⟩) ?_
    · exact frobKerIdeal_le_augIdeal hp.out.ne_zero k (G.A 1)
    · intro x hx
      have h : J ≤ RingHom.ker
          ((Algebra.TensorProduct.map f f).comp (comulAlgHom k (G.A 1))) := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨a, ha, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker, map_pow, AlgHom.comp_apply,
          FrobKerOrder.map_pow_eq, comulAlgHom_apply, rTensor_counit_comul,
          TensorProduct.lid_tmul, one_smul, ← map_pow]
        have hpow : f (a ^ p) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal ha)
        rw [hpow, tmul_zero]
      exact h hx
    · intro x hx
      have h : J ≤ J.comap (HopfAlgebra.antipodeAlgHom k (G.A 1)) := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨a, ha, rfl⟩
        rw [SetLike.mem_coe, Ideal.mem_comap, map_pow]
        apply pow_mem_frobKerIdeal
        have ha' : counit (R := k) a = 0 := ha
        simp [RingHom.mem_ker, ha']
      exact h hx
  set I := kerIdeal (q.app 1) ⊔ frobKerIdeal p k (G.A 1) with hI
  have : I.IsHopfIdeal k := isHopfIdeal_sup _ _
  let π : G.A 1 →ₐc[k] G.A 1 ⧸ I := Bialgebra.Quotient.mkBialgHom I
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have : Module.Finite k (G.A 1) := G.finite 1
  refine ⟨G.A 1 ⧸ I, inferInstance, inferInstance, KerGrp.isCocomm_of_surjective π hπ,
    Module.Finite.of_surjective (π : G.A 1 →ₗ[k] G.A 1 ⧸ I) hπ, π, hπ,
    Ideal.ext fun _ => Ideal.Quotient.eq_zero_iff_mem, ?_, FrobKerOrder.le_sq p k (G.A 1)⟩
  intro a ha
  obtain ⟨b, rfl⟩ := hπ a
  have hb : b ∈ augIdeal k (G.A 1) := ha
  change Ideal.Quotient.mk I b ^ p = 0
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sup_right (pow_mem_frobKerIdeal hb)

end GlobalTheory.PDiv.FrobKerInter
