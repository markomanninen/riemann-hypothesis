module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFibreDimQuotientPDivGroupLevel
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing

@[expose] public section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_fibreDim_quotient_pDivGroupLevel :
    ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (k m : ℕ),
      1 ≤ k → ∀ (B : Type) [CommRing B] [HopfAlgebra O B] [IsCocomm O B] [Module.Finite O B]
        [Module.Projective O B] (j : B →ₐc[O] G.A (k + m)) (ρ : G.A (k + m) →ₗ[O] B),
        (∀ b, ρ (j b) = b) → torsionIdeal (R := O) (A := G.A (k + m)) p ≤ kerIdeal j →
        ∀ q : PrimeSpectrum O,
          fibreDim (B ⧸ torsionIdeal (R := O) (A := B) (p ^ m)) q = p ^ (m * G.height) := by
  intro p _ O _ G k m hk B _ _ _ _ _ j ρ hρ hj q
  obtain ⟨r, μ, hr, hker, hμ, hμq⟩ := G.exists_mulPow_fibreRank_eq p O k m
  let jₗ := (j : B →ₐ[O] G.A (k + m)).toLinearMap
  let rjₗ := ((r.comp j) : B →ₐ[O] G.A k).toLinearMap
  let μₗ := (μ : G.A k →ₐ[O] G.A (k + m)).toLinearMap
  let mul := mulBy (R := O) (A := B) (p ^ m)
  let mulₗ := (mul : B →ₐ[O] B).toLinearMap
  have hjq : fibreRank jₗ q = fibreDim B q :=
    (FibreRanks.fibre_ranks O B (G.A (k + m)) (G.A (k + m)) jₗ).1 ρ hρ q
  have hlevel := fibreDim_eq_ker_mul_range j q
  rw [show fibreRank (j : B →ₐ[O] G.A (k + m)).toLinearMap q = _ from hjq, G.fibreDim_eq]
    at hlevel
  have hres := fibreDim_eq_ker_mul_range (r.comp j) q
  rw [G.fibreDim_eq] at hres
  have hle : RingHom.ker r ≤ kerIdeal j := by
    rw [hker]
    exact (torsionIdeal_le_of_dvd (dvd_pow_self p (by omega : k ≠ 0))).trans hj
  let J := kerIdeal (r.comp j)
  let φ : G.A (k + m) →ₐ[O] G.A k ⧸ J := (Ideal.Quotient.mkₐ O J).comp r
  have hφ : Function.Surjective φ := (Ideal.Quotient.mkₐ_surjective O J).comp hr
  have hkerφ : RingHom.ker φ = kerIdeal j := by
    have hcomap : RingHom.ker φ = J.comap (r : G.A (k + m) →ₐ[O] G.A k) := by
      ext a
      simp [φ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    rw [hcomap, show J = Ideal.map (r : G.A (k + m) →ₐ[O] G.A k) (kerIdeal j) from
      kerIdeal_comp r j, Ideal.comap_map_of_surjective (r : G.A (k + m) →ₐ[O] G.A k) hr,
      sup_eq_left]
    exact hle
  let e : (G.A (k + m) ⧸ kerIdeal j) ≃ₗ[O] (G.A k ⧸ J) :=
    ((Ideal.quotientEquivAlgOfEq O hkerφ).symm.trans
      (Ideal.quotientKerAlgEquivOfSurjective hφ)).toLinearEquiv
  rw [← fibreDim_congr e q] at hres
  have hmul := fibreDim_eq_ker_mul_range mul q
  have hlin : jₗ ∘ₗ mulₗ = μₗ ∘ₗ rjₗ := by
    ext b
    change j (mulBy (R := O) (A := B) (p ^ m) b) = μ (r (j b))
    rw [map_mulBy, hμ]
  have hrank : fibreRank mulₗ q = fibreRank rjₗ q := by
    rw [← (FibreRanks.fibre_ranks O B B (G.A (k + m)) mulₗ).2.1 jₗ q hjq, hlin,
      (FibreRanks.fibre_ranks O B (G.A k) (G.A (k + m)) rjₗ).2.1 μₗ q (hμq q)]
  change fibreDim B q = fibreDim (B ⧸ kerIdeal mul) q * fibreRank mulₗ q at hmul
  rw [hrank] at hmul
  change fibreDim (B ⧸ kerIdeal mul) q = _
  have hp : 0 < p ^ (k * G.height) := pow_pos (Fact.out : p.Prime).pos _
  have hpow : p ^ ((k + m) * G.height) = p ^ (m * G.height) * p ^ (k * G.height) := by
    rw [Nat.add_mul, pow_add, mul_comm]
  refine (Nat.eq_of_mul_eq_mul_right hp ?_).symm
  rw [← hpow, hlevel, hmul, hres]
  ring
