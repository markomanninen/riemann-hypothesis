module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHopfQuotientTorsionIdealStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFibreDimQuotientPDivGroupLevelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveRankAtStalkOfConstFibreDimStatement

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory.HTPair

theorem exists_quotPDivGroup : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsLocalRing O] (G : PDivGroup p O) (τ : QuotTower G), ∃ (H : PDivGroup p O)
    (q : ∀ m, τ.B m →ₐc[O] H.A m), (∀ m, Function.Surjective (q m)) ∧
    (∀ m, RingHom.ker (q m) = torsionIdeal (R := O) (A := τ.B m) (p ^ m)) ∧
    ∀ m b, H.res m (q (m + 1) b) = q m (τ.r m b) := by
  intro p _ O _ _ _ G τ
  have existsHopfQuotient :
      ∀ (O : Type) [CommRing O] (B : Type) [CommRing B] [HopfAlgebra O B] [IsCocomm O B] (n : ℕ),
        ∃ (D : Type) (_ : CommRing D) (_ : HopfAlgebra O D) (_ : IsCocomm O D) (π : B →ₐc[O] D),
          Function.Surjective π ∧ RingHom.ker π = torsionIdeal (R := O) (A := B) n := by
    intro O _ B _ _ _ n
    let f : B →ₐc[O] B := mulBy (R := O) (A := B) n
    let I := kerIdeal f
    let q : B →ₐ[O] B ⧸ I := Ideal.Quotient.mkₐ O I
    have hI : I.IsHopfIdeal O := by
      refine { toIsCoideal := ?_, antipode_mem := ?_ }
      · refine { counit_eq_zero := ?_, map_mkQ_comul_eq_zero := ?_ }
        · intro x hx
          exact (kerIdeal_le_ker_iff f (Bialgebra.counitAlgHom O B)).2 (fun c => by simp) hx
        · intro x hx
          have hqf : ∀ c : B, q (f c) = algebraMap O (B ⧸ I) (counit (R := O) c) :=
            (kerIdeal_le_ker_iff f q).1 fun _ hc => Ideal.Quotient.eq_zero_iff_mem.2 hc
          have hcomp : q.toLinearMap ∘ₗ (f : B →ₗ[O] B) =
              Algebra.linearMap O (B ⧸ I) ∘ₗ counit := LinearMap.ext hqf
          let Φ := (Algebra.TensorProduct.map q q).comp (Bialgebra.comulAlgHom O B)
          have hΦ : I ≤ RingHom.ker Φ := by
            refine Ideal.map_le_iff_le_comap.2 fun c hc => ?_
            have hc' : counit (R := O) c = 0 := hc
            change TensorProduct.map q.toLinearMap q.toLinearMap (comul (f c)) = 0
            rw [← CoalgHomClass.map_comp_comul_apply, ← LinearMap.comp_apply,
              ← TensorProduct.map_comp, hcomp]
            have hsplit : TensorProduct.map (Algebra.linearMap O (B ⧸ I) ∘ₗ counit)
                (Algebra.linearMap O (B ⧸ I) ∘ₗ counit) =
                TensorProduct.map (Algebra.linearMap O (B ⧸ I))
                  (Algebra.linearMap O (B ⧸ I) ∘ₗ counit) ∘ₗ
                  LinearMap.rTensor B (counit (R := O) (A := B)) := by
              rw [LinearMap.rTensor, ← TensorProduct.map_comp, LinearMap.comp_id]
            rw [hsplit, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul, TensorProduct.map_tmul]
            simp [hc']
          exact hΦ hx
      · have hle : I ≤ I.comap (HopfAlgebra.antipodeAlgHom O B) := by
          refine Ideal.map_le_iff_le_comap.2 fun c hc => ?_
          have hc' : counit (R := O) c = 0 := hc
          change HopfAlgebra.antipode O (f c) ∈ I
          rw [← GlobalTheory.bialgHom_map_antipode]
          exact Ideal.mem_map_of_mem (f : B →ₐ[O] B) (by simp [RingHom.mem_ker, hc'])
        exact fun _ hx => hle hx
    let π : B →ₐc[O] B ⧸ I := Bialgebra.Quotient.mkBialgHom I
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
  have hex := fun m => existsHopfQuotient O (τ.B m) (p ^ m)
  choose D iR iH iC q hq hk using hex
  letI := iR
  letI := iH
  letI := iC
  have hB1 : ∀ m (x : PrimeSpectrum O),
      fibreDim (τ.B m ⧸ torsionIdeal (R := O) (A := τ.B m) (p ^ m)) x = p ^ (m * G.height) := by
    intro m x
    have h := GlobalTheory.T.torsion_fibreDim_quotient_pDivGroupLevel p O G 1 m le_rfl (τ.B m)
    rw [show 1 + m = m + 1 from Nat.add_comm 1 m] at h
    exact h (τ.j m) (τ.ρ m) (τ.ρ_j m) (τ.tors_le m) x
  have hB2 : ∀ m (x : PrimeSpectrum O),
      fibreDim (τ.B (m + 1) ⧸ torsionIdeal (R := O) (A := τ.B (m + 1)) (p ^ m)) x = p ^ (m * G.height) := by
    intro m x
    have h := GlobalTheory.T.torsion_fibreDim_quotient_pDivGroupLevel p O G 2 m (by norm_num) (τ.B (m + 1))
    rw [show 2 + m = m + 1 + 1 by omega] at h
    exact h (τ.j (m + 1)) (τ.ρ (m + 1)) (τ.ρ_j (m + 1)) (τ.tors_le (m + 1)) x
  haveI hfin : ∀ m, Module.Finite O (D m) := fun m =>
    Module.Finite.of_surjective (q m : τ.B m →ₗ[O] D m) (hq m)
  have hD : ∀ m (x : PrimeSpectrum O), fibreDim (D m) x = p ^ (m * G.height) := by
    intro m x
    have hk' : RingHom.ker (q m : τ.B m →ₐ[O] D m) = torsionIdeal (R := O) (A := τ.B m) (p ^ m) := hk m
    have e := ((Ideal.quotientEquivAlgOfEq O hk').symm.trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := (q m : τ.B m →ₐ[O] D m)) (hq m))).toLinearEquiv
    rw [← hB1 m x]
    exact (fibreDim_congr e x).symm
  have hPR := fun m => GlobalTheory.T.projective_rankAtStalk_of_const_fibreDim O (D m) (p ^ (m * G.height)) (hD m)
  haveI hproj : ∀ m, Module.Projective O (D m) := fun m => (hPR m).1
  have hle : ∀ m, RingHom.ker (q (m + 1)) ≤ RingHom.ker ((q m).comp (τ.r m)) := by
    intro m b hb
    rw [hk] at hb
    have h1 : τ.r m b ∈ torsionIdeal (R := O) (A := τ.B m) (p ^ (m + 1)) := by
      rw [← map_torsionIdeal (τ.r_surjective m)]
      exact Ideal.mem_map_of_mem (τ.r m : τ.B (m + 1) →ₐ[O] τ.B m) hb
    have h2 : τ.r m b ∈ RingHom.ker (q m) := by
      rw [hk]
      exact torsionIdeal_le_of_dvd (pow_dvd_pow p (Nat.le_succ m)) h1
    rw [RingHom.mem_ker] at h2 ⊢
    exact h2
  let res := fun m => liftSurj (q (m + 1)) (hq (m + 1)) ((q m).comp (τ.r m)) (hle m)
  have hres : ∀ m b, res m (q (m + 1) b) = q m (τ.r m b) := fun m b => liftSurj_apply ..
  have hres_surj : ∀ m, Function.Surjective (res m) := by
    intro m d
    obtain ⟨c, rfl⟩ := hq m d
    obtain ⟨b, rfl⟩ := τ.r_surjective m c
    exact ⟨_, hres m b⟩
  have hker : ∀ m, RingHom.ker (res m) = torsionIdeal (R := O) (A := D (m + 1)) (p ^ m) := by
    intro m
    refine ker_eq_of_fibreDim_eq (res m : D (m + 1) →ₐ[O] D m) (hres_surj m) _ ?_ fun x => ?_
    · rw [← map_torsionIdeal (hq (m + 1))]
      refine Ideal.map_le_iff_le_comap.2 fun b hb => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change res m (q (m + 1) b) = 0
      rw [hres, ← RingHom.mem_ker, hk, ← map_torsionIdeal (τ.r_surjective m)]
      exact Ideal.mem_map_of_mem (τ.r m : τ.B (m + 1) →ₐ[O] τ.B m) hb
    · let φ : τ.B (m + 1) →ₐ[O] D (m + 1) ⧸ torsionIdeal (R := O) (A := D (m + 1)) (p ^ m) :=
        (Ideal.Quotient.mkₐ O _).comp (q (m + 1) : τ.B (m + 1) →ₐ[O] D (m + 1))
      have hφ : Function.Surjective φ :=
        (Ideal.Quotient.mkₐ_surjective O _).comp (hq (m + 1))
      have hkφ : RingHom.ker φ = torsionIdeal (R := O) (A := τ.B (m + 1)) (p ^ m) := by
        ext b
        rw [RingHom.mem_ker]
        change Ideal.Quotient.mk _ (q (m + 1) b) = 0 ↔ _
        rw [Ideal.Quotient.eq_zero_iff_mem, ← map_torsionIdeal (hq (m + 1))]
        constructor
        · intro hb
          obtain ⟨c, hc, e⟩ := (Ideal.mem_map_iff_of_surjective
            (q (m + 1) : τ.B (m + 1) →ₐ[O] D (m + 1)) (hq (m + 1))).1 hb
          have h3 : b - c ∈ RingHom.ker (q (m + 1)) := by
            rw [RingHom.mem_ker, map_sub, sub_eq_zero]
            exact e.symm
          rw [hk] at h3
          have h4 := torsionIdeal_le_of_dvd (R := O) (A := τ.B (m + 1))
            (pow_dvd_pow p (Nat.le_succ m)) h3
          simpa using Ideal.add_mem _ h4 hc
        · intro hb
          exact Ideal.mem_map_of_mem (q (m + 1) : τ.B (m + 1) →ₐ[O] D (m + 1)) hb
      have e := ((Ideal.quotientEquivAlgOfEq O hkφ).symm.trans
        (Ideal.quotientKerAlgEquivOfSurjective hφ)).toLinearEquiv
      rw [hD, ← hB2 m x]
      exact (fibreDim_congr e x).symm
  let H : PDivGroup p O :=
    { height := G.height
      A := D
      commRing := iR
      hopf := iH
      cocomm := iC
      finite := hfin
      projective := hproj
      rank_eq := fun m x => (hPR m).2 x
      res := res
      res_surjective := hres_surj
      ker_res := hker }
  exact ⟨H, q, hq, hk, hres⟩

end GlobalTheory.HTPair
