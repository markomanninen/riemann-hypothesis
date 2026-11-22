module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderTensorPadicIsAzumayaAlmostAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsScalarTowerCenAlgebra

@[expose] public section

open scoped TensorProduct
open GlobalTheory.LKInvGood
open GlobalTheory.LocAzumaya Module in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localOrderTensorPadic_isAzumaya_almost_all : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B]
    (Λ : Subring B) (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ),
    Module.Finite ℤ Λ → (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ;
      IsAzumaya (cenOrder ℓ F) (locOrder ℓ Λ) := by
  intro F B _ _ _ _ _ _ _ _ _ Λ hΛ hfin hspan
  classical
  have hlocalBasis : ∀ (ι : Type) [Fintype ι] (e : Module.Basis ι F B), (∀ i, e i ∈ Λ) →
      ∃ D : ℕ, 0 < D ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ D →
        letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ;
        ∃ f : Module.Basis ι (cenOrder ℓ F) (locOrder ℓ Λ),
          (∀ i, (f i : ℚ_[ℓ] ⊗[ℚ] B) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i) ∧
          ∀ (y : locOrder ℓ Λ) (b : B), (y : ℚ_[ℓ] ⊗[ℚ] B) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b →
            ∀ k, ((f.repr y k : cenOrder ℓ F) : ℚ_[ℓ] ⊗[ℚ] F) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr b k := by
    intro ι _ e he
    obtain ⟨D, hD, hDint⟩ := exists_den_coords F B Λ hfin ι e
    refine ⟨D, hD, fun ℓ _ hℓ => ?_⟩
    let _ := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ
    have hco : ∀ x ∈ Λ, ∀ k, (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr x k ∈ cenOrder ℓ F :=
      fun x hx k => GlobalTheory.SepModel.tmul_mem_cenOrder ℓ hℓ (hDint x hx k)
    have hv : ∀ i, (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i ∈ locOrder ℓ Λ := fun i => Algebra.subset_adjoin ⟨_, he i, rfl⟩
    let v : ι → locOrder ℓ Λ := fun i => ⟨_, hv i⟩
    have hsmul : ∀ (c : cenOrder ℓ F) (y : locOrder ℓ Λ),
        ((c • y : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) = cenMap ℓ F B c * y := fun c y => rfl
    have hsum : ∀ c : ι → cenOrder ℓ F, ((∑ i, c i • v i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) =
        ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i) := by
      intro c
      rw [AddSubmonoidClass.coe_finsetSum]
      simp only [hsmul, v]
    have hcoef : ∀ (c : ι → cenOrder ℓ F) (b : B),
        ((∑ i, c i • v i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b →
        ∀ k, ((c k : cenOrder ℓ F) : ℚ_[ℓ] ⊗[ℚ] F) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr b k := by
      intro c b h k
      obtain ⟨π, hπ1, hπ2⟩ := exists_coordProj ℓ F B e k
      have h' := congrArg π h
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hsum, map_sum, hπ1] at h'
      simp only [hπ2, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h'
      exact h'
    have hli : LinearIndependent (cenOrder ℓ F) v := by
      rw [Fintype.linearIndependent_iff]
      intro c hc k
      have h0 : ((∑ i, c i • v i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (0 : B) := by
        rw [hc, TensorProduct.tmul_zero]; rfl
      have := hcoef c 0 h0 k
      apply Subtype.ext
      simpa using this
    have hsp : ⊤ ≤ Submodule.span (cenOrder ℓ F) (Set.range v) := by
      rintro y -
      obtain ⟨c, hc, hy⟩ := exists_coords_of_mem_locOrder ℓ F B Λ ι e he hco y y.2
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun i => ⟨c i, hc i⟩, Subtype.ext ?_⟩
      rw [hsum, hy]
    let f := Basis.mk hli hsp
    have hfv : ∀ i, f i = v i := fun i => Basis.mk_apply hli hsp i
    refine ⟨f, fun i => by rw [hfv], fun y b hy k => ?_⟩
    apply hcoef (fun i => f.repr y i) b _ k
    have hs := f.sum_repr y
    simp only [hfv] at hs
    rw [hs, hy]
  obtain ⟨e, he⟩ := exists_basis_mem (F := F) Λ hspan
  have hδ : IsUnit (structMat e).det :=
    (bijective_iff_isUnit_det e).1 (GroundTheory.Brauer.mulLeftRight_bijective F B)
  obtain ⟨m, hm, hmint⟩ := GlobalTheory.SepModel.exists_nat_integral ({((structMat e).det)⁻¹} : Finset F)
  obtain ⟨D, hD, hbasis⟩ := hlocalBasis _ e he
  refine ⟨D * m, by positivity, fun ℓ _ hℓ => ?_⟩
  let _ := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ
  obtain ⟨f, hf1, hf2⟩ := hbasis ℓ (fun h => hℓ (Dvd.dvd.mul_right h _))
  have hinv : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((structMat e).det)⁻¹ ∈ cenOrder ℓ F :=
    GlobalTheory.SepModel.tmul_mem_cenOrder ℓ (fun h => hℓ (Dvd.dvd.mul_left h _))
      (hmint _ (Finset.mem_singleton_self _))
  have hent : (cenOrder ℓ F).val.toRingHom.mapMatrix (structMat f) =
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℚ_[ℓ]) (B := F)).toRingHom.mapMatrix
        (structMat e) := by
    ext ⟨k, l⟩ ⟨i, j⟩
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Subalgebra.coe_val, Algebra.TensorProduct.includeRight_apply, structMat_apply]
    apply hf2
    simp only [Subalgebra.coe_mul, hf1, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have hdet : (((structMat f).det : cenOrder ℓ F) : ℚ_[ℓ] ⊗[ℚ] F) =
      (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (structMat e).det := by
    have h1 := RingHom.map_det (cenOrder ℓ F).val.toRingHom (structMat f)
    have h2 := RingHom.map_det
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℚ_[ℓ]) (B := F)).toRingHom (structMat e)
    rw [hent, ← h2] at h1
    simpa using h1
  have hunit : IsUnit (structMat f).det := by
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
    rw [Subalgebra.coe_mul, hdet, Subalgebra.coe_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      mul_inv_cancel₀ hδ.ne_zero, Algebra.TensorProduct.one_def]
  have : Nontrivial B := inferInstance
  have : FaithfulSMul (cenOrder ℓ F) (locOrder ℓ Λ) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have h : cenMap ℓ F B a = cenMap ℓ F B b :=
      congrArg (fun x : locOrder ℓ Λ => (x : ℚ_[ℓ] ⊗[ℚ] B)) hab
    exact Subtype.ext (cenMap_injective ℓ F B h)
  have := Module.Projective.of_basis f
  have := Module.Finite.of_basis f
  exact ⟨(bijective_iff_isUnit_det f).2 hunit⟩
