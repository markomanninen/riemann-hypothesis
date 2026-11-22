module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdFNonnegOfIsInteger
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDeterminantKernelOpenAndFactor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TildeCharacterOnUnitary

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.ChiDet

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem detId_stdL (N : ℕ) (M : Submodule (𝓞 H.E) (Fin N → H.E)) : Th.detId H (Th.stdL H N) M = detSub M := by
  classical
  unfold Th.detId detSub
  congr 1
  ext z
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨fun j i => A i j, fun j => ?_, (Matrix.det_transpose A).symm⟩
    have h1 : (Pi.single j 1 : Fin N → H.E) ∈ Th.stdL H N := fun k _ => by
      by_cases e : k = j
      · subst e
        rw [Pi.single_eq_same]
        exact Submodule.one_le.1 le_rfl
      · rw [Pi.single_eq_of_ne e]
        exact Submodule.zero_mem _
    have h2 := hA _ h1
    rw [Matrix.mulVec_single_one] at h2
    exact h2
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(Matrix.of x).transpose, fun v hv => ?_, (Matrix.det_transpose _).symm⟩
    choose b hb using fun i => Submodule.mem_one.1 (hv i trivial)
    have e : (Matrix.of x).transpose.mulVec v = ∑ i, b i • x i := by
      funext j
      rw [Finset.sum_apply]
      show ∑ i, x i j * v i = ∑ i, b i • x i j
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, hb, mul_comm]
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hx i)

theorem ordSub_detSub_stdL (N : ℕ) (w : HeightOneSpectrum (𝓞 H.E)) : ordSub w (detSub (Th.stdL H N)) = 0 := by
  rw [← detId_stdL, detId_std, Submodule.one_eq_span]
  have h := ordSub_span_singleton w (1 : H.Eˣ)
  rw [Units.val_one] at h
  rw [h]
  simp [ordF]

theorem tildeD_eq_chiId : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), IsChiPsi H χ → ∀ (N : ℕ) (M : Submodule (𝓞 H.E) (Fin N → H.E)), Submodule.IsLattice H.E M → ∀ x : DtT H, (QuotientGroup.mk x : DtT H ⧸ UOT H) = relDetT H N (Th.stdL H N) M → ((tildeD H χ x : ℂˣ) : ℂ) = chiId χ (Th.detId H (Th.stdL H N) M) := by
  intro R H χ hχ N M hM x hx
  have hK : KD H ≤ (χ.1.comp (finPartI H.E)).ker :=
    (KerDet.kernel_open_and_factor R H).2.2.2 χ hχ.triv (fun v y hy _ => hχ.unr v y hy) fun v _ => hχ.unr v
  have hU := (ChiLaws.chi_laws R H χ hχ).1
  have hfin : {w : HeightOneSpectrum (𝓞 H.E) | ordSub w (detSub M) ≠ 0}.Finite := by
    by_cases h : ∃ k : H.Eˣ, (k : H.E) ∈ detSub M
    · obtain ⟨k, hk⟩ := h
      exact DetOrd.ordSub_finite (DetOrd.isFractional_detSub M hM.fg) k hk
    · have hz : ∀ w, ordSub w (detSub M) = 0 := by
        intro w
        unfold ordSub
        have he : {n : ℤ | ∃ k : H.Eˣ, (k : H.E) ∈ detSub M ∧ ordF w k = n} = ∅ := by
          ext n
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨k, hk, _⟩
          exact h ⟨k, hk⟩
        rw [he]
        simp
      simp [hz]
  unfold relDetT at hx
  have h1 := hU _ (QuotientGroup.eq.1 hx)
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  rw [h1, tildeD_mk H hK, detId_stdL]
  unfold chiId
  congr 1
  simp only [ordSub_detSub_stdL, sub_zero]
  have h2 : Function.HasFiniteMulSupport fun w : HeightOneSpectrum (𝓞 H.E) =>
      localIdele H.E w (atFin w (unif w)) ^ (ordSub w (detSub M)).toNat := by
    refine hfin.subset fun w hw h0 => hw ?_
    simp only [h0, Int.toNat_zero, pow_zero]
  refine ((χ.1.comp (finPartI H.E)).map_finprod h2).trans (finprod_congr fun w => ?_)
  rw [map_pow, MonoidHom.comp_apply, KerDet.finPartI_localIdele]
  rfl

end GlobalTheory.Mem.ChiDet
