module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PSurjS
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.OneSubEvTInvInt

@[expose] public section

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain PI.UnitaryGroupMassFormula.UJClassFin
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section TL

variable {F : Type} [Field F] [NumberField F]

theorem algebraMap_int_intAf (t : 𝓞 F) : algebraMap F (Af F) (algebraMap (𝓞 F) F t) ∈ intAf F := by
  intro w
  show (algebraMap F (Af F) (algebraMap (𝓞 F) F t)) w ∈ w.adicCompletionIntegers F
  rw [af_alg_apply, HeightOneSpectrum.mem_adicCompletionIntegers]
  have e1 : algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F t) =
      ((algebraMap (𝓞 F) F t : F) : w.adicCompletion F) := rfl
  rw [e1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_le_one w t

theorem finElt (m : 𝓞 F) (hm : m ≠ 0) : {w : HeightOneSpectrum (𝓞 F) | m ∈ w.asIdeal}.Finite := by
  have hI : Ideal.span {m} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hm
  apply (Ideal.finite_factors hI).subset
  intro w hw
  show w.asIdeal ∣ Ideal.span {m}
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hw

theorem evT_compl (X : Set (HeightOneSpectrum (𝓞 F))) : 1 - evT Xᶜ = evT X := by
  apply af_ext
  intro u
  rw [af_sub_apply, af_one_apply, evT_apply, evT_apply]
  by_cases h : u ∈ X
  · rw [if_neg (fun h' => h' h), if_pos h, sub_zero]
  · rw [if_pos (show u ∈ Xᶜ from h), if_neg h, sub_self]

theorem evT_inv_int (X : Set (HeightOneSpectrum (𝓞 F))) (t : 𝓞 F) (ht : ∀ u ∈ X, t ∉ u.asIdeal) :
    evT X * algebraMap F (Af F) ((algebraMap (𝓞 F) F t)⁻¹) ∈ intAf F := by
  rw [← evT_compl]
  exact one_sub_evT_inv_int Xᶜ t (fun u hu => ht u (by simpa using hu))

theorem evT_mul_of_subset {X Y : Set (HeightOneSpectrum (𝓞 F))} (hXY : X ⊆ Y) : evT X * evT Y = evT X := by
  apply af_ext
  intro u
  rw [af_mul_apply, evT_apply, evT_apply]
  by_cases h : u ∈ X
  · rw [if_pos h, if_pos (hXY h), mul_one]
  · rw [if_neg h, zero_mul]

theorem evT_split {B S : Set (HeightOneSpectrum (𝓞 F))} (hBS : B ⊆ S) : evT S = evT B + evT (S \ B) := by
  apply af_ext
  intro u
  rw [af_add_apply, evT_apply, evT_apply, evT_apply]
  by_cases h1 : u ∈ B
  · rw [if_pos (hBS h1), if_pos h1, if_neg (fun h => h.2 h1), add_zero]
  · by_cases h2 : u ∈ S
    · rw [if_pos h2, if_neg h1, if_pos ⟨h2, h1⟩, zero_add]
    · rw [if_neg h2, if_neg h1, if_neg (fun h => h2 h.1), add_zero]

theorem t_lemma (v : HeightOneSpectrum (𝓞 F)) (m : 𝓞 F) (hm : m ≠ 0) :
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧
      (1 - evT {v}) * algebraMap F (Af F) (algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F m) ∈ intAf F := by
  classical
  have hn : ∀ w : HeightOneSpectrum (𝓞 F), ∃ n : ℕ, m ∉ w.asIdeal ^ n := by
    intro w
    by_contra h
    push_neg at h
    have hmem : m ∈ ⨅ i, w.asIdeal ^ i := (Submodule.mem_iInf _).2 h
    rw [Ideal.iInf_pow_eq_bot_of_isDomain w.asIdeal w.isPrime.ne_top, Ideal.mem_bot] at hmem
    exact hm hmem
  choose n hn using hn
  let s : Finset (HeightOneSpectrum (𝓞 F)) := insert v (finElt m hm).toFinset
  obtain ⟨t, ht⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s) (fun w => w.asIdeal)
    (fun w => if w = v then 1 else n w) (fun w _ => w.prime)
    (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
    (fun w => if (w : HeightOneSpectrum (𝓞 F)) = v then 1 else 0)
  refine ⟨t, ?_, ?_⟩
  · intro htv
    have h1 : t - 1 ∈ v.asIdeal := by simpa using ht v (Finset.mem_insert_self _ _)
    have h2 : (1 : 𝓞 F) ∈ v.asIdeal := by
      have := v.asIdeal.sub_mem htv h1
      simpa using this
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)
  · intro w
    show ((1 - evT {v}) * algebraMap F (Af F) (algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F m)) w ∈
      w.adicCompletionIntegers F
    rw [af_mul_apply, af_sub_apply, evT_apply, af_one_apply, af_alg_apply]
    split_ifs with hw
    · rw [sub_self, zero_mul]
      exact zero_mem _
    · rw [sub_zero, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers]
      have e1 : algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F m) =
          ((algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F m : F) : w.adicCompletion F) := rfl
      rw [e1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_div₀,
        HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
      have hw' : w ≠ v := fun h => hw (by rw [h]; exact Set.mem_singleton v)
      have hpos : 0 < w.intValuation m := zero_lt_iff.2 (HeightOneSpectrum.intValuation_ne_zero w m hm)
      by_cases hmw : m ∈ w.asIdeal
      · have hws : w ∈ s := Finset.mem_insert_of_mem ((Set.Finite.mem_toFinset _).2 hmw)
        have h1 := ht w hws
        simp only [if_neg hw', sub_zero] at h1
        have hle := (HeightOneSpectrum.intValuation_le_pow_iff_mem w t (n w)).2 h1
        have hnot : ¬ w.intValuation m ≤ WithZero.exp (-((n w : ℕ) : ℤ)) :=
          fun h => hn w ((HeightOneSpectrum.intValuation_le_pow_iff_mem w m (n w)).1 h)
        have hlt := lt_of_le_of_lt hle (not_le.1 hnot)
        exact (div_le_one₀ hpos).2 hlt.le
      · rw [(HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl w m).2 hmw, div_one]
        exact HeightOneSpectrum.intValuation_le_one w t

end TL

section FL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] {M : ℕ}

theorem tmul_one_smul_Fsmul (a : Af F) (c : F) (Y : Fin M → Af F ⊗[F] E) :
    (a ⊗ₜ[F] (1 : E)) • (c • Y) = ((a * algebraMap F (Af F) c) ⊗ₜ[F] (1 : E)) • Y := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_smul_comm, show a * algebraMap F (Af F) c = c • a by rw [Algebra.smul_def, mul_comm],
    ← TensorProduct.smul_tmul', smul_mul_assoc]

theorem tmul_one_smul_smul (a a' : Af F) (Y : Fin M → Af F ⊗[F] E) :
    (a ⊗ₜ[F] (1 : E)) • ((a' ⊗ₜ[F] (1 : E)) • Y) = ((a * a') ⊗ₜ[F] (1 : E)) • Y := by
  rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem crd_iff (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) (s : 𝓞 F) (w : V) :
    algebraMap (𝓞 F) (𝓞 E) s • w ∈ L0 ↔ (algebraMap (𝓞 F) F s) • b.equivFun w ∈ crdOf b L0 := by
  rw [mem_iff_crdOf b L0, equivFun_osmul, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply (𝓞 F) F E, algebraMap_smul]

end FL

end PI.UnitaryGroupMassFormula.UJClassMass

end
