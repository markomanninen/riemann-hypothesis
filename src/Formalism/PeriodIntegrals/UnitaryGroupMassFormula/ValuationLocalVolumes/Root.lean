module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.GramAugT
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfThreeX

@[expose] public section

noncomputable section

namespace PI.OmVf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmVd IsLocalRing
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem exists_integral_root_of_quadratic (β γ ν : Fv F v) (hβ : β ∈ v.adicCompletionIntegers F) (hγ : γ ∈ v.adicCompletionIntegers F)
    (hγm : Valued.v γ < 1) (hν : ν ∈ v.adicCompletionIntegers F) :
    ∃ s ∈ v.adicCompletionIntegers F, β + (1 - γ * β) * s - γ * (1 - γ * β) * ν * s ^ 2 = 0 := by
  set b : v.adicCompletionIntegers F := ⟨β, hβ⟩
  set g : v.adicCompletionIntegers F := ⟨γ, hγ⟩
  set m : v.adicCompletionIntegers F := ⟨ν, hν⟩
  have hg : g ∈ maximalIdeal (v.adicCompletionIntegers F) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨w, hw⟩
    have h1 : ((w⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) * g = 1 := by
      rw [← hw]; simp
    have h2 : ((((w⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : Fv F v)) * γ = 1 := by
      have := congrArg (fun x : v.adicCompletionIntegers F => (x : Fv F v)) h1
      simpa using this
    have h3 : Valued.v ((((w⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : Fv F v)) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers (K := F) (v := v)).1 (Subtype.property _)
    have h4 := congrArg Valued.v h2
    rw [map_mul, map_one] at h4
    have : Valued.v ((((w⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : Fv F v)) * Valued.v γ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left' h3) hγm
    rw [h4] at this
    exact lt_irrefl _ this
  have hu : IsUnit (1 - g * b) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ((maximalIdeal _).mul_mem_right b hg)
  open scoped WithZero Topology in
  open HeightOneSpectrum Filter in
  have hcomplete : IsAdicComplete (maximalIdeal (v.adicCompletionIntegers F)) (v.adicCompletionIntegers F) := by
    let R := 𝓞 F
    let L := F
    let w := v
    let Ow := v.adicCompletionIntegers F
    let Lw := v.adicCompletion F
    have lt_one_iff_le (g : ℤᵐ⁰) : g < 1 ↔ g ≤ WithZero.exp (-1 : ℤ) := by
      induction g using WithZero.expRecOn with
      | zero => simp
      | exp a => rw [← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]; omega

    have v_algebraMap (l : L) : Valued.v (algebraMap L Lw l) = w.valuation L l :=
      valuedAdicCompletion_eq_valuation' w l

    have exists_unif : ∃ π : Ow, Valued.v (π : Lw) = WithZero.exp (-1 : ℤ) := by
      obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer L
      have h : Valued.v (algebraMap L Lw π) = WithZero.exp (-1 : ℤ) := by
        rw [v_algebraMap, hπ]
      refine ⟨⟨algebraMap L Lw π, ?_⟩, h⟩
      rw [mem_adicCompletionIntegers, h]
      exact ((lt_one_iff_le _).2 le_rfl).le

    have mem_max_iff (x : Ow) :
        x ∈ IsLocalRing.maximalIdeal Ow ↔ Valued.v (x : Lw) < 1 := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        adicCompletionIntegers.isUnit_iff_valued_eq_one]
      have : Valued.v (x : Lw) ≤ 1 := (mem_adicCompletionIntegers R L w).1 x.2
      exact ⟨fun h => lt_of_le_of_ne this h, fun h => h.ne⟩

    have max_eq_span {π : Ow} (hπ : Valued.v (π : Lw) = WithZero.exp (-1 : ℤ)) :
        IsLocalRing.maximalIdeal Ow = Ideal.span {π} := by
      ext x
      rw [mem_max_iff, Ideal.mem_span_singleton, lt_one_iff_le, ← hπ]
      exact (adicCompletionIntegers.integers L w).le_iff_dvd

    have mem_max_pow_iff {π : Ow} (hπ : Valued.v (π : Lw) = WithZero.exp (-1 : ℤ)) (x : Ow) (n : ℕ) :
        x ∈ IsLocalRing.maximalIdeal Ow ^ n ↔ Valued.v (x : Lw) ≤ Valued.v (π : Lw) ^ n := by
      rw [max_eq_span hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      have := (adicCompletionIntegers.integers L w).le_iff_dvd (x := x) (y := π ^ n)
      rw [map_pow, map_pow] at this
      exact this.symm

    obtain ⟨π, hπ⟩ := exists_unif
    have hπ1 : ‖(π : Lw)‖ < 1 := by
      rw [Valued.toNormedField.norm_lt_one_iff]
      exact (lt_one_iff_le _).2 hπ.le
    have hπ0 : (π : Lw) ≠ 0 := by
      intro h
      rw [h, map_zero] at hπ
      exact WithZero.exp_ne_zero hπ.symm
    have hr0 : 0 < ‖(π : Lw)‖ := norm_pos_iff.mpr hπ0
    have key : ∀ (n : ℕ) (x y : Ow),
        x ≡ y [SMOD ((IsLocalRing.maximalIdeal Ow) ^ n • ⊤ : Submodule Ow Ow)] ↔
          ‖(x : Lw) - y‖ ≤ ‖(π : Lw)‖ ^ n := by
      intro n x y
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_max_pow_iff hπ,
        ← map_pow, ← Valued.toNormedField.norm_le_iff]
      simp only [norm_pow]
      rfl
    refine { haus' := ?_, prec' := ?_ }
    · intro x hx
      have h : ∀ n : ℕ, ‖(x : Lw)‖ ≤ ‖(π : Lw)‖ ^ n := fun n => by
        simpa using (key n x 0).mp (hx n)
      have hx0 : ‖(x : Lw)‖ ≤ 0 :=
        ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hπ1) h
      exact Subtype.ext (norm_le_zero_iff.mp hx0)
    · intro f hf
      have hc : ∀ n : ℕ, dist (f n : Lw) (f (n + 1)) ≤ 1 * ‖(π : Lw)‖ ^ n := fun n => by
        rw [dist_eq_norm, one_mul]
        exact (key n _ _).mp (hf n.le_succ)
      obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric _ 1 hπ1 hc)
      have hl1 : ‖l‖ ≤ 1 := le_of_tendsto' hl.norm (fun n =>
        Valued.toNormedField.norm_le_one_iff.mpr (f n).2)
      refine ⟨⟨l, Valued.toNormedField.norm_le_one_iff.mp hl1⟩, fun n => ?_⟩
      rw [key]
      have ht : Tendsto (fun m => ‖(f n : Lw) - f m‖) atTop (𝓝 ‖(f n : Lw) - l‖) :=
        (tendsto_const_nhds.sub hl).norm
      exact le_of_tendsto ht (eventually_atTop.mpr ⟨n, fun m hm => (key n _ _).mp (hf hm)⟩)

  letI := hcomplete
  haveI : HenselianLocalRing (v.adicCompletionIntegers F) := ⟨fun f hf a h₁ h₂ => HenselianRing.is_henselian f hf a h₁ (h₂.map _)⟩
  obtain ⟨s, hs⟩ := PI.OmVf.quad_root (-(g * (1 - g * b) * m)) (1 - g * b) b
    (neg_mem ((maximalIdeal _).mul_mem_right m ((maximalIdeal _).mul_mem_right _ hg))) hu
  refine ⟨s, s.property, ?_⟩
  have := congrArg (fun x : v.adicCompletionIntegers F => (x : Fv F v)) hs
  simp only [b, g, m] at this
  push_cast at this
  linear_combination this
end PI.OmVf
