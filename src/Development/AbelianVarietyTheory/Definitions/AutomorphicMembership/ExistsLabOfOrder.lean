module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.CyclotomicNorms Polynomial Module

namespace GlobalTheory.WeilDeligne.LabModel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
variable {g : ℕ} [Fact g.Prime]

theorem eq_one_of_cong (h : IsPlaceOver A w) (hw : normV w = g) {l : ℕ} (hc : l.Coprime g)
    {u : Ω} (hu : u ^ l = 1) (h1 : A.valuation (u - 1) < 1) : u = 1 := by
  have hg : g.Prime := Fact.out
  by_contra hne
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [Nat.Coprime, Nat.gcd_zero_left] at hc
    exact hg.ne_one hc
  have hv : A.valuation u ≤ 1 := by
    have := A.valuation.map_add (u - 1) 1
    rw [sub_add_cancel, map_one] at this
    exact this.trans (max_le h1.le le_rfl)
  have hs : ∑ i ∈ Finset.range l, u ^ i = 0 := by
    have e := geom_sum_mul u l
    rw [hu, sub_self] at e
    exact (mul_eq_zero.mp e).resolve_right (sub_ne_zero.mpr hne)
  have hlv : A.valuation (l : Ω) < 1 := by
    have e : (l : Ω) = -∑ i ∈ Finset.range l, (u ^ i - 1) := by
      rw [Finset.sum_sub_distrib, hs]
      simp
    rw [e, Valuation.map_neg]
    exact Valuation.map_sum_lt _ one_ne_zero fun i _ => by
      simpa using GlobalTheory.WeilDeligne.cong_pow hv (by simp) h1 i
  have hgw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hw]
    have : Finite (𝓞 E ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (by
      rw [show Nat.card (𝓞 E ⧸ w.asIdeal) = normV w from rfl, hw]
      exact hg.ne_zero)
    rw [show normV w = Nat.card (𝓞 E ⧸ w.asIdeal) from rfl, ← nsmul_one]
    exact card_nsmul_eq_zero'
  have hlw : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal := by
    intro hl
    obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.mpr hc).map (Int.castRingHom (𝓞 E))
    have h1 : (1 : 𝓞 E) ∈ w.asIdeal := by
      rw [← hab]
      simp only [eq_intCast, Int.cast_natCast]
      exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left a hl) (w.asIdeal.mul_mem_left b hgw)
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have := GlobalTheory.InertiaMovesRoot.val_eq_one_of_notMem h hlw
  have e : algebraMap E Ω ((((l : ℕ) : 𝓞 E)) : E) = (l : Ω) := by simp
  rw [e] at this
  exact (ne_of_lt hlv) this

end GlobalTheory.WeilDeligne.LabModel
