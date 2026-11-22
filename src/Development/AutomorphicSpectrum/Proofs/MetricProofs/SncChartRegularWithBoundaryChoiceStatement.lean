module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartRegularWithBoundaryChoice
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime

@[expose] public section

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_chart_regular_with_boundary_choice : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ) (p : (k : K) → ι k) (x : SncRes.Pts P) (r : Fin e → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (Jf : Finset (Fin e)) (σ : Fin e → Option (Fin (SncRes.rc P D))), IsMultiHomogIdeal P → IsMultiHomogIdeal D → x ∈ SncRes.src P p → (∀ h ∈ (SncRes.ideal P p), eval (SncRes.coord P p x) h = 0) → IsRegularLocalRing (locRing (SncRes.ideal P p) (SncRes.coord P p x)) → ringKrullDim (locRing (SncRes.ideal P p) (SncRes.coord P p x)) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing (SncRes.ideal P p) (SncRes.coord P p x)) (r l)) = Ideal.map (algebraMap _ (locRing (SncRes.ideal P p) (SncRes.coord P p x))) (ptIdeal (SncRes.coord P p x)) → (∀ l, σ l = none ↔ l ∉ Jf) → (∀ l k, σ l = some k → SncRes.ideal (SncRes.compIdeal P D k) p = SncRes.Par.chPrime (SncRes.ideal P p) (SncRes.coord P p x) (r l)) → (∀ k, (∀ g ∈ SncRes.compIdeal P D k, eval (SncRes.rep x) g = 0) → ∃ l ∈ Jf, σ l = some k) → ∃ O : Set (SncRes.Pts P), IsOpen O ∧ x ∈ O ∧ O ⊆ SncRes.src P p ∧ ∀ k, SncRes.comp P D k ∩ O = {x' ∈ O | ∃ l, σ l = some k ∧ eval (SncRes.coord P p x') (r l) = 0} := by
  intro K _ ι _ P D e p x r Jf σ hP hD hx _ _ _ _ _ hch hout
  classical
  have zero_iff {Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hQ : IsMultiHomogIdeal Q)
      (y : SncRes.Pts P) (hy : y ∈ SncRes.src P p) :
      (∀ f ∈ Q, eval (SncRes.rep y) f = 0) ↔
        ∀ h ∈ SncRes.ideal Q p, eval (SncRes.coord P p y) h = 0 := by
    have hchart := mem_conePts_iff_chartIdeal hQ p (SncRes.rep y) hy
    constructor
    · intro h
      exact renPt_zero _ _ (hchart.1 ⟨(SncRes.rep_mem y).1, h⟩)
    · intro h
      have hyQ : SncRes.rep y ∈ conePts Q := hchart.2 fun f hf => by
        rw [← eval_renC]
        exact h _ (Ideal.mem_map_of_mem _ hf)
      exact hyQ.2
  have norm_ne (y : SncRes.Pts P) (k : K) :
      ((∑ i, ‖SncRes.rep y ⟨k, i⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (SncRes.Top.normSq_pos ((SncRes.rep_mem y).1 k)).ne'
  have mem_src_iff (y : SncRes.Pts P) :
      y ∈ SncRes.src P p ↔ ∀ k, y.1 ⟨k, (p k, p k)⟩ ≠ 0 := by
    refine forall_congr' fun k => ?_
    rw [← SncRes.proj_rep y]
    simp only [SncRes.proj, ne_eq, div_eq_zero_iff, norm_ne, or_false, mul_eq_zero,
      map_eq_zero, or_self]
  have hopen : IsOpen (SncRes.src P p) := by
    have heq : SncRes.src P p = ⋂ k, {y : SncRes.Pts P | y.1 ⟨k, (p k, p k)⟩ ≠ 0} := by
      ext y
      simp [mem_src_iff]
    rw [heq]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_ne_fun ((continuous_apply _).comp continuous_subtype_val) continuous_const
  have hcoord : ContinuousOn (SncRes.coord P p) (SncRes.src P p) := by
    refine continuousOn_iff_continuous_domRestrict.2 (continuous_pi fun j => ?_)
    let q := (Fintype.equivFin (Σ k, ι k)).symm j
    have hratio (y : SncRes.src P p) :
        SncRes.coord P p y.1 j = y.1.1 ⟨q.1, (q.2, p q.1)⟩ / y.1.1 ⟨q.1, (p q.1, p q.1)⟩ := by
      have hstar : starRingEnd ℂ (SncRes.rep y.1 ⟨q.1, p q.1⟩) ≠ 0 := by
        simpa using y.2 q.1
      change affCoord p (SncRes.rep y.1) q = _
      rw [← SncRes.proj_rep y.1]
      simp only [SncRes.proj, affCoord]
      rw [div_div_div_cancel_right₀ (norm_ne y.1 q.1), mul_div_mul_right _ _ hstar]
    have hv (a : Σ k, ι k × ι k) : Continuous fun y : SncRes.src P p => y.1.1 a :=
      (continuous_apply a).comp (continuous_subtype_val.comp continuous_subtype_val)
    change Continuous (fun y : SncRes.src P p => SncRes.coord P p y.1 j)
    simp only [hratio]
    exact (hv ⟨q.1, (q.2, p q.1)⟩).div (hv ⟨q.1, (p q.1, p q.1)⟩)
      (fun y => (mem_src_iff y.1).1 y.2 q.1)
  have hQ (k) : IsMultiHomogIdeal (SncRes.compIdeal P D k) :=
    MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup K ι P D hP hD _ (SncRes.compIdeal_mem D k)
  choose s hst hsw using fun l =>
    SncRes.NearComp.exists_den_chPrime (SncRes.ideal P p) (SncRes.coord P p x) (r l)
  have hg : ∀ k, ∃ g, eval (SncRes.coord P p x) g ≠ 0 ∧
      ((∃ l, σ l = some k) ∨ g ∈ SncRes.ideal (SncRes.compIdeal P D k) p) := by
    intro k
    by_cases hk : ∃ l, σ l = some k
    · exact ⟨1, by simp, Or.inl hk⟩
    · have hn : ¬ ∀ h ∈ SncRes.ideal (SncRes.compIdeal P D k) p,
          eval (SncRes.coord P p x) h = 0 := fun h => by
        obtain ⟨l, -, hl⟩ := hout k ((zero_iff (hQ k) x hx).2 h)
        exact hk ⟨l, hl⟩
      push Not at hn
      obtain ⟨g, hg, hgt⟩ := hn
      exact ⟨g, hgt, Or.inr hg⟩
  choose g hgt hgk using hg
  let F := (∏ l, s l) * ∏ k, g k
  have hFw : ∀ w, eval w F ≠ 0 ↔ (∀ l, eval w (s l) ≠ 0) ∧ ∀ k, eval w (g k) ≠ 0 := by
    intro w
    simp only [F, map_mul, map_prod, ne_eq, mul_eq_zero, not_or, Finset.prod_eq_zero_iff,
      Finset.mem_univ, true_and, not_exists]
  refine ⟨SncRes.src P p ∩ SncRes.coord P p ⁻¹' {w | eval w F ≠ 0}, ?_,
    ⟨hx, (hFw _).2 ⟨hst, hgt⟩⟩, Set.inter_subset_left, fun k => ?_⟩
  · exact hcoord.isOpen_inter_preimage hopen
      (isOpen_ne_fun (MvPolynomial.continuous_eval F) continuous_const)
  · ext y
    constructor
    · rintro ⟨hc, ho⟩
      refine ⟨ho, ?_⟩
      have hz := (zero_iff (hQ k) y ho.1).1 hc
      rcases hgk k with ⟨l, hl⟩ | hk
      · refine ⟨l, hl, hz _ ?_⟩
        rw [hch l k hl]
        exact Ideal.mem_comap.2 (Ideal.subset_span rfl)
      · exact absurd (hz _ hk) (((hFw _).1 ho.2).2 k)
    · rintro ⟨ho, l, hl, hr⟩
      refine ⟨(zero_iff (hQ k) y ho.1).2 ?_, ho⟩
      rw [hch l k hl]
      exact hsw l _ ((zero_iff hP y ho.1).1 (SncRes.rep_mem y).2)
        (((hFw _).1 ho.2).1 l) hr
