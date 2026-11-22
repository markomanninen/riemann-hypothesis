module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscBDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TraceFib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AeEvTNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TraceGramDetNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HadamardGram
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormPts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GeneratorNeZeroOfHeight

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem disc_pointwise (hd : d.AxH 𝒜) (h : d.S1) (a b : KTp K d.D d.N) (hab : d.IsPres hd h a b)
    (sg : K →+* ℂ) :
    ∀ᵐ z ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)),
      Real.log ‖d.evT sg 0 (d.tOf z) a‖ - Real.log ‖d.evT sg 0 (d.tOf z) b‖ ≤
        d.del * Real.log d.del + 2 * ∑ k, Real.log (d.supN sg d.wF (d.thp (hd.sel k))) +
          2 * ∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
            -Real.log (d.nrm c d.wF (hd.a4.choose c) P) := by
  classical
  obtain ⟨hb0, habE, m, hm0, hma, hmb⟩ := hab
  have hDe := d.de_ne_zero hd h
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at habE
    exact mul_ne_zero hDe ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb0) habE.symm
  have heW : ∀ c, hd.a4.choose c ∈ 𝒜 c d.wF ∧ hd.a4.choose c ≠ 0 := hd.a4.choose_spec.1
  have hST : ∀ᵐ z ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)),
      ∀ c, (d.ST c sg (d.tOf z)).Finite ∧ (d.ST c sg (d.tOf z)).ncard = d.delc c := by
    have : Countable K := countable_numberField K
    filter_upwards [NPB.ae_gen (D := d.D) (N := d.N) sg] with z hz
    obtain ⟨y, -, hpt⟩ := NPB.exists_gen sg (fun q => d.tOf z q.1 q.2) hz 1 one_ne_zero
    have hy : ∀ i, y (Fin.natAdd (d.N + 1) i) ≠ 0 := by
      intro i h0
      apply hpt (MvPolynomial.X (i.succ, 0)) (MvPolynomial.X_ne_zero _)
      simp [NPB.gpt, h0]
    intro c
    let pt := NPB.gpt (fun q => d.tOf z q.1 q.2) y
    let : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    let : Algebra (KTf K d.D d.N) ℂ := (tauPev sg pt hpt).toAlgebra
    have := d.KT_finiteDimensional hd c
    let e : KTf K d.D d.N ≃+* d.KT c :=
      (d.KTtoS h c).rangeRestrictFieldEquiv.trans (RingEquiv.subfieldCongr (d.KTtoS_fieldRange h c))
    have he : (algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)).comp e.symm.toRingHom =
        (RingEquiv.refl (OmS (Ω c) d.D d.N)).toRingHom.comp (algebraMap (d.KT c) (OmS (Ω c) d.D d.N)) := by
      refine RingHom.ext fun x => ?_
      change d.KTtoS h c (e.symm x) = (x : OmS (Ω c) d.D d.N)
      exact congrArg (fun u : d.KT c => (u : OmS (Ω c) d.D d.N)) (e.apply_symm_apply x)
    have : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
      Module.Finite.of_equiv_equiv e.symm (RingEquiv.refl _) he
    have hrank : Module.finrank (KTf K d.D d.N) (OmS (Ω c) d.D d.N) = d.delc c :=
      (Algebra.finrank_eq_of_equiv_equiv e.symm (RingEquiv.refl _) he).symm
    have : CharZero (KTf K d.D d.N) := inferInstance
    have : Algebra.IsSeparable (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
      Algebra.IsSeparable.of_integral _ _
    let restrict (σ : OmS (Ω c) d.D d.N →ₐ[KTf K d.D d.N] ℂ) :=
      (σ : OmS (Ω c) d.D d.N →+* ℂ).comp (algebraMap (Ω c) (OmS (Ω c) d.D d.N))
    have hcomm (σ : OmS (Ω c) d.D d.N →ₐ[KTf K d.D d.N] ℂ) :
        (σ : OmS (Ω c) d.D d.N →+* ℂ).comp (d.KTtoS h c) = tauPev sg pt hpt :=
      RingHom.ext fun x => σ.commutes x
    have hinj : Function.Injective restrict := fun σ₁ σ₂ hσ =>
      AlgHom.coe_ringHom_injective (d.emb_ext h c sg pt hpt _ _ (hcomm σ₁) (hcomm σ₂) hσ)
    have hrange : Set.range restrict = d.ST c sg (fun i j => pt (i.succ, j)) := by
      ext P
      constructor
      · rintro ⟨σ, rfl⟩
        exact d.emb_mem_ST hd h c sg pt hpt _ (hcomm σ)
      · intro hP
        obtain ⟨σ, hσ, hrestrict⟩ := d.exists_emb hd h c sg pt hpt P hP
        exact ⟨{ σ with commutes' := fun x => RingHom.congr_fun hσ x }, hrestrict⟩
    rw [d.ST_scale c sg (d.tOf z) y hy] at hrange
    refine ⟨hrange ▸ Set.finite_range _, ?_⟩
    rw [← hrange, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, AlgHom.card, hrank]
  filter_upwards [hST, d.de_fibre hd h a b ⟨hb0, habE, m, hm0, hma, hmb⟩ sg,
    d.ae_evT_ne_zero sg a ha0 m hm0 hma, d.ae_evT_ne_zero sg b hb0 m hm0 hmb] with z hz hfib haz hbz
  set e := hd.a4.choose with he
  set t := d.tOf z with ht
  set s : Fin d.del → ℝ := fun k => d.supN sg d.wF (d.thp (hd.sel k)) with hsdef
  have hfin : ∀ c, (d.ST c sg t).Finite := fun c => (hz c).1
  have hcard : ∀ c, (d.ST c sg t).ncard = d.delc c := fun c => (hz c).2
  let _ : ∀ c, Fintype (d.ST c sg t) := fun c => (hfin c).fintype
  let M : (Σ c, d.ST c sg t) → Fin d.del → ℂ := fun r k =>
    (r.2 : Ω r.1 →+* ℂ) (ratio (Ω := Ω r.1) (d.thp (hd.sel k) r.1) (e r.1))
  let ν : (Σ c, d.ST c sg t) → ℝ := fun r => d.nrm r.1 d.wF (e r.1) r.2
  have hR : Fintype.card (Σ c, d.ST c sg t) = d.del := by
    rw [Fintype.card_sigma]
    unfold Data.del
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hcard c, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  have hν : ∀ r, 0 < ν r := fun r => hd.nrm_pos r.1 r.2 (heW r.1).1 (heW r.1).2
  have hM : ∀ r k, ‖M r k‖ * ν r ≤ s k := by
    rintro ⟨c, P, hP⟩ k
    have hth : d.thp (hd.sel k) c ∈ 𝒜 c d.wF := hd.thp_mem _ c
    have hline := eq_ratio_smul_on_line d (hd := hd) hth (heW c).1 (heW c).2
    have h1 : ‖P (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c))‖ * d.nrm c d.wF (e c) P ≤
        d.nrm c d.wF (d.thp (hd.sel k) c) P := by
      by_cases hr : ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c) = 0
      · rw [hr, map_zero, norm_zero, zero_mul]
        rw [hr, zero_smul] at hline
        rw [hline, hd.nrm_zero]
      · have h2 := hd.nrm_smul c P _ (heW c).1 (heW c).2 hr
        rw [← hline] at h2
        rw [h2]
    have hmem : d.thp (hd.sel k) ∈ d.Thp := by
      rw [hd.Thp_span]
      exact Submodule.subset_span ⟨_, rfl⟩
    have h3 : d.nrm c d.wF (d.thp (hd.sel k) c) P ≤ s k :=
      le_ciSup (f := fun p : (Σ c, PT (Ω := Ω c) sg) => d.nrm p.1 d.wF (d.thp (hd.sel k) p.1) p.2)
        (hd.bdd sg d.wF (d.thp (hd.sel k)) (Or.inr (Or.inl ⟨hmem, rfl⟩))) ⟨c, ⟨P, hP.1⟩⟩
    exact h1.trans h3
  have hG : (Matrix.of fun k l : Fin d.del => ∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t),
        P (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c)) *
          P (ratio (Ω := Ω c) (d.thp (hd.sel l) c) (e c))) =
      Matrix.of fun k l => ∑ r, M r k * M r l := by
    ext k l
    simp only [Matrix.of_apply, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]
  have hq : d.evT sg 0 t a / d.evT sg 0 t b = (Matrix.of fun k l : Fin d.del => ∑ r, M r k * M r l).det := by
    rw [hfib hbz, hG]
  set D0 := (Matrix.of fun k l : Fin d.del => ∑ r, M r k * M r l).det with hD0
  have hD0ne : D0 ≠ 0 := by
    rw [← hq]
    exact div_ne_zero haz hbz
  have hlhs : Real.log ‖d.evT sg 0 t a‖ - Real.log ‖d.evT sg 0 t b‖ = Real.log ‖D0‖ := by
    rw [← hq, norm_div, Real.log_div (norm_ne_zero_iff.mpr haz) (norm_ne_zero_iff.mpr hbz)]
  have hH := hadamard_gram hR M ν s hν hM
  have hpos : 0 < ‖D0‖ * ∏ r, ν r ^ 2 :=
    mul_pos (norm_pos_iff.mpr hD0ne) (Finset.prod_pos fun r _ => pow_pos (hν r) 2)
  have hRpos : 0 < (d.del : ℝ) ^ d.del * ∏ k, s k ^ 2 := lt_of_lt_of_le hpos hH
  have hlog := Real.log_le_log hpos hH
  have hs : ∀ k, s k ^ 2 ≠ 0 := fun k =>
    (Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hRpos.ne')) k (Finset.mem_univ _)
  have hdel : (d.del : ℝ) ^ d.del ≠ 0 := left_ne_zero_of_mul hRpos.ne'
  rw [Real.log_mul (norm_ne_zero_iff.mpr hD0ne)
      (Finset.prod_ne_zero_iff.mpr fun r _ => pow_ne_zero 2 (hν r).ne'),
    Real.log_prod (fun r _ => pow_ne_zero 2 (hν r).ne'),
    Real.log_mul hdel (Finset.prod_ne_zero_iff.mpr fun k _ => hs k),
    Real.log_prod (fun k _ => hs k)] at hlog
  simp only [Real.log_pow, Nat.cast_ofNat] at hlog
  have hsumν : ∑ r, Real.log (ν r) = ∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t),
      Real.log (d.nrm c d.wF (e c) P) := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]
  have hsumneg : ∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t), -Real.log (d.nrm c d.wF (e c) P) =
      -∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t), Real.log (d.nrm c d.wF (e c) P) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← finsum_set_coe_eq_finsum_mem, ← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype,
      finsum_eq_sum_of_fintype, Finset.sum_neg_distrib]
  rw [hlhs, hsumneg, ← hsumν]
  have e1 : ∑ r, (2 : ℝ) * Real.log (ν r) = 2 * ∑ r, Real.log (ν r) := by rw [Finset.mul_sum]
  have e2 : ∑ k, (2 : ℝ) * Real.log (s k) = 2 * ∑ k, Real.log (s k) := by rw [Finset.mul_sum]
  rw [e1, e2] at hlog
  linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0
