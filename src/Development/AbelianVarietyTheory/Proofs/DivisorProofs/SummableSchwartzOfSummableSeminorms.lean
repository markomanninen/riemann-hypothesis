module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace

@[expose] public section

open MeasureTheory Filter Topology

namespace GlobalTheory.ConvSeries

theorem seminorm_finset_sum_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Seminorm ℂ (SchwartzMap E ℂ)) (u : Finset ℕ) (t : ℕ → SchwartzMap E ℂ) :
    p (∑ j ∈ u, t j) ≤ ∑ j ∈ u, p (t j) := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert a u ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (map_add_le_add p _ _).trans (by gcongr)

theorem summable_of_summable_seminorm (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : ℕ → SchwartzMap E ℂ)
    (h : ∀ k n, Summable (fun j => SchwartzMap.seminorm ℂ k n (t j))) : Summable t := by
  classical
  have iteratedFDeriv_sub' (f g : (SchwartzMap E ℂ)) (n : ℕ) (x : E) :
      iteratedFDeriv ℝ n (⇑(f - g)) x = iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n g x := by
    have hf : ContDiff ℝ n f := f.smooth n
    have hg : ContDiff ℝ n g := g.smooth n
    rw [show (⇑(f - g) : E → ℂ) = ⇑f - ⇑g from rfl]
    exact iteratedFDeriv_sub_apply hf.contDiffAt hg.contDiffAt
  
  have cauchy_seminorm {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (k n : ℕ) {ε : ℝ} (hε : 0 < ε) :
      ∃ N, ∀ a ≥ N, ∀ b ≥ N, SchwartzMap.seminorm ℝ k n (u a - u b) < ε := by
    rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero, tendsto_comap_iff] at hu
    have h := ((schwartz_withSeminorms ℝ E ℂ).tendsto_nhds _ 0).1 hu (k, n) ε hε
    obtain ⟨⟨N₁, N₂⟩, hN⟩ := eventually_atTop.1 h
    refine ⟨max N₁ N₂, fun a ha b hb => ?_⟩
    have := hN (b, a) (Prod.mk_le_mk.2 ⟨le_of_max_le_left hb, le_of_max_le_right ha⟩)
    simpa [schwartzSeminormFamily] using this
  
  let limD (u : ℕ → (SchwartzMap E ℂ)) (n : ℕ) (x : E) :
      ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ :=
    limUnder atTop fun j => iteratedFDeriv ℝ n (u j) x
  
  have tendsto_limD {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (n : ℕ) (x : E) :
      Tendsto (fun j => iteratedFDeriv ℝ n (u j) x) atTop (𝓝 (limD u n x)) := by
    refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := cauchy_seminorm hu 0 n hε
    refine ⟨N, fun a ha b hb => ?_⟩
    rw [dist_eq_norm, ← iteratedFDeriv_sub']
    have := SchwartzMap.le_seminorm ℝ 0 n (u a - u b) x
    simp only [pow_zero, one_mul] at this
    exact this.trans_lt (hN a ha b hb)
  
  have key {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (k n : ℕ) {ε : ℝ} (hε : 0 < ε) :
      ∃ N, ∀ j ≥ N, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u j) x - limD u n x‖ ≤ ε := by
    obtain ⟨N, hN⟩ := cauchy_seminorm hu k n hε
    refine ⟨N, fun j hj x => ?_⟩
    have ht : Tendsto (fun b => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u j) x - iteratedFDeriv ℝ n (u b) x‖)
        atTop (𝓝 (‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u j) x - limD u n x‖)) :=
      ((tendsto_const_nhds.sub (tendsto_limD hu n x)).norm).const_mul _
    refine le_of_tendsto ht (eventually_atTop.2 ⟨N, fun b hb => ?_⟩)
    rw [← iteratedFDeriv_sub']
    exact (SchwartzMap.le_seminorm ℝ k n (u j - u b) x).trans (hN j hj b hb).le
  
  have tendstoUniformly_limD {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (n : ℕ) :
      TendstoUniformly (fun j => iteratedFDeriv ℝ n (u j)) (limD u n) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := key hu 0 n (half_pos hε)
    refine eventually_atTop.2 ⟨N, fun j hj x => ?_⟩
    have := hN j hj x
    rw [pow_zero, one_mul] at this
    rw [dist_eq_norm, norm_sub_rev]
    linarith
  
  have continuous_limD {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (n : ℕ) :
      Continuous (limD u n) :=
    (tendstoUniformly_limD hu n).continuous (Eventually.of_forall (f := atTop) fun j =>
      ((u j).smooth ⊤).continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).frequently
  
  have hasFDerivAt_limD {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (m : ℕ) (x : E) :
      HasFDerivAt (limD u m) ((limD u (m + 1) x).curryLeft) x := by
    refine hasFDerivAt_of_tendstoUniformly (f := fun j => iteratedFDeriv ℝ m (u j))
      (f' := fun j y => fderiv ℝ (iteratedFDeriv ℝ m (⇑(u j))) y)
      (g' := fun y => (limD u (m + 1) y).curryLeft) ?_ ?_ (fun y => tendsto_limD hu m y) x
    · exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) ℂ).isometry.uniformContinuous.comp_tendstoUniformly
        (tendstoUniformly_limD hu (m + 1))
    · intro j y
      exact ((((u j).smooth ⊤).differentiable_iteratedFDeriv
        (by exact_mod_cast WithTop.coe_lt_top (m : ℕ))) y).hasFDerivAt
  
  have hasFTaylorSeries {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) :
      HasFTaylorSeriesUpTo ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (limD u 0 x).curry0)
        (fun x => (fun m => limD u m x : FormalMultilinearSeries ℝ E ℂ)) := by
    exact { zero_eq := fun _ => rfl
            fderiv := fun m _ x => hasFDerivAt_limD hu m x
            cont := fun m _ => continuous_limD hu m }
  
  let limMap (u : ℕ → (SchwartzMap E ℂ)) (hu : CauchySeq u) : (SchwartzMap E ℂ) := by
    refine { toFun := fun x => (limD u 0 x).curry0
             smooth' := (hasFTaylorSeries hu).contDiff
             decay' := ?_ }
    intro k n
    obtain ⟨N, hN⟩ := key hu k n one_pos
    refine ⟨SchwartzMap.seminorm ℝ k n (u N) + 1, fun x => ?_⟩
    rw [← (hasFTaylorSeries hu).eq_iteratedFDeriv (m := n) (by exact_mod_cast le_top) x]
    have h1 := hN N le_rfl x
    have h2 := SchwartzMap.le_seminorm ℝ k n (u N) x
    have h3 : ‖limD u n x‖ ≤ ‖iteratedFDeriv ℝ n (u N) x‖ + ‖iteratedFDeriv ℝ n (u N) x - limD u n x‖ := by
      have := norm_sub_le (iteratedFDeriv ℝ n (u N) x) (iteratedFDeriv ℝ n (u N) x - limD u n x)
      simpa using this
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ ‖x‖ ^ k)
    change ‖x‖ ^ k * ‖limD u n x‖ ≤ _
    rw [mul_add] at h4
    linarith

  have iteratedFDeriv_limMap {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (n : ℕ) (x : E) :
      iteratedFDeriv ℝ n (limMap u hu) x = limD u n x :=
    ((hasFTaylorSeries hu).eq_iteratedFDeriv (m := n) (by exact_mod_cast le_top) x).symm
  
  have tendsto_limMap {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) :
      Tendsto u atTop (𝓝 (limMap u hu)) := by
    rw [(schwartz_withSeminorms ℝ E ℂ).tendsto_nhds]
    rintro ⟨k, n⟩ ε hε
    obtain ⟨N, hN⟩ := key hu k n (half_pos hε)
    refine eventually_atTop.2 ⟨N, fun j hj => ?_⟩
    refine lt_of_le_of_lt ?_ (half_lt_self hε)
    refine SchwartzMap.seminorm_le_bound ℝ k n _ (half_pos hε).le fun x => ?_
    rw [iteratedFDeriv_sub', iteratedFDeriv_limMap hu]
    exact hN j hj x
  
  haveI : CompleteSpace (SchwartzMap E ℂ) := by
    haveI : (uniformity (SchwartzMap E ℂ)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
    exact UniformSpace.complete_of_cauchySeq_tendsto fun u hu => ⟨limMap u hu, tendsto_limMap hu⟩
  rw [summable_iff_vanishing]
  intro U hU
  obtain ⟨s, r, hr, hsub⟩ := (schwartz_withSeminorms ℂ E ℂ).mem_nhds_iff 0 U |>.1 hU
  have hr' : 0 < r / 2 := half_pos hr
  have hS : ∀ i : ℕ × ℕ, ∃ S : Finset ℕ, ∀ u : Finset ℕ, Disjoint u S →
      ∑ j ∈ u, SchwartzMap.seminorm ℂ i.1 i.2 (t j) ∈ Set.Iio (r / 2) :=
    fun i => summable_iff_vanishing.1 (h i.1 i.2) _ (Iio_mem_nhds (by simpa using hr'))
  choose S hS using hS
  refine ⟨s.biUnion S, fun u hu => hsub ?_⟩
  rw [Seminorm.mem_ball_zero]
  refine lt_of_le_of_lt (Seminorm.finset_sup_apply_le hr'.le fun i hi => ?_) (half_lt_self hr)
  refine (seminorm_finset_sum_le _ u t).trans ?_
  exact (hS i u (Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem S hi) hu)).le

end GlobalTheory.ConvSeries
