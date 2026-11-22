module

public import Mathlib
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.InnerEuclideanEmbeddingEqAverage
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAtExtExtAll
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SubMulPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupNormFromNet
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNetMaxAtGoodEmb
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspReadingsLinearIndependent
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.EqZeroOfPnorm

@[expose] public section

noncomputable section

open Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.NetNorms NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory

private theorem linearIndependent_inclusion_of_le {K R ι : Type} [Field K] [AddCommGroup R] [Module K R]
    {A B : Submodule K R} (hAB : A ≤ B) (F : ι → A) (hF : LinearIndependent K F) :
    LinearIndependent K (fun i => (⟨F i, hAB (F i).2⟩ : B)) := by
  exact hF.map' (Submodule.inclusion hAB) (Submodule.ker_inclusion A B hAB)

set_option synthInstance.maxHeartbeats 200000 in
theorem exists_scalar_readings_on_net : ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → 16 ≤ D.R.f → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∃ (n : ℕ) (ev : Fin n → ((recB h.toLawsCore).Cusp j w →ₛₗ[σ] ℂ)), (∀ F, ∃ y, (recB h.toLawsCore).supN j w σ F / 4 ≤ ‖ev y F‖) ∧ (∀ y F, ‖ev y F‖ ≤ (recB h.toLawsCore).supN j w σ F) ∧ Real.log (16 * (n : ℝ)) ≤ 1041 * Zb D large₂ ^ 3 ∧ ∀ (m : ℕ) (F : Fin m → (recB h.toLawsCore).Cusp j w), LinearIndependent T.Q.c.F F → LinearIndependent ℂ (fun i => fun y => ev y (F i)) := by
  intro D T h hG large₂ j hj w hP hL hr hf σ hσ
  classical
  obtain ⟨NN, -, hnet, hlog⟩ :=
    GlobalTheory.RunIn.exists_net_max_at_goodEmb D T h hG large₂ j hj w hP hL hr hf σ hσ

  obtain ⟨L, hLdef⟩ : ∃ L, L = lieFac (T.Q.Dw j) (xiR D) (wtA w) := ⟨_, rfl⟩
  have hL0 : 0 < L := hLdef ▸ lieFac_pos _ _ _

  have hpn : ∀ (k : (T.U j σ).Comp) (P : Frame ((T.U j σ).X k).Ψ D.R.r → ℂ) x,
      ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) P x
        = ‖P x‖ * ((T.U j σ).X k).nfac (laU (T.U j σ) (wtA w) w.n k) x := fun _ _ _ => rfl
  have hnf : ∀ (k : (T.U j σ).Comp) x, 0 ≤ ((T.U j σ).X k).nfac (laU (T.U j σ) (wtA w) w.n k) x := by
    intro k x
    have h1 := GlobalTheory.NetNormExamples.pnorm_nonneg ((T.U j σ).X k) (laU (T.U j σ) (wtA w) w.n k)
      (fun _ => (1 : ℂ)) x
    rwa [hpn, norm_one, one_mul] at h1
  have hg : goodOf T.Q.c σ = σ := by rw [goodOf, ite_eq_left hσ]

  have hsup : ∀ F : (recB h.toLawsCore).Cusp j w, (recB h.toLawsCore).supN j w σ F =
      L * supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) F.1) := by
    intro F
    dsimp only [recB, cutN]
    rw [ite_eq_left hj]
    dsimp only [Formalism.L2.Pj.Core.Ns, supC]
    rw [hg, hLdef]

  have hhol : ∀ F : (recB h.toLawsCore).Cusp j w,
      rdU (T.U j σ) F.1 ∈ holSub (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) := by
    intro F
    have hC : F.1 ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n := (Submodule.mem_inf.mp F.2).1
    exact ((mem_cusp _ _ _ _ _ _).mp hC).2 σ hσ

  let pt : Fin NN.card → FPt (T.U j σ).X := fun y => (NN.equivFin.symm y).1
  have hsurj : ∀ p ∈ NN, ∃ y, pt y = p := fun p hp =>
    ⟨NN.equivFin ⟨p, hp⟩, by simp only [pt, Equiv.symm_apply_apply]⟩
  let a : Fin NN.card → ℝ := fun y =>
    L * ((T.U j σ).X (pt y).1).nfac (laU (T.U j σ) (wtA w) w.n (pt y).1) (pt y).2
  have ha : ∀ y, 0 ≤ a y := fun y => mul_nonneg hL0.le (hnf _ _)

  let ev : Fin NN.card → ((recB h.toLawsCore).Cusp j w →ₛₗ[σ] ℂ) := fun y =>
    { toFun := fun F => (a y : ℂ) * rdU (T.U j σ) F.1 (pt y).1 (pt y).2
      map_add' := fun F G => by
        show (a y : ℂ) * rdU (T.U j σ) (F.1 + G.1) (pt y).1 (pt y).2 =
          (a y : ℂ) * rdU (T.U j σ) F.1 (pt y).1 (pt y).2 + (a y : ℂ) * rdU (T.U j σ) G.1 (pt y).1 (pt y).2
        rw [map_add (f := _), Pi.add_apply, Pi.add_apply, mul_add]
      map_smul' := fun c F => by
        show (a y : ℂ) * rdU (T.U j σ) (c • F.1) (pt y).1 (pt y).2 =
          σ c • ((a y : ℂ) * rdU (T.U j σ) F.1 (pt y).1 (pt y).2)
        rw [LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
        ring }
  have hev : ∀ y F, ev y F = (a y : ℂ) * rdU (T.U j σ) F.1 (pt y).1 (pt y).2 := fun _ _ => rfl
  have hnorm : ∀ y F, ‖ev y F‖ =
      L * ((T.U j σ).X (pt y).1).pnorm (laU (T.U j σ) (wtA w) w.n (pt y).1)
        (rdU (T.U j σ) F.1 (pt y).1) (pt y).2 := by
    intro y F
    rw [hev, norm_mul, Complex.norm_of_nonneg (ha y), hpn]
    simp only [a]
    ring
  refine ⟨NN.card, ev, ?_, ?_, ?_, ?_⟩
  ·
    intro F
    obtain ⟨p, hp, hb⟩ := hnet _ (hhol F)
    obtain ⟨y, rfl⟩ := hsurj p hp
    refine ⟨y, ?_⟩
    rw [hnorm, hsup]
    have := mul_le_mul_of_nonneg_left hb hL0.le
    linarith
  ·
    intro y F
    rw [hnorm, hsup]
    exact mul_le_mul_of_nonneg_left
      (GlobalTheory.NetNormExamples.pnorm_le_supN (T.U j σ) _ (hhol F) (pt y)) hL0.le
  · exact hlog
  ·
    intro m F hF
    have hF' := linearIndependent_inclusion_of_le (B := T.C j w) inf_le_left F hF
    have hlin : LinearIndependent T.Q.c.F (fun i => (F i : T.R j)) :=
      hF'.map' (T.C j w).subtype (T.C j w).ker_subtype
    have hmem : ∀ i, (F i : T.R j) ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n := fun i =>
      Formalism.L2.Pj.cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n
        (Submodule.mem_inf.mp (F i).2).1
    have hind : LinearIndependent ℂ (fun i => rdU (T.U j σ) (F i : T.R j)) :=
      (GlobalTheory.reading_linearIndependent_and_injective
        GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ (T.Q.Xo j) T.Q.c σ _
        (Formalism.L2.PjFree.Unf.ofPj (T.U j σ))
        ((Formalism.L2.PjFree.isUnf_ofPj (T.U j σ)).2 (h.unf j hj σ hσ))
        (wtA w) w.n).1 m (fun i => (F i : T.R j)) hmem hlin
    rw [Fintype.linearIndependent_iff] at hind ⊢
    intro g hgz i
    refine hind g ?_ i
    show ∑ i, g i • rdU (T.U j σ) (F i).1 = 0
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = ∑ i, g i • rdU (T.U j σ) (F i).1 := ⟨_, rfl⟩
    rw [← hQ]
    have hQmem : Q ∈ holSub (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) := by
      rw [hQ]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hhol (F i))
    have hval : ∀ y, (a y : ℂ) * Q (pt y).1 (pt y).2 = 0 := by
      intro y
      have h1 := congrFun hgz y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hev] at h1
      rw [hQ, Finset.sum_apply, Finset.sum_apply, Finset.mul_sum, ← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    obtain ⟨p, hp, hb⟩ := hnet Q hQmem
    obtain ⟨y, rfl⟩ := hsurj p hp
    have h0 : ((T.U j σ).X (pt y).1).pnorm (laU (T.U j σ) (wtA w) w.n (pt y).1) (Q (pt y).1) (pt y).2 = 0 := by
      have hn := congrArg (‖·‖) (hval y)
      simp only [norm_mul, Complex.norm_of_nonneg (ha y), norm_zero] at hn
      simp only [a] at hn
      rw [hpn]
      have h2 : L * (‖Q (pt y).1 (pt y).2‖ *
          ((T.U j σ).X (pt y).1).nfac (laU (T.U j σ) (wtA w) w.n (pt y).1) (pt y).2) = 0 := by
        rw [← hn]; ring
      exact (mul_eq_zero.mp h2).resolve_left hL0.ne'
    have hS : supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) Q ≤ 0 := by
      rw [h0, mul_zero] at hb
      exact hb
    funext k x
    by_cases hx : x ∈ ((T.U j σ).X k).dom
    · show Q k x = 0
      apply GlobalTheory.NetNormExamples.eq_zero_of_pnorm ((T.U j σ).X k) (laU (T.U j σ) (wtA w) w.n k) _ hx
      exact le_antisymm
        ((GlobalTheory.NetNormExamples.pnorm_le_supN (T.U j σ) _ hQmem ⟨k, ⟨x, hx⟩⟩).trans hS)
        (GlobalTheory.NetNormExamples.pnorm_nonneg _ _ _ _)
    · show Q k x = 0
      rw [hQ, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hz : rdU (T.U j σ) (F i).1 k x = 0 := by
        simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dite_eq_right hx]
      rw [Pi.smul_apply, Pi.smul_apply, hz, smul_zero]

end GlobalTheory
