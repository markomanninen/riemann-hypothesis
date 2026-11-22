module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBP
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CccoefMono
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGerm

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal

noncomputable section

def cutN (k r n : ℕ) (g : B.Mat k r) : ℂ :=
  ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)

def apx {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (G : B.Mat k r → (Wq →L[ℂ] Wp)) (n : ℕ) : B.Mat k r → (Wq →L[ℂ] Wp) :=
  fun g => cutN k r n g • G g

theorem cptCoef_apx {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {χ : ℝ → ℝ} (hχ : C6.IsCut0 χ) (hF : B.CkOn ⊤ (B.GV P.k P.r) F) {ε : ℝ}
    (hε : 0 < ε) (n : ℕ) : KB.CptCoef Bs (apx (D.cutF Bs χ F ε) n) := by
  letI : NormedAddCommGroup (B.Mat P.k P.r) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (B.Mat P.k P.r) := Matrix.normedSpace
  obtain ⟨hχs, ⟨δ, hδ, hχ0⟩, -⟩ := hχ
  refine ⟨?_, ⟨2 * ((n : ℝ) + 1), ?_⟩, ⟨δ * ε, mul_pos hδ hε, ?_⟩⟩
  · intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hF', hFe⟩ := hF g₀ hg₀
    refine ⟨U, fun g => cutN P.k P.r n g • (((χ (Gf P.k P.r Bs.z Bs.z' g / ε) : ℝ) : ℂ) • F' g),
      hU, hgU, ?_, ?_⟩
    · have hn2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => Complex.normSq z) := by
        have e : (fun z : ℂ => Complex.normSq z) = fun z => z.re * z.re + z.im * z.im := by
          funext z
          exact Complex.normSq_apply z
        rw [e]
        exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
          (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
      have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : B.Mat P.k P.r => cutN P.k P.r n g) := by
        unfold cutN
        refine Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp ?_)
        refine (contDiff_const.sub ?_).div_const _
        refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => hn2.comp ?_
        exact (contDiff_apply_apply ℝ i j).comp (contDiff_id.const_smul (((n : ℝ) + 1)⁻¹))
      exact hc.contDiffOn.smul ((Complex.ofRealCLM.contDiff.comp
        (hχs.comp ((JCx1.contDiff_Gf Bs.z Bs.z').div_const ε))).contDiffOn.smul hF')
    · intro g hg hgv
      simp only [apx, D.cutF]
      rw [hFe g hg hgv]
  · intro g _ hne
    have h1 : cutN P.k P.r n g ≠ 0 := by
      intro h0
      apply hne
      simp only [apx, h0, zero_smul]
    simp only [cutN, ne_eq, Complex.ofReal_eq_zero, Real.smoothTransition.zero_iff_nonpos, not_le] at h1
    have hs : ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j) < 4 := by
      have := (div_pos_iff_of_pos_right (by norm_num : (0 : ℝ) < 3)).1 h1
      linarith
    have heq : ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j) =
        ((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.smul_apply, Complex.real_smul, Complex.normSq_mul, Complex.normSq_ofReal]
      ring
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hS : ∑ i, ∑ j, Complex.normSq (g i j) ≤ (2 * ((n : ℝ) + 1)) ^ 2 := by
      rw [heq, inv_pow, inv_mul_lt_iff₀ (by positivity)] at hs
      have e2 : (2 * ((n : ℝ) + 1)) ^ 2 = ((n : ℝ) + 1) ^ 2 * 4 := by ring
      rw [e2]
      exact hs.le
    unfold B.gN
    calc Real.sqrt (∑ i, ∑ j, Complex.normSq (g i j)) ≤ Real.sqrt ((2 * ((n : ℝ) + 1)) ^ 2) :=
          Real.sqrt_le_sqrt hS
      _ = 2 * ((n : ℝ) + 1) := Real.sqrt_sq (by positivity)
  · intro g _ hne
    have h1 : ((χ (Gf P.k P.r Bs.z Bs.z' g / ε) : ℝ) : ℂ) ≠ 0 := by
      intro h0
      apply hne
      simp only [apx, D.cutF, h0, zero_smul, smul_zero]
    have h2 : δ ≤ Gf P.k P.r Bs.z Bs.z' g / ε := by
      by_contra hlt
      push_neg at hlt
      exact h1 (by rw [hχ0 _ hlt]; simp)
    rwa [le_div_iff₀ hε] at h2

section fpmCk

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ckOn_fpm {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq)
    {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {A : B.Mat P.k P.r → (Wq →L[ℂ] Wq)} (p₀ : ℕ)
    (hf : B.CkOn ⊤ (B.GV P.k P.r) f) (hA : B.CkOn ⊤ (B.GV P.k P.r) A) :
    B.CkOn ⊤ (B.GV P.k P.r) (TBBx4.fpm p f A p₀) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hfe⟩ := ckOn_comp hf hA g₀ hg₀
  refine ⟨U, fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • f' g, hU, hgU, ?_, ?_⟩
  · have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun g : B.Mat P.k P.r => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp ((JCx1.contDiff_Gf p.T.base.z p.T.base.z').pow p₀)
    exact hs.contDiffOn.smul hf'
  · intro g hg hgv
    simp only [TBBx4.fpm]
    congr 1
    exact hfe g hg hgv

end fpmCk

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def LimTopN (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ γ : C.LPt, D.IsLocPt γ (P.r + 1) →
    Tendsto (fun n : ℕ => TBB.Ew p nn (apx G n) (P.r + 1) [] γ) atTop (𝓝 (TBB.Ew p nn G (P.r + 1) [] γ))

def LimZeroN (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) : Prop :=
  ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
    Tendsto (fun n : ℕ => TBB.Ew p nn (apx G n) 0 w []) atTop (𝓝 (TBB.Ew p nn G 0 w []))

theorem corS_of_apx (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ)
    (Λ : ℝ) (K N : ℕ) (C₂ : ℝ) (hC : ∀ n, TBB.CorS p nn (apx G n) Y Λ K N C₂) (hT : LimTopN p nn G)
    (hZ : LimZeroN p nn G Y N) : TBB.CorS p nn G Y Λ K N C₂ := by
  classical
  intro γ hγ
  have h := fun n => hC n γ hγ
  choose w hw hle using h
  set A : Finset C.Letter := Y.image (fun y => ((true, y) : C.Letter)) ∪
    Y.image (fun y => ((false, y + 1) : C.Letter)) with hA
  have hmem : ∀ n, ∀ l ∈ w n, l ∈ A := by
    intro n l hl
    obtain ⟨-, -, L, hL, -, hLl⟩ := hw n
    rw [hL, List.append_nil] at hl
    obtain ⟨y, hy, h | h⟩ := hLl l hl
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨y, hy, h.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y, hy, h.symm⟩)
  have hfin : (Set.range w).Finite := by
    refine ((List.finite_length_le (↥A) N).image (fun l => l.map Subtype.val)).subset ?_
    rintro _ ⟨n, rfl⟩
    refine ⟨(w n).pmap Subtype.mk (hmem n), ?_, ?_⟩
    · simp only [Set.mem_setOf_eq, List.length_pmap]
      exact (hw n).2.1
    · simp [List.map_pmap]
  obtain ⟨w0, hw0⟩ : ∃ w0, ∃ᶠ n in atTop, w n = w0 := by
    by_contra hcon
    push_neg at hcon
    have h2 := (Filter.eventually_all_finite hfin).mpr fun i _ => hcon i
    obtain ⟨n, hn⟩ := h2.exists
    exact hn (w n) ⟨n, rfl⟩ rfl
  have hw0' : TBB.IsExt P p.l0 Y N ((P.r + 1) * K) [] w0 := by
    obtain ⟨n, rfl⟩ := hw0.exists
    exact hw n
  refine ⟨w0, hw0', ?_⟩
  have hadm : TBB.AdmW P p.l0 Y w0 := by
    obtain ⟨hcut, -, L, hL, -, hLl⟩ := hw0'
    refine ⟨hcut, fun l hl => hLl l ?_⟩
    rwa [hL, List.append_nil] at hl
  have hlim := (hZ w0 hadm hw0'.2.1).const_mul ((C₂ * Λ ^ 2) ^ (P.r + 1)) |>.sub (hT γ hγ)
  have hfreq : ∃ᶠ n in atTop, (C₂ * Λ ^ 2) ^ (P.r + 1) * TBB.Ew p nn (apx G n) 0 w0 [] -
      TBB.Ew p nn (apx G n) (P.r + 1) [] γ ∈ Set.Ici (0 : ℝ) :=
    hw0.mono fun n hn => by
      rw [← hn]
      exact sub_nonneg.mpr (hle n)
  exact sub_nonneg.mp (isClosed_Ici.mem_of_frequently_of_tendsto hfreq hlim)

end place

end

end Formalism.FourierDecayAlt.P.CutBP
