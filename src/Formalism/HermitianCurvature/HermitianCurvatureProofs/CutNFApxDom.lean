module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopForm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDom
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CccoefMono

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def DominatedL2TruncationBound : Prop :=
  ∀ Cb C₁ : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ Th : B.DiffOp P.k P.r Wp Wq, NFOpOK C₁ p N Th →
      ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧ ∀ n : ℕ, ∀ᵐ c : Fin (P.r + 1) → ℂ,
        ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀ - N) *
          TBB.Ew p (fun _ => 1) (B.opApply Th (fun g => cutN P.k P.r n g • f g)) (P.r + 1) [] (TBB.bigPt P.r c) ≤ h c

section cutn

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cutN_ckOn {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E}
    (hf : B.CkOn (⊤ : ℕ∞) (B.GV k r) f) (n : ℕ) :
    B.CkOn (⊤ : ℕ∞) (B.GV k r) (fun g => cutN k r n g • f g) := by
  have hN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => Complex.normSq z) := by
    simp_rw [Complex.normSq_apply]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutN k r n) := by
    unfold cutN
    refine Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp ?_)
    refine ContDiff.div_const (contDiff_const.sub ?_) _
    refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
    exact hN.comp ((contDiff_apply_apply (𝕜 := ℝ) i j).comp (contDiff_const_smul _))
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hff⟩ := hf g₀ hg₀
  refine ⟨U, fun g => cutN k r n g • f' g, hU, hgU, hc.contDiffOn.smul hf', fun g hg hgv => ?_⟩
  show cutN k r n g • f g = cutN k r n g • f' g
  rw [hff g hg hgv]

end cutn

end

end Formalism.FourierDecayAlt.P.CutBP
