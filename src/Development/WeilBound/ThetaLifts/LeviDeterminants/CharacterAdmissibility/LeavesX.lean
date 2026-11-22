module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.DetNeHerm
public import Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.LagLine

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.ThKF0.Chr

theorem axX (hA : PositivityTheory.Mix.AdelSt) {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) : Ax (adeleClass F) ψ :=
  by
    have hb : AxB (adeleClass F) ψ := by
      constructor
      · exact fun κ _ => (GlobalTheory.T.theta_distribution_heisenberg_invariant F κ ψ hψ.1 (isStd_ne_one hψ) hψ.2.1).1
      · intro κ _
        obtain ⟨φ, h, h0⟩ := GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F κ
        exact ⟨φ, h, fun e => h0 (congrFun e 0)⟩
      · exact fun κ _ => adelicCoordinatesEvalZeroForm_mem_admissible κ
      · exact fun κ₁ κ _ _ j hj φ hφ => GlobalTheory.RestrSchA.mem_schA_comp_extend F j hj φ hφ
      · intro κ₁ κ _ _ j hj l hl g hg
        obtain ⟨T, hT⟩ := hl _ (GlobalTheory.RestrSchA.sb_comp_extend F hj hg)
        refine ⟨T.comp (GlobalTheory.RestrSchA.restrS F hj), fun f => ?_⟩
        rw [ContinuousLinearMap.comp_apply, ← hT]
        exact congrArg l (funext fun y => GlobalTheory.RestrSchA.pureA_extend F hj f g y)
      · exact fun κ κ' _ _ => GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ'
      · exact fun κ κ' _ _ => box_adm κ κ'
    exact ⟨hb, axDelta_of lagLine hψ, axImp_of hA hψ⟩

theorem theta_tower_hermitian_first (hA : PositivityTheory.Mix.AdelSt) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ (h : UA σ W.J), ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, h) Φ) = om₁ (1, h) (e Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he
  exact e_om_one_eq_om1_one_e (axX hA hP.base.std) hP hH hP₁ he

theorem theta_tower_hermitian_second (hA : PositivityTheory.Mix.AdelSt) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ (t : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) (g₁ : UA σ X₁.J) (m : UA σ X.J), IsLevi H t g₁ m → ∀ Φ ∈ schA F (Fin n × Fin d),
        e (om (m, 1) Φ) = ((χW t : ℂ) * (((absE F E t : ℝ) ^ ((d : ℝ) / 2) : ℝ) : ℂ)) • om₁ (g₁, 1) (e Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he
  exact mixX_levi (axX hA hP.base.std) hP hH hP₁ he

end PositivityTheory.ThKF0.Chr
