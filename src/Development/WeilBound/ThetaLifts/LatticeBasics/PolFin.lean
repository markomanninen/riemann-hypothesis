module

public import Mathlib
public import Development.WeilBound.ThetaLifts.LatticeBasics.RealInv
public import Development.WeilBound.ThetaLifts.SchwartzMoments.PolynomialFunctionalEvalContinuous

@[expose] public section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CompanionTheory.Ar.RT

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem polFin {B : Base F E} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {χX χW} {om : Rep σ Y W} {r s r' s'}
    (h : IsPair B M χX χW om r s r' s') : ∀ f ∈ M.Pol B.ψ B.emb, ∃ U : Submodule ℂ (SInf F (Fin n × Fin d)),
      FiniteDimensional ℂ U ∧ ∀ k ∈ KInf σ W B.emb, ∀ f₁ : SInf F _, Acts (evI F) (om (1, k)) f f₁ → f₁ ∈ U := by
  intro f hf
  have hψ := h.base.std
  have hs := h.weil.isUSplitting.toIsSplitting
  let S : Submodule ℂ (SInf F (Fin n × Fin d)) :=
    { carrier := {f | ∃ U : Submodule ℂ (SInf F (Fin n × Fin d)), FiniteDimensional ℂ U ∧
        ∀ k ∈ KInf σ W B.emb, ∀ A, PositivityTheory.ThKOwn.KPol.Impl om k A → A f ∈ U}
      zero_mem' := ⟨⊥, inferInstance, fun k _ A _ => by rw [map_zero]; exact zero_mem _⟩
      add_mem' := by
        rintro f g ⟨N, _, h1⟩ ⟨N', _, h2⟩
        exact ⟨N ⊔ N', inferInstance, fun k hk A hA => by
          rw [map_add (f := _)]; exact Submodule.add_mem_sup (h1 k hk A hA) (h2 k hk A hA)⟩
      smul_mem' := fun c f ⟨N, h0, h1⟩ => ⟨N, h0, fun k hk A hA => by rw [map_smul]; exact N.smul_mem c (h1 k hk A hA)⟩ }
  have hfS : f ∈ S := by
    refine (sInf_le (a := S) ⟨fun f₀ h₀ => ?_, fun u hu g ⟨N, h0, h1⟩ g₁ hg => ?_⟩ : M.Pol B.ψ B.emb ≤ S) hf
    · haveI := Dense.vacSp_fin h.base.cm M B.emb
      refine ⟨⨆ ε, Dense.vacSp M B.emb ε, inferInstance, fun k hk A hA => ?_⟩
      have hgauss : M.IsGauss B.ψ B.emb (A f₀) := by
        obtain ⟨ε, hε⟩ := h₀
        refine ⟨ε, fun u u' hu hu' hrel f f' hf hf' => ?_⟩
        set N := (mat k⁻¹).transpose with hN
        have hNk : N * (mat k).transpose = 1 := by
          rw [hN, ← Matrix.transpose_mul, PositivityTheory.ThKOwn.KPol.mat_mul_inv, Matrix.transpose_one]
        have e1 : u * N * (mat k).transpose = u := by rw [Matrix.mul_assoc, hNk, Matrix.mul_one]
        have e2 : u' * N * (mat k).transpose = u' := by rw [Matrix.mul_assoc, hNk, Matrix.mul_one]
        have hf1 := PositivityTheory.ThKOwn.KPol.actsD_unique M hψ hu hf
        have hf2 := PositivityTheory.ThKOwn.KPol.actsD_unique M hψ hu' hf'
        have i1 := PositivityTheory.ThKOwn.KPol.inter hψ hs hA (PositivityTheory.ThKOwn.KPol.at_mul hu N) f₀
        have i2 := PositivityTheory.ThKOwn.KPol.inter hψ hs hA (PositivityTheory.ThKOwn.KPol.at_mul hu' N) f₀
        rw [e1, ← hf1] at i1
        rw [e2, ← hf2] at i2
        have hcomm : ∀ w, Commute ((mat k⁻¹).map (piInf (B.emb w))) (W.θ w) := fun w => by
          have hc : Commute ((mat k).map (piInf (B.emb w))) (W.θ w) := hk.2 w
          have h1 : (mat k⁻¹).map (piInf (B.emb w)) * (mat k).map (piInf (B.emb w)) = 1 := by
            rw [← Matrix.map_mul, PositivityTheory.ThKOwn.KPol.mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
          have h2 : (mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w)) = 1 := by
            rw [← Matrix.map_mul, PositivityTheory.ThKOwn.KPol.mat_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
          show _ * _ = _ * _
          calc (mat k⁻¹).map (piInf (B.emb w)) * W.θ w
              = (mat k⁻¹).map (piInf (B.emb w)) * W.θ w * ((mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w))) := by
                rw [h2, Matrix.mul_one]
            _ = (mat k⁻¹).map (piInf (B.emb w)) * (W.θ w * (mat k).map (piInf (B.emb w))) * (mat k⁻¹).map (piInf (B.emb w)) := by
                simp only [Matrix.mul_assoc]
            _ = (mat k⁻¹).map (piInf (B.emb w)) * ((mat k).map (piInf (B.emb w)) * W.θ w) * (mat k⁻¹).map (piInf (B.emb w)) := by
                rw [hc.eq]
            _ = W.θ w * (mat k⁻¹).map (piInf (B.emb w)) := by
                rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
        have hrel' : ∀ w, (u' * N).map (piInf (B.emb w)) =
            (((ε w : ℤ) : ℂ) * Complex.I) • (Y.θ w * (u * N).map (piInf (B.emb w)) * (W.θ w).transpose) := fun w => by
          have hN' : N.map (piInf (B.emb w)) = ((mat k⁻¹).map (piInf (B.emb w))).transpose := by
            rw [hN, Matrix.transpose_map]
          have hc : (W.θ w).transpose * N.map (piInf (B.emb w)) = N.map (piInf (B.emb w)) * (W.θ w).transpose := by
            rw [hN', ← Matrix.transpose_mul, ← Matrix.transpose_mul, (hcomm w).eq]
          rw [Matrix.map_mul, Matrix.map_mul, hrel w, Matrix.smul_mul]
          simp only [Matrix.mul_assoc, hc]
        have hg := hε (u * N) (u' * N) (PositivityTheory.ThKOwn.KPol.at_mul hu N) (PositivityTheory.ThKOwn.KPol.at_mul hu' N) hrel' _ _
          (PositivityTheory.ThKOwn.KPol.actsD_dop M hψ (PositivityTheory.ThKOwn.KPol.at_mul hu N) f₀) (PositivityTheory.ThKOwn.KPol.actsD_dop M hψ (PositivityTheory.ThKOwn.KPol.at_mul hu' N) f₀)
        rw [← i1, ← i2, hg, map_smul]
      obtain ⟨ε, hε⟩ := hgauss
      exact Submodule.mem_iSup_of_mem ε fun u u' hu hu' e => hε u u' hu hu' e _ _ (Dense.actsD_dop M hψ hu _)
        (Dense.actsD_dop M hψ hu' _)
    · obtain ⟨N', h3, h4⟩ := Dense.exists_dop_fin N
      refine ⟨N', h3, fun k hk A hA => ?_⟩
      rw [PositivityTheory.ThKOwn.KPol.actsD_unique M hψ hu hg, PositivityTheory.ThKOwn.KPol.inter hψ hs hA hu]
      exact h4 _ _ _ (h1 k hk A hA)
  change ∃ U : Submodule ℂ (SInf F (Fin n × Fin d)), FiniteDimensional ℂ U ∧
    ∀ k ∈ KInf σ W B.emb, ∀ A, PositivityTheory.ThKOwn.KPol.Impl om k A → A f ∈ U at hfS
  obtain ⟨U, h0, h1⟩ := hfS
  refine ⟨U, h0, fun k hk f₁ h₁ => ?_⟩
  obtain ⟨A, hA⟩ := PositivityTheory.ThKOwn.KPol.exists_impl fun f => PositivityTheory.ThKOwn.KPol.exists_arch_operator hψ hs hk.1 f
  rw [PositivityTheory.ThKOwn.KPol.acts_unique hA h₁]
  exact h1 k hk A hA

end GlobalTheory.ThK.Dbl

end
