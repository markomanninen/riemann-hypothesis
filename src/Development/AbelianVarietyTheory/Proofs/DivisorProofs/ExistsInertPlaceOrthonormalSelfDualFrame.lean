module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InclRMulPtAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSelfDualEverywhere

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertUnitFrame

theorem exists_frame_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a'), B.IsGood σ → G.IsGood B → ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w → ∀ (h : w.under (𝓞 F) = v) (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∃ A : GL (Fin a') (w.adicCompletion E), IsFrameAt w G.V'.L A ∧
      (A : Matrix (Fin a') (Fin a') (w.adicCompletion E))ᵀ * G.V'.J.map (algebraMap E (w.adicCompletion E)) *
        (A : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL = 1 := by
  intro F E _ _ _ _ _ σ B a a' G hB hG v w hw h σL hc
  have hX := hG.hV'
  have hd : (G.V'.Jᵀ).det ≠ 0 := by
    rw [Matrix.det_transpose]; exact GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm σ B hX
  have hJ : IsHermND σ G.V'.Jᵀ :=
    ⟨fun i j => by simp only [Matrix.transpose_apply]; exact hX.herm j i, hd⟩
  have hs : IsSelfDualAt σ G.V'.Jᵀ G.V'.L v :=
    GlobalTheory.HermSelfDualLoc.isSelfDualAt_transpose F E σ B a' G.V' _ _ hB hX v
  have hspan : Submodule.span E (G.V'.L : Set (Fin a' → E)) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    let a : Fin a' → E := fun i => σ (f (Pi.single i 1))
    let u : Fin a' → E := a ᵥ* G.V'.J⁻¹
    have hu : u ᵥ* G.V'.J = a := by
      simp [u, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm σ B hX))]
    have hform (x : Fin a' → E) : form σ G.V'.J u x = σ (f x) := by
      rw [form, Matrix.dotProduct_mulVec, hu, LinearMap.pi_apply_eq_sum_univ f x, map_sum]
      change ∑ i, a i * σ (x i) = _
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_eq_mul, map_mul, mul_comm]
      have he : (fun j => if k = j then (1 : E) else 0) = Pi.single k 1 := funext fun j => by
        rw [Pi.single_apply]; exact if_congr eq_comm rfl rfl
      rw [he]
    have hline (c : E) : c • u ∈ G.V'.L := by
      apply (hX.dual _).2
      intro x hx
      have hx0 : f x = 0 := hf (Submodule.subset_span hx)
      have he : form σ G.V'.J (c • u) x = c * form σ G.V'.J u x := by
        simp [form, smul_dotProduct, smul_eq_mul]
      rw [he, hform, hx0, map_zero, mul_zero]
      exact isIntegral_zero
    have hu0 : u = 0 := by
      by_contra hn
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hn
      let coord := (LinearMap.proj i : (Fin a' → E) →ₗ[E] E).restrictScalars (𝓞 E)
      have ht : G.V'.L.map coord = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact ⟨(x / u i) • u, hline _, div_mul_cancel₀ _ hi⟩
      have : Module.Finite (𝓞 E) E := Module.finite_def.mpr (ht ▸ hX.lat.fg.map coord)
      exact RingOfIntegers.not_isField E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
    have ha : a = 0 := by simpa [hu0] using hu.symm
    apply hf0
    apply LinearMap.ext
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    apply Finset.sum_eq_zero
    intro i _
    have hi : σ (f (Pi.single i 1)) = 0 := congrFun ha i
    have hi' : f (Pi.single i 1) = 0 := (map_eq_zero σ).mp hi
    have he : (fun j => if i = j then (1 : E) else 0) = Pi.single i 1 := funext fun j => by
      rw [Pi.single_apply]; exact if_congr eq_comm rfl rfl
    simp [he, hi']
  obtain ⟨f, hf, ef⟩ := InertChart.exists_frame_antiJ hB.cm hJ hX.lat.fg hspan hw hc hs
  obtain ⟨ϖ, hU⟩ := InertChart.exists_isUnramInv hB.cm hw hc
  obtain ⟨k, hk, ek⟩ := InertChart.exists_congr_antiJ hU (B := 1) (one_mem _) (by exact Formalism.UG.cT_one _)
  refine ⟨f * k⁻¹, (InertChart.isFrameAt_mul hf (inv_mem hk)).1, ?_⟩
  have key : Formalism.UG.cT σL (f * k⁻¹).1 * (G.V'.Jᵀ).map (algebraMap E (w.adicCompletion E)) * (f * k⁻¹).1 = 1 := by
    rw [Units.val_mul, Formalism.UG.cT_mul, Units.val_one, Matrix.mul_one] at *
    calc Formalism.UG.cT σL (k⁻¹).1 * Formalism.UG.cT σL f.1 * (G.V'.Jᵀ).map (algebraMap E (w.adicCompletion E)) * (f.1 * (k⁻¹).1)
        = Formalism.UG.cT σL (k⁻¹).1 * (Formalism.UG.cT σL f.1 * (G.V'.Jᵀ).map (algebraMap E (w.adicCompletion E)) * f.1) * (k⁻¹).1 := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT σL (k⁻¹).1 * Formalism.UG.cT σL k.1 * (k.1 * (k⁻¹).1) := by
          rw [ef, ← ek]; simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [← Formalism.UG.cT_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Formalism.UG.cT_one, Matrix.one_mul]
  have := congrArg Matrix.transpose key
  simpa [Formalism.UG.cT, Matrix.transpose_mul, Matrix.transpose_map, Matrix.mul_assoc] using this

end GlobalTheory.InertUnitFrame
