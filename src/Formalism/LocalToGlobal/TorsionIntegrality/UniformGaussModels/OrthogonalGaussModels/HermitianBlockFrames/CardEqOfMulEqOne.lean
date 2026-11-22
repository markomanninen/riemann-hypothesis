module

public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.InsSuccAbove

@[expose] public section

open Matrix

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
namespace JSetup

variable {K : Type*} [Field K] (S : JSetup K)

private theorem mulVec_comp_equiv_apply {ι : Type*} [Fintype ι] {m : ℕ} (Γ : Matrix ι ι K) (e : ι ≃ Fin m)
    (x : Fin m → K) (i : ι) :
    (Γ *ᵥ (x ∘ e)) i = (Γ.submatrix e.symm e.symm *ᵥ x) (e i) := by
  simp only [mulVec, dotProduct, submatrix_apply, Equiv.symm_apply_apply, Function.comp]
  exact Fintype.sum_equiv e _ _ (fun j => by simp)

private theorem vecMul_comp_equiv_apply {ι : Type*} [Fintype ι] {m : ℕ} (Γ : Matrix ι ι K) (e : ι ≃ Fin m)
    (x : Fin m → K) (j : ι) :
    ((x ∘ e) ᵥ* Γ) j = (x ᵥ* Γ.submatrix e.symm e.symm) (e j) := by
  simp only [vecMul, dotProduct, submatrix_apply, Equiv.symm_apply_apply, Function.comp]
  exact Fintype.sum_equiv e _ _ (fun i => by simp)

theorem jac {ι : Type*} [Fintype ι] [DecidableEq ι] (Γ : Matrix ι ι K) (hΓ : S.IntM Γ) (hH : S.Herm Γ)
    (hU : S.UM Γ) :
    ∃ (k : ℕ) (v : Fin k → ι → K), (∀ c, S.IntV (v c)) ∧
      (∀ c c', S.hf Γ (v c) (v c') = if c = c' then 1 else 0) ∧
      ∑ c, Matrix.vecMulVec (Γ *ᵥ v c) (S.cv (v c) ᵥ* Γ) = Γ := by
  classical
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  have hU' : S.UM (Γ.submatrix e.symm e.symm) := by
    intro x hx hxd
    obtain ⟨x', hx', hxx'⟩ := hU (x ∘ e) (fun i => hx (e i)) (fun i => by
      rw [mulVec_comp_equiv_apply Γ e x i]; exact hxd (e i))
    refine ⟨x' ∘ e.symm, fun s => hx' (e.symm s), ?_⟩
    funext s
    have h1 := mulVec_comp_equiv_apply Γ e x (e.symm s)
    have h2 := mulVec_comp_equiv_apply Γ e (x' ∘ e.symm) (e.symm s)
    rw [Equiv.apply_symm_apply] at h1 h2
    have h3 : (x' ∘ e.symm) ∘ e = x' := by funext i; simp
    rw [h3] at h2
    rw [Pi.smul_apply, ← h1, ← h2, hxx', Pi.smul_apply]
  have jac_fin : ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) K), S.IntM Γ → S.Herm Γ → S.UM Γ →
      ∃ (k : ℕ) (v : Fin k → Fin m → K), (∀ c, S.IntV (v c)) ∧
        (∀ c c', S.hf Γ (v c) (v c') = if c = c' then 1 else 0) ∧
        ∑ c, vecMulVec (Γ *ᵥ v c) (S.cv (v c) ᵥ* Γ) = Γ := by
    intro m
    induction m with
    | zero =>
      intro Γ _ _ _
      exact ⟨0, Fin.elim0, fun c => c.elim0, fun c => c.elim0, by ext i; exact i.elim0⟩
    | succ m ih =>
      intro Γ hΓ hH hU
      by_cases h0 : Γ = 0
      · exact ⟨0, Fin.elim0, fun c => c.elim0, fun c => c.elim0, by simp [h0]⟩
      obtain ⟨a, i, ha, hai, haa⟩ := S.exists_unit_vec (Γ := Γ) hΓ hH hU h0
      have hG := S.IntM_Γp hΓ ha
      have hHG := S.Herm_Γp hΓ hH ha
      have hUG := S.UM_Γp hΓ hH hU ha haa
      have hGa := S.Γp_mulVec_self (Γ := Γ) haa
      have haG := S.vecMul_Γp_self (Γ := Γ) haa
      set G := S.Γp Γ a with hG_def
      obtain ⟨k, v'', hvI, hvo, hvs⟩ := ih (G.submatrix i.succAbove i.succAbove)
        (fun s t => hG _ _) (fun s t => hHG _ _) (S.UM_drop i hUG ha hai hGa haG)
      have hai0 : a i ≠ 0 := S.ne_zero_of_not_NU hai
      have hσa : S.σ (a i) ≠ 0 := S.ne_zero_of_not_NU (S.not_NU_σ (ha i) hai)
      set v' : Fin k → Fin (m + 1) → K := fun c => ins i (v'' c) with hv'_def
      have hv'I : ∀ c, S.IntV (v' c) := fun c => S.IntV_ins i (hvI c)
      have hv'o : ∀ c c', S.hf G (v' c) (v' c') = if c = c' then 1 else 0 := fun c c' => by
        rw [hv'_def, S.hf_ins, hvo]
      have hv's : ∑ c, vecMulVec (G *ᵥ v' c) (S.cv (v' c) ᵥ* G) = G := by
        apply S.ext_drop i hai0 hσa _ hGa _ haG
        · intro s t
          rw [Matrix.sum_apply]
          conv_rhs => rw [← submatrix_apply G i.succAbove i.succAbove s t, ← hvs, Matrix.sum_apply]
          refine Finset.sum_congr rfl fun c _ => ?_
          simp only [vecMulVec_apply, hv'_def, S.cv_ins, mulVec_ins, vecMul_ins]
        · rw [sum_mulVec']
          refine Finset.sum_eq_zero fun c _ => ?_
          rw [vecMulVec_mulVec, ← dotProduct_mulVec, hGa, dotProduct_zero, op_smul_eq_smul, zero_smul]
        · rw [vecMul_sum']
          refine Finset.sum_eq_zero fun c _ => ?_
          rw [vecMul_vecMulVec, dotProduct_mulVec, haG, zero_dotProduct, zero_smul]
      refine ⟨k + 1, Fin.cons a (fun c => S.proj Γ a (v' c)), ?_, ?_, ?_⟩
      · intro c
        refine Fin.cases ?_ (fun c => ?_) c
        · simpa using ha
        · simpa using S.IntV_proj hΓ ha (hv'I c)
      · intro c c'
        refine Fin.cases ?_ (fun c => ?_) c <;> refine Fin.cases ?_ (fun c' => ?_) c'
        · simpa using haa
        · simp only [Fin.cons_zero, Fin.cons_succ, S.hf_self_proj haa]
          rw [ite_eq_right (Fin.succ_ne_zero c').symm]
        · simp only [Fin.cons_zero, Fin.cons_succ, S.hf_proj_self hΓ hH ha haa (hv'I c)]
          rw [ite_eq_right (Fin.succ_ne_zero c)]
        · simp only [Fin.cons_succ, S.hf_proj_proj haa, Fin.succ_inj]
          exact hv'o c c'
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        have : ∀ c, vecMulVec (Γ *ᵥ S.proj Γ a (v' c)) (S.cv (S.proj Γ a (v' c)) ᵥ* Γ)
            = vecMulVec (G *ᵥ v' c) (S.cv (v' c) ᵥ* G) := fun c => by
          rw [S.mulVec_proj, S.vecMul_proj hΓ hH ha (hv'I c)]
        rw [Finset.sum_congr rfl (fun c _ => this c), hv's, hG_def, Γp]
        abel
  obtain ⟨k, v, hv, hort, hsum⟩ := jac_fin (Fintype.card ι) (Γ.submatrix e.symm e.symm)
    (fun s t => hΓ _ _) (fun s t => hH _ _) hU'
  have hconj : ∀ x : Fin (Fintype.card ι) → K, S.cv (x ∘ e) = S.cv x ∘ e := fun x => rfl
  refine ⟨k, fun c => v c ∘ e, fun c i => hv c (e i), fun c c' => ?_, ?_⟩
  · rw [← hort c c']
    simp only [hf, hconj, dotProduct]
    exact Fintype.sum_equiv e _ _ (fun i => by
      simp only [Function.comp, mulVec_comp_equiv_apply Γ e (v c') i])
  · ext i j
    have h := congrFun (congrFun hsum (e i)) (e j)
    simp only [Matrix.sum_apply, vecMulVec_apply, submatrix_apply, Equiv.symm_apply_apply] at h
    simp only [Matrix.sum_apply, vecMulVec_apply, hconj, mulVec_comp_equiv_apply Γ e _ i,
      vecMul_comp_equiv_apply Γ e _ j]
    exact h

end JSetup

theorem card_eq_of_mul_eq_one {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ}
    (V : Matrix n (Fin k) K) (W : Matrix (Fin k) n K) (h1 : V * W = 1) (h2 : W * V = 1) :
    Fintype.card n = k := by
  have e : (Fin k → K) ≃ₗ[K] (n → K) :=
    LinearEquiv.ofLinear (Matrix.toLin' V) (Matrix.toLin' W)
      (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])
  have h := e.finrank_eq
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  omega

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
