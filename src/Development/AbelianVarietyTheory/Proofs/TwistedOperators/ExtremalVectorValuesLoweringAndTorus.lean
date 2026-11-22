module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorAnnihilated

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExtFock

section Perm

variable {n : ℕ} (π : Fin n → Fin n)

theorem submatrix_eq_mul (P : Matrix (Fin n) (Fin n) ℂ) :
    P.submatrix id π = P * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π := by
  ext a b
  simp [Matrix.mul_apply, Matrix.one_apply]

variable {π}

theorem perm_mul_self (hπ : ∀ a, π (π a) = a) :
    (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.one_apply]
  simp [mul_ite, Finset.sum_ite_eq', hπ]

theorem perm_single_perm (hπ : ∀ a, π (π a) = a) (c d : Fin n) :
    (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π * Matrix.single c d 1 * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π =
      Matrix.single (π c) (π d) 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.one_apply, Matrix.single_apply]
  simp [mul_ite, ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, hπ]
  have key : ∀ x y, x = π y ↔ π x = y := fun x y => ⟨fun h => by rw [h, hπ], fun h => by rw [← h, hπ]⟩
  simp only [ite_and, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [key d b]
  by_cases h1 : π c = a
  · subst h1; simp
  · have h2 : ¬ a = π c := fun h => h1 h.symm
    simp [h1, h2]

theorem perm_diag_perm (hπ : ∀ a, π (π a) = a) (t : Fin n → ℂ) :
    (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π * Matrix.diagonal t * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π =
      Matrix.diagonal (fun a => t (π a)) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.one_apply, Matrix.diagonal_apply]
  simp [mul_ite, ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, hπ]
  split_ifs with h
  · rw [h]
  · rfl

theorem conj_submatrix (hπ : ∀ a, π (π a) = a) (P X : Matrix (Fin n) (Fin n) ℂ) :
    P.submatrix id π * X * (P.submatrix id π)⁻¹ =
      P * ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π * X * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π) * P⁻¹ := by
  rw [submatrix_eq_mul π P, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv (perm_mul_self hπ)]
  simp only [Matrix.mul_assoc]

end Perm

theorem killPair_rev {n p : ℕ} (hpn : p ≤ n) {c d : Fin n} (h : d < c) :
    GlobalTheory.HolRead.KillPair (fun a : Fin n => decide ((a : ℕ) < p)) (GlobalTheory.AdSpan.revPos p c) (GlobalTheory.AdSpan.revPos p d) := by
  have hdc : (d : ℕ) < c := h
  unfold GlobalTheory.HolRead.KillPair GlobalTheory.AdSpan.revPos
  by_cases hc : (c : ℕ) < p <;> by_cases hd : (d : ℕ) < p
  · left
    simp only [dif_pos (And.intro hc hpn), dif_pos (And.intro hd hpn), Fin.lt_def]
    refine ⟨by simp; omega, by simp; omega, by omega⟩
  · omega
  · right; right
    simp only [dif_neg (fun h' : (c : ℕ) < p ∧ p ≤ n => hc h'.1), dif_pos (And.intro hd hpn), Fin.lt_def]
    refine ⟨by simp; omega, by omega⟩
  · right; left
    simp only [dif_neg (fun h' : (c : ℕ) < p ∧ p ≤ n => hc h'.1), dif_neg (fun h' : (d : ℕ) < p ∧ p ≤ n => hd h'.1), Fin.lt_def]
    refine ⟨by simp; omega, by simp; omega, hdc⟩

end GlobalTheory.ExtFock

namespace GlobalTheory.ExtFock


open GlobalTheory.HolRead.ExtKill in
set_option maxHeartbeats 4000000 in
theorem ext_values : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T0) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (w : (R.cV i).W) (p : ℕ), (∀ τ, ((Wc D i).sig (tauE D τ)).1 = p) → p ≤ (Wc D i).rank → IsExtVec (R.MW i (sg0 D A)) (fun ρ => u ρ) → ∀ T ∈ R.Wall i (sg0 D A), LowKilled R.θ (Wc D i) (revB p (onb (R.MW i (sg0 D A)))) (T fun ρ => u ρ) ∧ ∀ (ρ : D.what₂.Tau) (s : Fin (Wc D i).rank → ℝ), ∃ l : ℂ, R.ωP i t (1, torAt R.θ (Wc D i) (revB p (onb (R.MW i (sg0 D A)))) ρ s) (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) w)) = l • R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) w) ∧ ∀ g, T (fun ρ => u ρ) (g * torAt R.θ (Wc D i) (revB p (onb (R.MW i (sg0 D A)))) ρ s) = l * T (fun ρ => u ρ) g := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hM hP i t u w p hp hpn hext T hT
  have hTm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hT
  have hεd : ∀ ρ, (R.MW i (sg0 D A)).ε ρ = fun a : Fin (Wc D i).rank => decide ((a : ℕ) < p) := by
    intro ρ; funext a; rw [hM.order i ρ a, hp ρ]
  have hε : ∀ ρ (a : Fin (Wc D i).rank), (R.MW i (sg0 D A)).ε ρ a = if (a : ℕ) < p then true else !true := by
    intro ρ a; rw [hεd ρ]; by_cases h : (a : ℕ) < p <;> simp [h]
  let V := Wc D i
  let M := R.MW i (sg0 D A)
  let v : M.Vec := fun ρ => u ρ
  have KW (ρ : D.what₂.Tau) :
      (∀ a b, GlobalTheory.HolRead.KillPair (M.ε ρ) a b →
        RderC R.θ V ρ ((M.fr ρ)⁻¹ * Matrix.single a b 1 * M.fr ρ) (T v) = 0) ∧
      ∀ (s : Fin V.rank → ℝ) (g : GA D V),
        T v (g * atTau R.θ V ρ ((M.fr ρ)⁻¹ *
          Matrix.diagonal (fun a => Complex.exp ((s a : ℂ) * Complex.I)) * M.fr ρ)) =
        Complex.exp (((∑ a, extWt M ρ a * s a : ℝ) : ℂ) * Complex.I) * T v g := by
    have hFrame := M.fr_unit ρ
    have hGram := M.fr_gram ρ
    obtain ⟨-, hlow, hwt⟩ := hext ρ
    have hlow' : (v ρ : M.H ρ) ∈ Formalism.MainNotions.S.lowKSub (M.ε ρ) (M.lam ρ) (M.σ ρ) := hlow
    refine ⟨fun a b hab => ?_, fun s g => ?_⟩
    · have hs := GlobalTheory.HolRead.MultDer.smoothVec_of_mem M ρ (v ρ).2
      have hd (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V ρ) :
          ∃ z : M.sm ρ, (z : M.H ρ) = dRep (M.rep ρ) X (v ρ : M.H ρ) ∧
            Rder R.θ V ρ X (T v) = T (Function.update v ρ z) := by
        have hH := GlobalTheory.SmoothAutCheck.gramAt_herm V ρ
        have hU := GlobalTheory.SmoothAutCheck.gramAt_unit V ρ
        have hRep := (GlobalTheory.HolDict.ModelRep.model_rep D V _ M ρ).2.1
        obtain ⟨hOrbit, -, hDeriv⟩ :=
          GlobalTheory.T.smoothVectors_unitaryRep_stable_conj_skewAdjoint _ _ _ _ hH hU hRep _ hs
        refine ⟨⟨_, Submodule.subset_span (hDeriv X hX).1⟩, rfl, ?_⟩
        funext x
        obtain ⟨ℓ, hℓ, hℓT⟩ := hTm.cont ρ v x
        have hDerivAt :=
          GlobalTheory.T.hasDerivAt_sobolevContinuous_orbit _ _ _ _ hH hU hRep _ hs ℓ hℓ X hX
        rw [← hℓT]
        have e : (fun t : ℝ => T v (x * oneP R.θ V ρ X t)) =
            fun t : ℝ => ℓ (M.rep ρ (NormedSpace.exp (t • X)) (v ρ : M.H ρ)) := by
          funext t
          have hg := GlobalTheory.SmoothAutCheck.exp_mem_UH hU hX t
          let z : M.sm ρ := ⟨_, Submodule.subset_span (hOrbit _ hg)⟩
          have hEquiv := congrFun (hTm.equiv ρ _ hg v z rfl) x
          exact ((hℓT z).trans hEquiv).symm
        show deriv (fun t : ℝ => T v (x * oneP R.θ V ρ X t)) 0 = _
        rw [e]
        exact hDerivAt.deriv
      have hs' := smoothVec_conj (σ := M.σ ρ) hFrame hGram hs
      set Z := (M.fr ρ)⁻¹ * Matrix.single a b 1 * M.fr ρ with hZ
      obtain ⟨hX, hY⟩ := GlobalTheory.SmoothAutCheck.parts_mem V ρ Z
      have hXY := GlobalTheory.SmoothAutCheck.parts_sum V ρ Z
      unfold RderC
      generalize (1 / 2 : ℂ) • (Z + conjAt V ρ Z) = X at hX hXY ⊢
      generalize (1 / (2 * Complex.I)) • (Z - conjAt V ρ Z) = Y at hY hXY ⊢
      obtain ⟨z, hz, ez⟩ := hd X hX
      obtain ⟨z', hz', ez'⟩ := hd Y hY
      have hX' := lie_conj hFrame hGram hX
      have hY' := lie_conj hFrame hGram hY
      have hE : M.fr ρ * X * (M.fr ρ)⁻¹ + Complex.I • (M.fr ρ * Y * (M.fr ρ)⁻¹) =
          Matrix.single a b 1 := by
        rw [← conj_cancel hFrame (Matrix.single a b 1), ← hZ, ← hXY]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
      have key : dRep (M.σ ρ) (M.fr ρ * X * (M.fr ρ)⁻¹) (v ρ : M.H ρ) +
          Complex.I • dRep (M.σ ρ) (M.fr ρ * Y * (M.fr ρ)⁻¹) (v ρ : M.H ρ) = 0 := by
        rcases hab with h | h | h
        · exact GlobalTheory.T.extremal_lowestKType_killed_compact_roots _ _ _ _ _
            (M.ds ρ).2.2.1 _ hlow' hs' hwt a b (Or.inl h) _ hX' _ hY' hE
        · exact GlobalTheory.T.extremal_lowestKType_killed_compact_roots _ _ _ _ _
            (M.ds ρ).2.2.1 _ hlow' hs' hwt a b (Or.inr h) _ hX' _ hY' hE
        · exact GlobalTheory.T.lowestKType_killed_by_negative_noncompact_roots _ _ _ _ _ p true
            (hε ρ) (M.enum ρ).1 (M.ds ρ) _ hlow' hs' a b h.1 h.2 _ hX' _ hY' hE
      have h0 : z + Complex.I • z' = 0 := by
        apply Subtype.ext
        show (z : M.H ρ) + Complex.I • (z' : M.H ρ) = 0
        rw [hz, hz', ← key, ← dRep_conj hFrame, ← dRep_conj hFrame]
        rfl
      have hSmul : T (Function.update v ρ (Complex.I • z')) =
          Complex.I • T (Function.update v ρ z') := by
        simpa only [RingHom.id_apply] using T.map_update_smul v ρ Complex.I z'
      rw [ez, ez', ← hSmul, ← T.map_update_add v ρ z (Complex.I • z'), h0, T.map_update_zero]
    · have hK := Formalism.IndefR.FWT.diag_mem (ε := M.ε ρ) s
      have hg := GlobalTheory.HolDict.ModelRep.conj_mem_inv hFrame hGram (kset_uj hK)
      have h := hTm.equiv ρ _ hg v
        (Complex.exp (((∑ a, extWt M ρ a * s a : ℝ) : ℂ) * Complex.I) • v ρ) (by
          unfold DSModel.rep
          rw [conj_cancel hFrame, hwt s hK]
          rfl)
      rw [T.map_update_smul, Function.update_eq_self] at h
      exact (congrFun h g).symm
  have hπ : ∀ a : Fin (Wc D i).rank, revPos p (revPos p a) = a := revPos_revPos p
  have hinv : ∀ ρ, ((onb (R.MW i (sg0 D A)) ρ))⁻¹ = (R.MW i (sg0 D A)).fr ρ := fun ρ =>
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 ((R.MW i (sg0 D A)).fr_unit ρ))
  refine ⟨⟨(hTm.aut _).smooth, fun ρ c d hdc => ?_⟩, fun ρ s => ?_⟩
  · have e : revB p (onb (R.MW i (sg0 D A))) ρ * Matrix.single c d 1 * (revB p (onb (R.MW i (sg0 D A))) ρ)⁻¹ =
        ((R.MW i (sg0 D A)).fr ρ)⁻¹ * Matrix.single (revPos p c) (revPos p d) 1 * (R.MW i (sg0 D A)).fr ρ := by
      show (onb (R.MW i (sg0 D A)) ρ).submatrix id (revPos p) * _ * ((onb (R.MW i (sg0 D A)) ρ).submatrix id (revPos p))⁻¹ = _
      rw [conj_submatrix hπ, perm_single_perm hπ, hinv]
      rfl
    rw [e]
    apply (KW ρ).1
    rw [hεd ρ]
    exact killPair_rev hpn hdc
  · set l : ℂ := Complex.exp (((∑ a, extWt (R.MW i (sg0 D A)) ρ a * s (revPos p a) : ℝ) : ℂ) * Complex.I) with hl
    have e : revB p (onb (R.MW i (sg0 D A))) ρ * Matrix.diagonal (fun a => Complex.exp ((s a : ℂ) * Complex.I)) *
        (revB p (onb (R.MW i (sg0 D A))) ρ)⁻¹ =
        ((R.MW i (sg0 D A)).fr ρ)⁻¹ * Matrix.diagonal (fun a => Complex.exp ((s (revPos p a) : ℂ) * Complex.I)) *
          (R.MW i (sg0 D A)).fr ρ := by
      show (onb (R.MW i (sg0 D A)) ρ).submatrix id (revPos p) * _ * ((onb (R.MW i (sg0 D A)) ρ).submatrix id (revPos p))⁻¹ = _
      rw [conj_submatrix hπ, perm_diag_perm hπ, hinv]
      rfl
    have htor : torAt R.θ (Wc D i) (revB p (onb (R.MW i (sg0 D A)))) ρ s =
        atTau R.θ (Wc D i) ρ (((R.MW i (sg0 D A)).fr ρ)⁻¹ *
          Matrix.diagonal (fun a => Complex.exp ((s (revPos p a) : ℂ) * Complex.I)) * (R.MW i (sg0 D A)).fr ρ) := by
      unfold torAt; rw [e]
    refine ⟨l, ?_, fun g => ?_⟩
    · have hK := Formalism.IndefR.FWT.diag_mem (ε := (R.MW i (sg0 D A)).ε ρ) (fun a => s (revPos p a))
      obtain ⟨-, -, hwt⟩ := hext ρ
      have h2 := (hP.ioP i t).2.1 ρ _ hK u (l • u ρ) (by
        show l • (((u ρ : (R.MW i (sg0 D A)).sm ρ)) : (R.MW i (sg0 D A)).H ρ) = _
        rw [hwt _ hK]) w
      rw [htor, h2, MultilinearMap.map_update_smul, Function.update_eq_self, map_smul, LinearMap.smul_apply]
      unfold RealDat.ptP
      exact map_smul _ _ _
    · rw [htor]
      exact (KW ρ).2 _ g

end GlobalTheory.ExtFock
