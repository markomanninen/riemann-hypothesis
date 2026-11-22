module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.OneScalar

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem infGL_scalar {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ} (u : (Rinf E)ˣ) :
    infGL E n (GeneralLinearGroup.scalar (Fin n) u) = GeneralLinearGroup.scalar (Fin n) (TR.infId E u) := by
  have h1 : pInf E (TR.infId E u).val = u.val := by
    change pInf E (1 - sInf E 1 + sInf E _) = _
    have h : ∀ x, pInf E (sInf E x) = x := fun x => (TR.infEq E).symm_apply_apply x
    simp [h]
  have h2 : pFin E (TR.infId E u).val = 1 := by
    change (1 : Af E) - 0 + 0 = 1
    simp
  refine TR.ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]
  · rw [TR.pFin_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]

private theorem deriv_centre {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ} (φ : TR.Sm E n)
    (g : GA E n) :
    HasDerivAt (fun t : ℝ => φ.1 (g * GeneralLinearGroup.scalar (Fin n) (TR.infId E (TR.expU (t • (1 : Rinf E))))))
      ((TR.lie E n (oneL E n) φ).1 g) 0 := by
  have h := TR.hasDerivAt_curve φ g (fun t : ℝ => GeneralLinearGroup.scalar (Fin n) (TR.expU (t • (1 : Rinf E))))
    (oneL E n) (by simp [TR.expU_zero]) (by
      refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
      by_cases e : i = j
      · subst e
        simpa using Real.hasDerivAt_exp 0
      · simpa [Matrix.diagonal_apply, Matrix.one_apply, e] using hasDerivAt_const (0 : ℝ) (0 : ℝ))
  simp only [infGL_scalar] at h
  exact h

theorem UpperTheory.V.Af.Smo.cenSame :
    UpperTheory.V.Af.Smo.CentEq → UpperTheory.V.Af.Smo.SetUp → UpperTheory.V.Af.Smo.EigOfSat → UpperTheory.V.Af.Smo.CenSame := by
  intro hC hS hE E _ _ _ n π π' hs hc φ' hφ'
  obtain ⟨φ, hφ, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
  obtain ⟨S, B, hB, hk, hk'⟩ := hS E n π π' hs φ hφ φ' hφ'
  have key : ∀ ψ : TR.Sm E n, TR.IsCuspForm ψ → Continuous ψ.1 ∧ IsLeftInvariant ψ.1 := fun ψ hψ => by
    refine ⟨?_, hψ.1.left⟩
    have hp : Continuous (pInf E) := by
      have hc : Continuous (TR.infEq E).symm :=
        continuous_pi fun w =>
          (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp (continuous_apply w)
      exact hc.comp continuous_fst
    refine continuous_iff_continuousAt.2 fun g => ?_
    have hm : Continuous fun x : GA E n => g⁻¹ * x := continuous_const.mul continuous_id
    have hI : Continuous (Matrix.GeneralLinearGroup.map (pInf E) : GA E n → GL (Fin n) (Rinf E)) :=
      Continuous.units_map _ (continuous_id.matrix_map hp)
    have hFn : Continuous (Matrix.GeneralLinearGroup.map (pFin E) : GA E n → GL (Fin n) (Af E)) :=
      Continuous.units_map _ (continuous_id.matrix_map continuous_snd)
    have h1 : Continuous fun x : GA E n => toL (Matrix.GeneralLinearGroup.map (pInf E) (g⁻¹ * x)).val :=
      (Units.continuous_val (M := Matrix (Fin n) (Fin n) (Rinf E))).comp (hI.comp hm)
    have h2 : ContinuousAt (fun x : GA E n => chart ψ.1 g (toL (Matrix.GeneralLinearGroup.map (pInf E) (g⁻¹ * x)).val)) g :=
      ContinuousAt.comp (f := fun x : GA E n => toL (Matrix.GeneralLinearGroup.map (pInf E) (g⁻¹ * x)).val)
        (TR.contDiffAt_chart ψ.2 g (TR.val_mem_invSet _)).continuousAt h1.continuousAt
    refine h2.congr ?_
    have h3 : {x : GA E n | TR.finRep E n (Matrix.GeneralLinearGroup.map (pFin E) (g⁻¹ * x)) ψ = ψ} ∈ 𝓝 g :=
      (hψ.1.level.preimage (hFn.comp hm)).mem_nhds (by simp)
    filter_upwards [h3] with x hx
    rw [TR.chart_val]
    conv_lhs => rw [← hx]
    change ψ.1 (g * infGL E n _ * finGL E n _) = _
    rw [mul_assoc, TR.infGL_mul_finGL, mul_inv_cancel_left]
  have loc : ∀ w ∉ S, ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), InKS S (locGL E n w k) := by
    intro w hw k hkk
    refine ⟨fun x hx => GlobalTheory.CuspRep.pLoc_locGL_of_ne (show x ≠ w from fun e => hw (e ▸ hx)) _, fun x => ?_⟩
    by_cases e : x = w
    · subst e
      rw [GlobalTheory.CuspRep.pLoc_locGL]
      exact hkk
    · rw [GlobalTheory.CuspRep.pLoc_locGL_of_ne e]
      exact one_mem _
  have e := hC E n S B φ.1 φ'.1 (key _ (π.cusp _ hφ)).1 (key _ (π'.cusp _ hφ')).1 (key _ (π.cusp _ hφ)).2
    (key _ (π'.cusp _ hφ')).2 (fun w hw => ⟨hE E n π w _ (hB w hw).2.1 φ hφ fun g k h => hk g _ (loc w hw k h),
      hE E n π' w _ (hB w hw).2.2 φ' hφ' fun g k h => hk' g _ (loc w hw k h)⟩) hk hk'
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (Subtype.ext (funext h))
  refine Subtype.ext (funext fun g' => ?_)
  have d1 := (deriv_centre φ g).mul_const (φ'.1 g')
  have d2 := (deriv_centre φ' g').const_mul (φ.1 g)
  simp only [e _ g g'] at d1
  have d := d1.unique d2
  rw [hc φ hφ] at d
  exact (mul_eq_zero.1 (d.symm.trans (zero_mul _))).resolve_left hg
