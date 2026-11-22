module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneParamDualListSumAbsTwistSpecial
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligneParam_dual_listSum_absTwist_special : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ l : List (WD h), (sumList l).lpDual = sumList (l.map WD.lpDual)) ∧ (∀ (y : WD h) (s : ℝ), (y.lpTw s).lpDual = y.lpDual.lpTw (-s)) ∧ ∀ (y : WD h) (n : ℕ), (y.lpChar (WD.lpSp (h := h) n)).lpDual = y.lpDual.lpChar (WD.lpSp (h := h) n) := by
  intro E Ω _ _ _ _ _ A w h
  have dual_sp (y : WD h) (n : ℕ) :
      (y.lpChar (WD.lpSp (h := h) n)).lpDual = y.lpDual.lpChar (WD.lpSp (h := h) n) := by
    induction y using WD.ind with
    | hP m a =>
      rw [WD.lpSp, WD.lpChar_mk, WD.lpDual_mk, WD.lpDual_mk, WD.lpChar_mk]
      exact WD.sound ((GlobalTheory.WDDual.iso_tensor_dual a (WDRep.sp (h := h) n)).symm.trans
        ((WDRep.Iso.refl a.dual).tensor (GlobalTheory.WDDual.iso_sp_dual (h := h) n)))
  exact ⟨GlobalTheory.WDDual.WDClass.lpDual_sumList, GlobalTheory.WDDual.WDClass.lpDual_lpTw,
    dual_sp⟩
