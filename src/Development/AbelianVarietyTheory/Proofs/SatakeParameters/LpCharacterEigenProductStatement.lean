module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharacterEigenProduct
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lp_character_eigen_product : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h) (l : ℕ) (σ : Weil h), ((x.lpChar (WD.lpSp (h := h) l)).eig σ).prod = ((x.eig σ).prod) ^ l := by
  intro E Ω _ _ _ _ _ A w h x l σ
  induction x using WD.ind with
  | hP n a =>
    rw [WD.lpSp, WD.lpChar_mk, WD.eig_mk, WD.eig_mk, WDRep.tensor_ρ, WDRep.sp_ρ,
      DetSp.prod_roots_charpoly, DetSp.prod_roots_charpoly, DetSp.det_map, DetSp.det_diagEnd,
      Finset.prod_zpow, ← Units.coe_prod, DetSp.prod_spEig, Units.val_one, one_zpow, one_pow, mul_one]
