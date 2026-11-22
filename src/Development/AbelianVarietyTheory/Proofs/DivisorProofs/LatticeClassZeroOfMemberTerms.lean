module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFramedPointLiesOverTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqAdicSumAtImageOfZeroPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointLiesOverAfterFieldExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep.TermsLabel

theorem yy_zero_of_terms : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (T : X → C → V), 𝔪.Terms x₀ lab T → ∀ c, 𝔪.YY (lab c) 0 := by
  intro I X₁ z₁ act x₀ V _ _ _ ev X _ t δ 𝔪 C lab T hT c
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, -, hw₀, -, hg, -⟩ := hT
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hB := 𝔪.D.tau_bimult
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    have := X₁.S.r_pos; have := X₁.S.N_ge
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨⟨o, ho₁, ho₂⟩, hwc, hov⟩ := hg c
  letI := GlobalTheory.TorusExt.gtGroup 𝔪.D.toPre (FractionRing V)
  letI := GlobalTheory.TorusExt.gtGroup 𝔪.D.toPre (AlgebraicClosure (FractionRing V))
  have hkg : (X₁.S.r * X₁.S.N) • g' c = 0 :=
    ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 ho₁).symm.trans ((GlobalTheory.TorusExt.isZero_iff_eq _).1 ho₂)
  set gb := GlobalTheory.TorusExt.gtExt 𝔪.D.toPre (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)))
    (RingHom.comp_id _) (g' c) with hgb
  have hkgb : (X₁.S.r * X₁.S.N) • gb = 0 := by
    rw [hgb, ← map_nsmul, hkg, map_zero]

  have hi : GtPtF.IsIota 0 (0 : GtPtF 𝔪.D.toPre (AlgebraicClosure (FractionRing V))) := by
    have hz := (GlobalTheory.TorusExt.isZero_iff_eq (0 : GtPtF 𝔪.D.toPre (AlgebraicClosure (FractionRing V)))).2 rfl
    obtain ⟨hb, hv⟩ := (GlobalTheory.TorusExt.isZero_iff_val _).1 hz
    refine (GlobalTheory.TorusExt.isIota_iff_val 0 _).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩
    have C : IsCub (DVR.th 𝔪.D.toPre (T := TF (R := V) (AlgebraicClosure (FractionRing V))) y J) := isCub_cubV 𝔪.D.toPre.cub hJ
    have tt := tau_mul (𝟙 (TF (R := V) (AlgebraicClosure (FractionRing V)))) hJ hB 0 0 χ
    rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at tt
    exact (hv χ y J hJ).trans (mul_eq_left.1 tt.symm).symm
  let p : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) :=
    ⟨0, gb, 0, (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 hkgb.symm, hi⟩
  let xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A :=
    GlobalTheory.TorsionExt.fieldMap (FractionRing V) (AlgebraicClosure (FractionRing V)) ≫ x (lab c)
  obtain ⟨wb, frb, hwb, hfrb, hlb⟩ := GlobalTheory.T.torusExtension_point_liesOver_after_field_extension V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U (AlgebraicClosure (FractionRing V)) w₀
    hw₀ (g' c) (w c) (x (lab c)) (fr (lab c)) hwc (hfr _).1 hov xb rfl

  obtain ⟨f', f₁, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) hk
  have hq := (f₁ p (f' p)).2 rfl
  obtain ⟨w', fr', hw', hfr', hl'⟩ := GlobalTheory.Poinc.Tors.ValPair.liesOver_of_qkToAkU V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U (AlgebraicClosure (FractionRing V))
    w₀ hw₀ _ hk p (f' p) rfl hq

  have e := GlobalTheory.Poinc.Tors.OneOver.eq_of_liesOver hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U (AlgebraicClosure (FractionRing V)) w₀ hw₀ p.g wb w' xb
    (f' p) frb fr' hwb hw' hfrb hfr' hlb hl'
  refine ⟨p, xb, (map_zero 𝔪.e₈).symm, e ▸ hq, ?_⟩
  have e₁ : spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ spMap 𝔪.yK =
      spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) :=
    (Spec.map_comp (CommRingCat.ofHom 𝔪.yK) (CommRingCat.ofHom (algebraMap _ _))).symm
  rw [← e₁, Category.assoc, ← hx (lab c)]
  rfl

end GlobalTheory.GSep.TermsLabel
