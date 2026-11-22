module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartsOfUpre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCompactificationIsModelOfChartsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleChartUnitaryBoundaryPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalCompactificationSmoothSncBoundaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncToroidalGenericBoundaryOfSncBoundary
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChartJoin

theorem rigidForFan_of_uStB : UStB → GlobalTheory.RigChart.RigidForFan := by
  intro hU E _ _ _ H Dw hpq φ hpol hnsi l Xo c
  obtain ⟨Z, zs, i, OZ, N, d, J, S, π, j, BD, hUP, hSep⟩ := hU E H Dw hpq φ hpol hnsi l Xo c
  obtain ⟨⟨-, -, -, -, -, hOZ, -⟩, ⟨hN, hdet⟩, -, ⟨hd, hJ, -⟩, ⟨-, -, hj, -, hji, -, hBD, -⟩, k₀, hamp⟩ := id hUP
  haveI := hj
  have hpre := GlobalTheory.T.exists_tripleChart_unitary_boundary_point Xo c φ hpq hpol hnsi zs i OZ N d J π j BD hUP hSep
  obtain ⟨Y, ε, hYj, hYs, hsab⟩ := GlobalTheory.T.unitary_compactification_isModel_of_charts Xo c φ hpq hpol hnsi zs i OZ N d J π j BD hUP hSep hpre
  obtain ⟨hsm, hsnc⟩ := GlobalTheory.T.toroidalCompactification_smooth_snc_boundary Xo c φ hpq hpol hnsi zs i OZ N d J π j BD hUP hSep hpre
  have hch := fun x hx => GlobalTheory.UChartOf.charts_of_upre Y ε hYj hsab hpre x hx
  have hYi : Y.j ≫ ε.hom ≫ π = i := by rw [← Category.assoc, hYj, hji]
  refine ⟨Y, BD.pull ε.hom (BD.keepsRegular_of_flat _), d, N * max k₀ 1, hd, ?_, ?_, ?_, ?_, fun x hx => (hch x hx).1, ?_,
    fun x hx _ => (hch x hx).2⟩
  · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  ·
    have h2 : genStr Y ≫ spMap (RingHom.id c.F) = genStr Y := by
      rw [show spMap (RingHom.id c.F) = 𝟙 (Sp c.F) by simp [spMap]]
      exact Category.comp_id _
    have e : genStr Y = (genι Y ≫ ε.hom) ≫ (π ≫ zs) := by
      rw [← h2, ← pullback.condition]
      exact (congrArg (genι Y ≫ ·) hYs).trans (by simp only [Category.assoc])
    rw [e]
    have := smoothOfRelativeDimension_comp (n := 0) (m := Dw.dim) (genι Y ≫ ε.hom) (π ≫ zs)
    rwa [zero_add] at this
  ·
    refine GlobalTheory.SncIso.snc_vanishingIdeal_of_isIso (genι Y ≫ ε.hom) j.opensRange.compl (genBd Y) (fun a => ?_) hsnc
    rw [mem_genBd]
    show a ∉ Set.range Y.jQ ↔ (genι Y ≫ ε.hom) a ∉ Set.range j
    refine not_congr ⟨?_, ?_⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [← hYj]; rfl⟩
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      have h1 : (genι Y ≫ ε.hom) (Y.jQ z) = (genι Y ≫ ε.hom) a := by
        rw [← hz, ← hYj]; rfl
      rw [← GlobalTheory.UChartOf.inv_apply_self (genι Y ≫ ε.hom) (Y.jQ z), h1, GlobalTheory.UChartOf.inv_apply_self]
  ·
    intro x hx hab
    rw [EffCartierData.idealSheaf_pull, hBD, Scheme.IdealSheafData.support_comap,
      Scheme.IdealSheafData.support_comap] at hx
    obtain ⟨g, rfl⟩ : ∃ g : gen Y, genι Y g = x := ⟨inv (genι Y) x, by
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
    have hg : g ∈ Set.range Y.jQ := by rw [← Y.ab_gen]; exact hab
    obtain ⟨z, rfl⟩ := hg
    refine hJ _ hx ⟨z, ?_⟩
    rw [← hYi]
    rfl
  ·
    intro hL
    have hk : k₀ ≤ max k₀ 1 := le_max_left _ _
    have isLB {X : Scheme} (D : EffCartierData X) : D.lb.IsLB := by
      refine { cover := D.cover, g_self := ?_, cocycle := ?_ }
      · intro i
        exact Units.ext (D.eq_trans_on i i le_rfl le_rfl (c := 1) (_root_.one_mul _).symm).symm
      · intro i j k
        have hi : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U i := inf_le_left.trans inf_le_left
        have hj : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U j := inf_le_left.trans inf_le_right
        have hk : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U k := inf_le_right
        refine Units.ext (D.eq_trans_on i k hi hk ?_)
        rw [D.trans_spec_on i j hi hj, D.trans_spec_on j k hj hk, ← _root_.mul_assoc]
        rfl
    have hBL := isLB BD
    have hL' := isLB (BD.pull ε.hom (BD.keepsRegular_of_flat _))
    have hA := (hamp _ hk).pull_of_isAffineHom ε.hom
    have hAS : (CechPic.tens (lbPow (OZ.pull π) (max k₀ 1)) (CechPic.dual BD.lb)).IsLB :=
      CechPic.isLB_tens (isLB_lbPow (LB.isLB_pull hOZ π) _) (CechPic.isLB_dual hBL)
    have hP : (GlobalTheory.TorRef.polOf Y (N * max k₀ 1) (BD.pull ε.hom (BD.keepsRegular_of_flat _))).IsLB :=
      CechPic.isLB_tens (isLB_lbPow hL _) (CechPic.isLB_dual hL')
    refine hA.of_lbIso hP ((CechPic.cls_eq_iff hP (LB.isLB_pull hAS ε.hom)).1 ?_)
    have e1 : CechPic.cls _ (LB.isLB_pull hOZ (ε.hom ≫ π)) = N • CechPic.cls _ hL := by
      rw [(CechPic.cls_eq_iff _ (isLB_lbPow hL N)).2 (hdet Y (ε.hom ≫ π) hYi hL), CechPic.cls_lbPow hL]
    have e2 : CechPic.cls _ hL' = CechPic.pull ε.hom (CechPic.cls _ hBL) := by
      rw [(CechPic.cls_eq_iff _ (LB.isLB_pull hBL _)).2 (BD.lbIso_pull _ _), CechPic.cls_pull hBL]
    rw [CechPic.cls_pull hOZ, CechPic.pull_comp] at e1
    refine (CechPic.cls_tens (isLB_lbPow hL _) (CechPic.isLB_dual hL') hP).trans ?_
    rw [CechPic.cls_pull hAS ε.hom,
      CechPic.cls_tens (isLB_lbPow (LB.isLB_pull hOZ π) _) (CechPic.isLB_dual hBL),
      CechPic.cls_lbPow hL, CechPic.cls_lbPow (LB.isLB_pull hOZ π), CechPic.cls_dual hL', CechPic.cls_dual hBL,
      CechPic.cls_pull hOZ π, e2, map_add, map_nsmul, map_neg, e1, mul_nsmul]

end GlobalTheory.UChartJoin
