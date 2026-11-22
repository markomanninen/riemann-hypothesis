module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

namespace GlobalTheory.CompHS

theorem nonempty_cartier_of_locally_principal : ∀ (Y : Scheme.{0}) (I : Y.IdealSheafData),
    (∀ y : Y, ∃ (W : Y.affineOpens) (a : Γ(Y, W.1)), y ∈ W.1 ∧ a ∈ nonZeroDivisors Γ(Y, W.1) ∧
      I.ideal W = Ideal.span {a}) → Nonempty (Cartier I) := by
  intro Y I h
  obtain ⟨D, hD⟩ := GlobalTheory.EffCartierData.exists_idealSheaf_eq (I := I) h
  have hLB : D.lb.IsLB := by
    refine { cover := D.cover, g_self := ?_, cocycle := ?_ }
    · intro i
      exact Units.ext (D.eq_trans_on i i le_rfl le_rfl (c := 1) (one_mul _).symm).symm
    · intro i j k
      have hi : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U i := inf_le_left.trans inf_le_left
      have hj : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U j := inf_le_left.trans inf_le_right
      have hk : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U k := inf_le_right
      refine Units.ext (D.eq_trans_on i k hi hk ?_)
      rw [D.trans_spec_on i j hi hj, D.trans_spec_on j k hj hk, ← mul_assoc]
      rfl
  refine ⟨{ P := D.lb, isLB := hLB, t := D.canonical, reg := fun i y hi => ?_, cut := ?_ }⟩
  · exact GlobalTheory.Cartier.isRegularFn_iff_germ.1 (D.regular i) y hi
  · refine ideal_ext_stalk fun y => ?_
    obtain ⟨i, hi⟩ := D.exists_mem y
    rw [stalkId_cutIdeal hLB _ i y hi, ← hD, D.stalkId_idealSheaf i y hi, Set.range_const]
    rfl

end GlobalTheory.CompHS
