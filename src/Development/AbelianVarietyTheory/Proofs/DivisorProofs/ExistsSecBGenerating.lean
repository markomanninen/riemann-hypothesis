module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAmpleTensorAmplePowProjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CechPic

namespace GlobalTheory.Mum

theorem exists_secB_generating : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R) (α : D.X),
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ (n : ℕ) (b : Fin n → D.SecB k α), ⨆ j, nonzeroLocus (b j) = ⊤ := by
  intro R _ _ _ D α
  have hL := D.P.isLB
  have := D.P.isAb.proper
  have hA : IsAmpleLB D.P.L := (relAmple_iff_isAmpleLB_of_isAffine D.P.A hL).1 D.P.ample
  have hN : ∀ k, (LB.LinComb D.P.L (D.famφB α) (DegPre.famε k)).IsLB := fun k => LB.isLB_linComb hL _ _
  obtain ⟨k₀, hk⟩ := eventually_atTop.1 (hA.eventually_isGenerated_tens_lbPow (hN 0))
  refine ⟨k₀, fun k h => ?_⟩
  have hP := isLB_lbPow hL k
  have hT := isLB_tens (hN 0) hP
  refine (hk k h).of_lbIso (hN k) (iso_of_chart hT ⟨fun j => (j, fun _ => j 0), fun _ _ hj => ⟨hj, ?_⟩, ?_⟩)
  · exact Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hj 0
  · intro y p q hp hq
    set_option maxHeartbeats 200000 in
    refine (gm_linComb D.P.L (D.famφB α) (DegPre.famε k) (𝟙 _) y p q hp hq).trans ?_
    refine ((gm_tens (LB.LinComb D.P.L (D.famφB α) (DegPre.famε 0)) (lbPow D.P.L k) (𝟙 _) y (p, fun _ => p 0) (q, fun _ => q 0) ⟨hp, Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hp 0⟩ ⟨hq, Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hq 0⟩).trans ?_).symm
    refine (congrArg₂ (· * ·) (gm_linComb D.P.L (D.famφB α) (DegPre.famε 0) (𝟙 _) y p q hp hq) (gm_linComb D.P.L (fun _ : PUnit => 𝟙 _) (fun _ => (k : ℤ)) (𝟙 _) y (fun _ => p 0) (fun _ => q 0) (Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hp 0) (Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hq 0))).trans ?_
    simp only [Fin.prod_univ_four, Fintype.prod_unique, DegPre.famφB, DegPre.famε, Matrix.cons_val, Category.id_comp, zpow_sub, zpow_one]
    simp only [Nat.cast_zero, zpow_zero, one_mul]
    ac_rfl

end GlobalTheory.Mum
