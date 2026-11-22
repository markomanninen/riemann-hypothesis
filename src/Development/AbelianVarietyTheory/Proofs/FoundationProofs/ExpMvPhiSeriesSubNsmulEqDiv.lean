module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpMvNegLogMvMul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralSubst

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.ExpLogShift

open MvPowerSeries

theorem expMv_phAt_sub_nsmul : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (h : PowerSeries ℂ_[p]) (n : ℕ), PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1 → PowerSeries.constantCoeff h = 0 → MvPowerSeries.constantCoeff ((g.phAt h : MvPowerSeries Unit ℂ_[p]) - MvPowerSeries.C (n : ℂ_[p]) * g.phAt (GL3Theta.Xv ())) = 0 ∧ expMv ((g.phAt h : MvPowerSeries Unit ℂ_[p]) - MvPowerSeries.C (n : ℂ_[p]) * g.phAt (GL3Theta.Xv ())) = ((PowerSeries.subst h (ePhi1 g.lam g.abelian₂ g.C g.wq))⁻¹ * ePhi1 g.lam g.abelian₂ g.C g.wq ^ n : PowerSeries ℂ_[p]) := by
  intro p _ g h n hE hh
  have exp_add {f g : MvPowerSeries Unit ℂ_[p]} (hf : constantCoeff f = 0)
      (hg : constantCoeff g = 0) : expMv (f + g) = expMv f * expMv g := by
    rw [GlobalTheory.ExpLogMv.expMv_eq_subst hf, GlobalTheory.ExpLogMv.expMv_eq_subst hg,
      GlobalTheory.ExpLogMv.expMv_eq_subst (by simp [hf, hg])]
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add hf hg
  have exp_zero : expMv (0 : MvPowerSeries Unit ℂ_[p]) = 1 := by
    rw [GlobalTheory.ExpLogMv.expMv_eq_subst (by simp)]
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero
  have cc_ph : PowerSeries.constantCoeff g.ph = 0 := by
    have ht := (GlobalTheory.ExpLogMv.expMv_neg_logMv_mul p Unit _ hE).1
    show constantCoeff (-GL3Theta.logMv (ePhi1 g.lam g.abelian₂ g.C g.wq)) = 0
    rw [map_neg, ht, neg_zero]
  have cc_phAt {y : MvPowerSeries Unit ℂ_[p]} (hy : constantCoeff y = 0) :
      constantCoeff (g.phAt y) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hy _ cc_ph
  have exp_sum {ι : Type} (s : Finset ι) {f : ι → MvPowerSeries Unit ℂ_[p]}
      (hf : ∀ i, constantCoeff (f i) = 0) : expMv (∑ i ∈ s, f i) = ∏ i ∈ s, expMv (f i) := by
    induction s using Finset.induction_on with
    | empty => simpa using exp_zero
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, exp_add (hf i) (by simp [map_sum, hf]), ih]
  have subst_exp {a : Unit → MvPowerSeries Unit ℂ_[p]} (ha : ∀ i, constantCoeff (a i) = 0)
      {f : MvPowerSeries Unit ℂ_[p]} (hf : constantCoeff f = 0) : subst a (expMv f) = expMv (subst a f) := by
    have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
    rw [GlobalTheory.ExpLogMv.expMv_eq_subst hf, GlobalTheory.ExpLogMv.expMv_eq_subst (constantCoeff_subst_eq_zero hs ha hf)]
    rw [PowerSeries.subst_def, subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hf).const hs]
    rfl
  have inv_ePhi1 {y : MvPowerSeries Unit ℂ_[p]} (hy : constantCoeff y = 0) :
      (PowerSeries.subst y (ePhi1 g.lam g.abelian₂ g.C g.wq))⁻¹ = expMv (g.phAt y) := by
    have hs : HasSubst (fun _ : Unit => y) := hasSubst_of_constantCoeff_zero fun _ => hy
    have ht := congrArg (subst (fun _ : Unit => y)) (GlobalTheory.ExpLogMv.expMv_neg_logMv_mul p Unit _ hE).2
    rw [subst_mul hs, subst_exp (f := -GL3Theta.logMv (ePhi1 g.lam g.abelian₂ g.C g.wq)) (fun _ => hy) cc_ph, ← coe_substAlgHom hs (R := ℂ_[p]), map_one,
      coe_substAlgHom] at ht
    have h1 : constantCoeff (PowerSeries.subst y (ePhi1 g.lam g.abelian₂ g.C g.wq)) ≠ 0 := by
      rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_psubst hy, hE]; exact one_ne_zero
    rw [MvPowerSeries.inv_eq_iff_mul_eq_one h1]
    exact ht
  have hh' : MvPowerSeries.constantCoeff (h : MvPowerSeries Unit ℂ_[p]) = 0 := hh
  have hX : MvPowerSeries.constantCoeff (GL3Theta.Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := by
    simp [GL3Theta.Xv]
  have ha : MvPowerSeries.constantCoeff (g.phAt (h : MvPowerSeries Unit ℂ_[p])) = 0 :=
    cc_phAt hh'
  have hb : MvPowerSeries.constantCoeff (g.phAt (GL3Theta.Xv () : MvPowerSeries Unit ℂ_[p])) = 0 :=
    cc_phAt hX
  refine ⟨by simp [map_sub, map_mul, ha, hb], ?_⟩
  set b : MvPowerSeries Unit ℂ_[p] := g.phAt (GL3Theta.Xv ()) with hbdef
  set F : PowerSeries ℂ_[p] := ePhi1 g.lam g.abelian₂ g.C g.wq with hF

  have hbph : b = (g.ph : MvPowerSeries Unit ℂ_[p]) := by
    show PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[p]) g.ph = g.ph
    rw [← PowerSeries.map_algebraMap_eq_subst_X]; simp

  have hbF : expMv b * (F : MvPowerSeries Unit ℂ_[p]) = 1 := by
    rw [hbph]; exact (GlobalTheory.ExpLogMv.expMv_neg_logMv_mul p Unit _ hE).2
  have hnb : MvPowerSeries.constantCoeff (-b) = 0 := by simp [hb]

  have hneg : expMv (-b) = (F : MvPowerSeries Unit ℂ_[p]) := by
    have h0 : expMv b * expMv (-b) = 1 := by
      rw [← exp_add hb hnb, add_neg_cancel, exp_zero]
    calc expMv (-b) = expMv (-b) * (expMv b * (F : MvPowerSeries Unit ℂ_[p])) := by rw [hbF, mul_one]
      _ = (expMv b * expMv (-b)) * F := by ring
      _ = F := by rw [h0, one_mul]
  have hsum : (g.phAt (h : MvPowerSeries Unit ℂ_[p])) - MvPowerSeries.C (n : ℂ_[p]) * b =
      g.phAt (h : MvPowerSeries Unit ℂ_[p]) + ∑ _i ∈ Finset.range n, -b := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_eq_add_neg, ← neg_mul]
    congr 1
    rw [neg_mul, mul_neg]
    congr 1
  have hsum0 : MvPowerSeries.constantCoeff (∑ _i ∈ Finset.range n, -b) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; simp [hb]
  rw [hsum, exp_add ha hsum0,
    exp_sum _ (fun _ => hnb), Finset.prod_const, Finset.card_range, hneg,
    ← inv_ePhi1 hh']

end GlobalTheory.ExpLogShift
