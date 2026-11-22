module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
public import Development.AbelianVarietyTheory.Definitions.Divisors.VdmSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeSplitsCompactNoncompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointDetOnCompactTorus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumShiftHolds

@[expose] public section

section
open GlobalTheory.PsCo.PcEG

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open GlobalTheory.HCChar (dsChar)

namespace GlobalTheory.PsCo.PcEF

namespace WeylCompactTorusIdentity

theorem alg {W S C M s p x : ℂ} (hs : s * s = 1) (hp : p * p = 1) (hW : W ≠ 0) (hM : M ≠ 0) (hs0 : s ≠ 0)
    (hx : W * x = S * C) : s * x = p * S / (W * (s * M)) * (p * M * C) := by
  have hden : W * (s * M) ≠ 0 := mul_ne_zero hW (mul_ne_zero hs0 hM)
  rw [div_mul_eq_mul_div, eq_div_iff hden]
  linear_combination (M * s * s) * hx + (M * S * C) * hs - (M * S * C) * hp

theorem neg_one_pow_mul_self (k : ℕ) : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

end WeylCompactTorusIdentity


open WeylCompactTorusIdentity in
theorem weylFormulaCompactTorusIdentity_of_ingredients : VdmSplit → PhysTor → NumShift → TorusId := by
  intro hV hP hN n ε lam Λ m hm hΛ θ hinj x hx
  have ht0 : ∀ a, tor θ a ≠ 0 := fun a => Complex.exp_ne_zero _
  obtain ⟨hPD, -⟩ := hP n ε θ
  have hVd := hV n ε (tor θ)
  have hx' : ReciprocityTheory.ChartRestriction.TR.Weyl.wdenK ε (tor θ) * x =
      (∑ w ∈ GlobalTheory.HCChar.compactWeyl ε,
        ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ a, tor θ a ^ m (w.symm a)) *
        ∏ a, tor θ a ^ (-(if ε a then 0 else (pOf ε : ℤ))) := by
    rw [hx]
    exact (congrArg (fun μ => ReciprocityTheory.ChartRestriction.TR.Weyl.numK ε μ (tor θ)) (funext hΛ)).trans
      (hN n ε m (fun b : Bool => if b then (0 : ℤ) else (pOf ε : ℤ)) (tor θ) ht0)
  have hV0 : (∏ a, ∏ b ∈ Finset.Ioi a, (tor θ a - tor θ b)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun a _ => Finset.prod_ne_zero_iff.mpr (fun b hb => ?_))
    exact sub_ne_zero.mpr (fun h => (Finset.mem_Ioi.mp hb).ne (hinj h))
  rw [hVd] at hV0
  rw [GlobalTheory.HCChar.dsChar_eq ε hm θ, hPD, hVd]
  exact alg (neg_one_pow_mul_self _) (neg_one_pow_mul_self _)
    (left_ne_zero_of_mul hV0) (right_ne_zero_of_mul (right_ne_zero_of_mul hV0))
    (pow_ne_zero _ (by norm_num)) hx'

end GlobalTheory.PsCo.PcEF

end
end

namespace GlobalTheory.PsCo.PcEF
open GlobalTheory.PsCo.PcEG

theorem torusId_full : TorusId := weylFormulaCompactTorusIdentity_of_ingredients vandermonde_splits_compactNoncompact adjointDet_onCompactTorus numShift_holds

end GlobalTheory.PsCo.PcEF
