module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyDoubleCosetBesselBoundOfGap
public import Formalism.SharpRestriction.CuspSpanNormBounds.NearParameterGap
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselFunctionalOfSigmaContinuity
public import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecLowPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecInfPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.Admissible
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.GgExistsAddCharNeOne

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeCS3dClosed

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BridgeLemma₄


variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in
theorem inputs_of (hDI : Formalism.FourierDecayAlt.ThreeDimData.DecInf) (hJ : PI.BesselMapUniq.BesselMapUniq) : Formalism.FourierDecayAlt.ThreeDimData.Inputs := by
  have hK := Formalism.L2.SG.LitS.kFinSmooth_pi Formalism.L2.SG.Pf.k_finite_smooth
  refine ⟨?_, hDI, hK, hJ⟩
  intro k r _ ε lam h H _ _ _ σ hlam hDS hgap hh P hP w₁ w₂ h₁ h₂
  have hSmooth (w : H) (hw : w ∈ PI.UpqRep.lowKSub ε lam (fun g => σ (P⁻¹ * g * P))) :
      w ∈ smoothVecs (k := k) (r := r) σ := by
    obtain ⟨V, hfd, hwV, hstable⟩ := DoubleDerivativeSmoothness.kfin_of_mem_lowKSub hw
    exact hK k r ε lam H σ hlam hDS w
      ⟨V, hfd, hwV, LowestKTypeMultiplicity.kstable_Hpk hP hstable⟩

  let a := Formalism.FourierDecayAlt.ThreeDimData.aOf r h
  let m := ⌈a⌉₊
  have hn : 1 ≤ 2 * r + k + 1 := by omega
  have hnReal : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast hn
  have hnCube : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := one_le_pow₀ hnReal
  have hh0 : 0 ≤ h := le_trans (by positivity) hh
  have hsqrt : 1 ≤ Real.sqrt (2 * ((r : ℝ) + 1)) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) r]
  have ha0 : 0 ≤ a := div_nonneg hh0 (by positivity)
  have ha8 : a ≤ h / 8 := by
    dsimp [a, Formalism.FourierDecayAlt.ThreeDimData.aOf]
    exact div_le_div_of_nonneg_left hh0 (by norm_num) (by linarith)
  have ham : a ≤ (m : ℝ) := Nat.le_ceil a
  have hm : ReciprocityTheory.ChartRestriction.DS.thrStar ε + (m : ℝ) < h := by
    have hmUpper : (m : ℝ) < a + 1 := Nat.ceil_lt_add_one ha0
    linarith [Formalism.L2.SG.BesselDiscreteSeries.thrStar_le hn ε]
  obtain ⟨C, Ws, -, hC⟩ :=
    ReciprocityTheory.ChartRestriction.DS.DecInf.decSm hlam hgap m hm hDS
  let B := C * (Ws.map fun W => ‖dsigW (k := k) (r := r) σ W w₁‖).sum *
    (Ws.map fun W => ‖dsigW (k := k) (r := r) σ W w₂‖).sum
  refine ⟨B, fun x hx => ?_⟩
  let g := Formalism.FourierDecayAlt.B.gN x
  have hg : 1 ≤ g := ((Formalism.FourierDecayAlt.P.norm_inverse_bound k r).2 x hx).2
  have hg0 : 0 < g := lt_of_lt_of_le zero_lt_one hg
  have hb : g ^ m * ‖inner ℂ w₂ (σ x w₁)‖ ≤ B :=
    hC w₁ (hSmooth w₁ h₁) w₂ (hSmooth w₂ h₂) x hx
  have hB : 0 ≤ B := le_trans (mul_nonneg (pow_nonneg hg0.le _) (norm_nonneg _)) hb
  have hpow : (g ^ m)⁻¹ ≤ g ^ (-a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hg0.le]
    exact Real.rpow_le_rpow_of_exponent_le hg (neg_le_neg ham)
  calc
    ‖inner ℂ w₂ (σ x w₁)‖ ≤ B * (g ^ m)⁻¹ := by
      rw [le_mul_inv_iff₀ (pow_pos hg0 _), mul_comm]
      exact hb
    _ ≤ B * g ^ (-a) := mul_le_mul_of_nonneg_left hpow hB

end Formalism.MainNotions.BridgeCS3dClosed
