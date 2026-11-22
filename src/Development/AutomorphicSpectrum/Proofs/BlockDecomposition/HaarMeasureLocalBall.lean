module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetOff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusProductFormulaTotallyReal

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

namespace GlobalTheory.CompanionTheory.Equi.BallVol

theorem measure_translate_ballV : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (k : ℕ) (a : Fv F v), lam ((fun z => z - a) ⁻¹' ballV v k) = ENNReal.ofReal (((Ideal.absNorm v.asIdeal : ℝ) ^ k)⁻¹) := by
  intro F _ _ v lam hlam k a
  obtain ⟨hHaar, h1⟩ := hlam
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : ProperSpace (Fv F v) := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : lam.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure lam
  have htr : (fun z => z - a) ⁻¹' ballV v k = (fun z => z + -a) ⁻¹' ballV v k := by
    simp only [sub_eq_add_neg]
  rw [htr, measure_preimage_add_right]
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v
  let ϖ : Fv F v := ((π : v.adicCompletion F) : Fv F v)
  have hvϖ : Valued.v ϖ = WithZero.exp (-1) := by
    rw [← hπ]; exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hvϖ
    exact WithZero.exp_ne_zero hvϖ.symm
  open Pointwise in
  have hball : ballV v k = (ϖ ^ k) • (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext z
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (pow_ne_zero k hϖ0)]
    simp only [ballV, Set.mem_ofPred_eq, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
      smul_eq_mul, map_mul, map_inv₀, map_pow, hvϖ]
    have hk : (WithZero.exp (-1 : ℤ)) ^ k = WithZero.exp (-(k : ℤ)) := by
      rw [← WithZero.exp_nsmul]; simp
    rw [hk, inv_mul_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), mul_one]
  rw [hball]
  have hu : IsUnit (ϖ ^ k) := (pow_ne_zero k hϖ0).isUnit
  open Pointwise in
  have key := distribHaarChar_mul lam hu.unit (v.adicCompletionIntegers F : Set (Fv F v))
  rw [Units.smul_def, IsUnit.unit_spec, h1, mul_one] at key
  rw [← key]
  open scoped Pointwise in
  have card_residue (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
      Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal := by
    obtain ⟨a, ha⟩ := GlobalTheory.HaarLatticeScale.exists_valued_eq_exp F v (-1)
    have ha1 : a ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact ((GlobalTheory.HaarLatticeScale.lt_one_iff_le_exp _).2 ha.le).le
    have h := (GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers F v).2 ⟨a, ha1⟩ 1
      (by simpa using ha)
    have e : IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {⟨a, ha1⟩} := by
      ext y
      rw [GlobalTheory.CNorm.mem_span_singleton_adicCompletionIntegers v
        (by change Valued.v a ≠ 0; rw [ha]; exact WithZero.exp_ne_zero)]
      change _ ↔ _ ≤ Valued.v a
      rw [ha, ← GlobalTheory.HaarLatticeScale.lt_one_iff_le_exp]
      exact Valuation.mem_maximalIdeal_iff _ _
    rw [pow_one, ← e] at h
    exact h
  open scoped Pointwise ENNReal NNReal in
  have modu_finite (x : Fv F v)
      (hx : x ≠ 0) : (distribHaarChar (Fv F v) hx.isUnit.unit : ℝ) = ‖x‖ := by
    have hu : IsUnit x := hx.isUnit
    have hv : Valued.v x ≠ 0 := by simpa using hx
    let μ : Measure (Fv F v) := Measure.addHaar
    have h := GlobalTheory.HaarLatticeScale.measureReal_valued_le_exp F v (Fv F v) μ Unit
      (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm (WithZero.log (Valued.v x))
    have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
    have e0 : (v.adicCompletionIntegers F : Set (Fv F v)) = Metric.closedBall 0 1 := by
      ext y
      rw [mem_closedBall_zero_iff, Valued.toNormedField.norm_le_one_iff]
      rfl
    have h0 : μ (v.adicCompletionIntegers F : Set (Fv F v)) ≠ 0 := (hO.measure_pos μ ⟨0, zero_mem _⟩).ne'
    have h1 : μ (v.adicCompletionIntegers F : Set (Fv F v)) ≠ ∞ := by
      rw [e0]; exact (isCompact_closedBall _ _).measure_lt_top.ne
    have e1 : {y : Fv F v | ∀ i, Valued.v ((ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm y i) ≤
        WithZero.exp (WithZero.log (Valued.v x))} = hu.unit • (v.adicCompletionIntegers F : Set (Fv F v)) := by
      ext y
      rw [Set.mem_smul_set_iff_inv_smul_mem, WithZero.exp_log hv, SetLike.mem_coe,
        HeightOneSpectrum.mem_adicCompletionIntegers, Units.smul_def, smul_eq_mul, map_mul,
        Units.val_inv_eq_inv_val, map_inv₀, IsUnit.unit_spec, inv_mul_le_iff₀ (zero_lt_iff.2 hv), mul_one]
      simp
    have e2 : {y : Fv F v | ∀ i, (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm y i ∈
        v.adicCompletionIntegers F} = (v.adicCompletionIntegers F : Set (Fv F v)) := by
      ext y
      simp
    rw [e1, e2, Measure.real, ← distribHaarChar_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, card_residue,
      Fintype.card_unit, pow_one] at h
    have h2 := mul_right_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨h0, h1⟩) h
    rw [h2, FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv]
    push_cast
    congr 1
  have hm := modu_finite (ϖ ^ k) (pow_ne_zero k hϖ0)
  have hn : ‖ϖ‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ := by
    rw [NumberField.FinitePlace.norm_def, HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π, hπ,
      WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    show (((Ideal.absNorm v.asIdeal : NNReal) ^ (-1 : ℤ) : NNReal) : ℝ) = _
    rw [zpow_neg_one, NNReal.coe_inv, NNReal.coe_natCast]
  rw [norm_pow, hn, inv_pow] at hm
  rw [← hm, ENNReal.ofReal_coe_nnreal]

end GlobalTheory.CompanionTheory.Equi.BallVol
