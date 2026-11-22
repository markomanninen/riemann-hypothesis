module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealWeight
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DistribHaarCharTransport
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VectorTupleProductMeasureTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexMulMeasure

@[expose] public section

open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp Formalism.UG Matrix GlobalTheory.BorelUMod
open scoped NNReal Pointwise

noncomputable section
namespace GlobalTheory.LineUMod

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem locCompact_secondCountable [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) :
    LocallyCompactSpace L ∧ SecondCountableTopology L := by
  obtain ⟨-, hv, -, hϖ, -, hq, hcard⟩ := h
  haveI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨ϖ, by rw [hϖ]; exact WithZero.coe_ne_zero, by rw [hϖ, ← WithZero.coe_one, ne_eq, WithZero.coe_inj]; decide⟩
  letI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)
  have hp := (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    (K := L)).2 ⟨inferInstance, (Valued.v : Valuation L _).valuationSubring_isDiscreteValuationRing,
      Nat.finite_of_card_ne_zero (by
        refine ne_of_eq_of_ne hcard (pow_ne_zero _ (by omega)))⟩
  constructor
  · open scoped Valued in exact inferInstance
  · open scoped Valued in exact inferInstance


open UpLatIndex in
theorem distribHaarChar_eq [CompleteSpace L] [LocallyCompactSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ}
    (h : IsUnramInv ϖ σ q) (u : Lˣ) : (distribHaarChar L u : ℝ) = (q : ℝ) ^ (-2 * ordL (u : L)) := by
  have hq : q ≠ 0 := by have := h.2.2.2.2.2.1; omega
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  haveI := (locCompact_secondCountable h).2
  borelize L
  let μ : Measure L := Measure.addHaar
  have key : ∀ k K : ℤ, k ≤ K → μ.real (ordBall L k) = (q : ℝ) ^ (2 * (K - k)) * μ.real (ordBall L K) := by
    intro k K hk
    have e := relIndex_ordBall h hk
    haveI : ((ordBall L K).addSubgroupOf (ordBall L k)).FiniteIndex :=
      ⟨ne_of_eq_of_ne e (pow_ne_zero _ (pow_ne_zero _ hq))⟩
    have := GlobalTheory.BaseModule.addRelIndex_mul_measure (ordBall L K) (ordBall L k) (ordBall_mono hk)
      (isOpen_vball h.2.2.2.1 K).measurableSet μ
    rw [Measure.real, ← this, e, ENNReal.toReal_mul, ENNReal.toReal_natCast, ← pow_mul, Nat.cast_pow, ← zpow_natCast,
      Measure.real]
    congr 2
    omega
  have hs : u • (ordBall L 0 : Set L) = ordBall L (ordL (u : L)) := by
    ext x
    obtain ⟨y, rfl⟩ := MulAction.surjective u x
    beta_reduce
    rw [Set.smul_mem_smul_set_iff, SetLike.mem_coe, SetLike.mem_coe, mem_ordBall, mem_ordBall, Units.smul_def,
      smul_eq_mul, map_mul, v_eq_exp u.ne_zero, neg_zero, WithZero.exp_zero]
    exact (mul_le_iff_le_one_right WithZero.exp_pos).symm
  have h1 := congrArg ENNReal.toReal (distribHaarChar_mul μ u (ordBall L 0 : Set L))
  rw [hs, ENNReal.toReal_mul, ENNReal.coe_toReal, ← Measure.real, ← Measure.real,
    key 0 |ordL (u : L)| (abs_nonneg _), key (ordL (u : L)) _ (le_abs_self _), ← mul_assoc] at h1
  have hpos : μ.real (ordBall L |ordL (u : L)|) ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨(isOpen_vball h.2.2.2.1 _).measure_ne_zero μ ⟨0, zero_mem (ordBall L _)⟩,
      (isCompact_vball h _).measure_ne_top⟩
  have h2 := mul_right_cancel₀ hpos h1
  rw [eq_comm, ← mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ hq'), ← _root_.zpow_neg, ← zpow_add₀ hq'] at h2
  rw [← h2]
  congr 1
  ring

section Mat
omit [Valued L (WithZero (Multiplicative ℤ))]

variable (x y : Fin n → L) (z : L)

end Mat

variable {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) (hc : Continuous σ)



variable {θ d : L} (hθ : θ + σ θ = 1) (hd : σ d = -d) (hd0 : d ≠ 0)



end GlobalTheory.LineUMod
