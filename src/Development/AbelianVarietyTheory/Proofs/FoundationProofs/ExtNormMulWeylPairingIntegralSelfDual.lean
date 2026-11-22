module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.ProdFormula
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeHasBasisAtEveryFinitePlace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BlockActMemRangeMapSubtype
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapEqOfMemNabStd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GramLocallyUnimodular

@[expose] public section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.PairInt

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem val_mul_nonneg (w : HeightOneSpectrum (𝓞 K)) {a b : K} (ha : 0 ≤ vw w a) (hb : 0 ≤ vw w b) :
    0 ≤ vw w (a * b) := by
  by_cases h0 : a = 0
  · rw [h0, zero_mul, ValuationRepresentative.vw_zero]
  by_cases h1 : b = 0
  · rw [h1, mul_zero, ValuationRepresentative.vw_zero]
  rw [ValuationRepresentative.vw_mul w a b h0 h1]
  exact add_nonneg ha hb

theorem val_pow_eq_zero (w : HeightOneSpectrum (𝓞 K)) {a : K} (ha : vw w a = 0) (k : ℕ) : vw w (a ^ k) = 0 := by
  by_cases h0 : a = 0
  · subst h0
    rcases k with _ | k
    · rw [pow_zero, ValuationRepresentative.vw_one]
    · rw [pow_succ, mul_zero, ValuationRepresentative.vw_zero]
  induction k with
  | zero => rw [pow_zero, ValuationRepresentative.vw_one]
  | succ k ih => rw [pow_succ, ValuationRepresentative.vw_mul w _ _ (pow_ne_zero _ h0) h0, ih, ha, add_zero]

theorem val_zpow_eq_zero (w : HeightOneSpectrum (𝓞 K)) {a : K} (ha : vw w a = 0) (e : ℤ) : vw w (a ^ e) = 0 := by
  obtain ⟨k, rfl | rfl⟩ := e.eq_nat_or_neg
  · rw [zpow_natCast, val_pow_eq_zero w ha]
  · rw [zpow_neg, zpow_natCast, ValuationRepresentative.vw_inv, val_pow_eq_zero w ha, neg_zero]

theorem val_prod_nonneg (w : HeightOneSpectrum (𝓞 K)) {ι : Type} (s : Finset ι) (f : ι → K)
    (hf : ∀ i ∈ s, 0 ≤ vw w (f i)) : 0 ≤ vw w (∏ i ∈ s, f i) :=
  Finset.prod_induction f (fun a => 0 ≤ vw w a) (fun _ _ ha hb => val_mul_nonneg w ha hb)
    (ValuationRepresentative.vw_one w).ge hf

private theorem selfDualK_full {K : Type} [Field K] [NumberField K] [StarRing K]
    {n : ℕ} (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K))
    (hM : IsSelfDualK G M) : Submodule.IsFullLattice K M := by
  classical
  haveI : Submodule.IsLattice K M := hM.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hM.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin n → K) → K := fun x => star x ⬝ᵥ G *ᵥ y
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) s f
  have ha0 : (algebraMap (𝓞 K) K a) ≠ 0 :=
    (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 K) (Fin n → K) := {
    carrier := {x | ∃ b : 𝓞 K, (b : K) = (algebraMap (𝓞 K) K a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : K) + c = _
      rw [hb, hc]
      simp [f, dotProduct, Matrix.mulVec, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd K) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def,
        RingOfIntegers.mapRingHom_apply, Pi.star_apply, star_mul, dotProduct, Matrix.mulVec,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : K) * _ = _
      ring }
  have hsP : (s : Set (Fin n → K)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 K) K a) • y ∈ M := by
    rw [← hM.2]
    change ∀ x ∈ M, star x ⬝ᵥ G *ᵥ ((algebraMap (𝓞 K) K a) • y) ∈ (1 : Submodule (𝓞 K) K)
    intro x hx
    obtain ⟨b, hb⟩ := (hs ▸ Submodule.span_le.mpr hsP) hx
    have hpair : (b : K) = star x ⬝ᵥ G *ᵥ ((algebraMap (𝓞 K) K a) • y) := by
      rw [hb]
      simp only [f, dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    refine ⟨b, ?_⟩
    simpa [LinearMap.toSpanSingleton_apply, Algebra.smul_def] using hpair
  have hy' : (algebraMap (𝓞 K) K a) • y ∈ Submodule.span K (M : Set (Fin n → K)) :=
    Submodule.subset_span hy
  have := (Submodule.span K (M : Set (Fin n → K))).smul_mem (algebraMap (𝓞 K) K a)⁻¹ hy'
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this


theorem extNorm_mul_pairK_integral : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K) (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, (G τ)ᴴ = G τ) → (∀ τ, IsUnit (G τ).det) → (∀ τ, IsSelfDualK (G τ) (M τ)) → ∀ x ∈ nabK lam M, ∀ y ∈ nabK lam M, extNorm K lam * pairK lam G x y ∈ (algebraMap (𝓞 K) K).range := by
  intro K _ _ _ ι _ n lam G M hG hdet hM x hx y hy
  obtain ⟨hglob, hloc⟩ := GlobalTheory.LocInt.localIntegrality K
  refine hglob _ fun w => ?_
  choose B hB using fun τ => GlobalTheory.LatBasisAt.basisAtEx K n (M τ) (selfDualK_full (G τ) (M τ) (hM τ)) (conjPl w)
  choose B' hB' using fun τ => GlobalTheory.LatBasisAt.basisAtEx K n (M τ) (selfDualK_full (G τ) (M τ) (hM τ)) w
  have hx' : x.1 ∈ nabP lam M := hx
  have hy' : y.1 ∈ nabP lam M := hy
  simp only [nabP, transLat, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars] at hx' hy'
  have hF := hx' (conjPl w) B hB
  have hF' := hy' w B' hB'
  have ex : x.1 = actP lam B (actP lam B⁻¹ x.1) := by rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]
  have ey : y.1 = actP lam B' (actP lam B'⁻¹ y.1) := by rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]
  obtain ⟨q, hq, hq'⟩ := extNormPos K ι n lam
  have hne : extNorm K lam ≠ 0 := by
    rw [hq']
    simpa using hq.ne'
  have hP := fun τ => GlobalTheory.GramLoc.gram_locally_unimodular K n (G τ) (M τ) (hG τ) (hdet τ) (hM τ) w (B τ) (B' τ) (hB τ) (hB' τ)
  rw [pairK_apply, ex, ey, pairTransport K ι n lam G B B', pairP_apply, ← mul_assoc, mul_div_cancel₀ _ hne,
    fockL_apply]
  refine val_mul_nonneg w ?_ ?_
  · exact val_prod_nonneg w _ _ fun τ _ => (val_zpow_eq_zero w (hP τ).2 _).ge
  · exact GlobalTheory.TestLat.vw_fockS_blockAct_nonneg K ι n w _ _ _ (hloc ι n lam (conjPl w) _ hF) (hloc ι n lam w _ hF')
      fun τ a b => (hP τ).1 b a

end GlobalTheory.PairInt
