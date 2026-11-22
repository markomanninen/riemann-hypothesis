module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
public import Formalism.PolynomialDimension.WeylDim

@[expose] public section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.LocMatLat

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]


omit [DecidableEq ι] in
theorem exists_denom (B : HeightOneSpectrum (𝓞 K) → Matrix ι ι K) (h : {w | ¬ IntAt w (B w)}.Finite) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ w, IntAt w ((d : K) • B w) := by
  haveI : Finite {w | ¬ IntAt w (B w)} := h
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K))
    (fun p : {w | ¬ IntAt w (B w)} × ι × ι => B p.1.1 p.2.1 p.2.2)
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, fun w i j => ?_⟩
  by_cases hw : IntAt w (B w)
  · rw [Matrix.smul_apply, smul_eq_mul, map_mul]
    exact mul_le_one' (w.valuation_le_one (b : 𝓞 K)) (hw i j)
  · obtain ⟨r, hr⟩ := hb (⟨w, hw⟩, i, j)
    have : ((b : 𝓞 K) : K) • B w i j = algebraMap (𝓞 K) K r := by
      rw [hr]; simp [Algebra.smul_def]
    rw [Matrix.smul_apply, this]
    exact w.valuation_le_one r


omit [DecidableEq ι] in
theorem mulVec_le (w : HeightOneSpectrum (𝓞 K)) {M : Matrix ι ι K} (hM : IntAt w M) {x : ι → K}
    (hx : ∀ j, w.valuation K (x j) ≤ 1) (i : ι) : w.valuation K ((M *ᵥ x) i) ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_one' (hM i j) (hx j)

theorem isLattice_locLat (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] [DecidableEq ι]
    (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K) (hA : IsAdelic A) : Submodule.IsFullLattice K (locLat A) := by
  obtain ⟨hdet, hfin⟩ := hA
  obtain ⟨d, hd0, hd⟩ := exists_denom A (hfin.subset fun w hw h => hw h.1)
  obtain ⟨e, he0, he⟩ := exists_denom (fun w => (A w)⁻¹) (hfin.subset fun w hw h => hw h.2)
  have hdK : (d : K) ≠ 0 := by simpa using hd0
  have heK : (e : K) ≠ 0 := by simpa using he0
  have hLat : Submodule.IsLattice K (locLat A) := by
    constructor
    · let f : (ι → 𝓞 K) →ₗ[𝓞 K] (ι → K) := (e : K)⁻¹ • (Algebra.linearMap (𝓞 K) K).compLeft ι
      have hf : (LinearMap.range f).FG := by
        rw [← Submodule.map_top]
        exact Submodule.FG.map _ Module.Finite.fg_top
      refine hf.of_le fun x hx => ?_
      have hint : ∀ i, (e : K) * x i ∈ (algebraMap (𝓞 K) K).range := fun i =>
        HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K _ fun w => by
          have h1 := mulVec_le w (he w) (hx w) i
          rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec,
            Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hdet w)), Matrix.one_mulVec] at h1
          exact h1
      choose y hy using hint
      refine ⟨y, funext fun i => ?_⟩
      change (e : K)⁻¹ * algebraMap (𝓞 K) K (y i) = x i
      rw [hy, inv_mul_cancel_left₀ heK]
    · intro s hs hli
      exact (LinearIndependent.iff_fractionRing _ _).mp hli
  refine { toIsLattice := hLat, span_eq_top := ?_ }
  rw [eq_top_iff, ← (Pi.basisFun K ι).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  change Pi.basisFun K ι i ∈ Submodule.span K (locLat A : Set (ι → K))
  have hm : (d : K) • Pi.basisFun K ι i ∈ locLat A := by
    intro w j
    have h := mulVec_le w (hd w) (x := Pi.basisFun K ι i) (by
      intro k
      simp only [Pi.basisFun_apply, Pi.single_apply]
      split_ifs <;> simp) j
    simpa only [Matrix.smul_mulVec, Matrix.mulVec_smul] using h
  have hm' := (Submodule.span K (locLat A : Set (ι → K))).smul_mem (d : K)⁻¹
    (Submodule.subset_span hm)
  simpa only [smul_smul, inv_mul_cancel₀ hdK, one_smul] using hm'

end GlobalTheory.LocMatLat
