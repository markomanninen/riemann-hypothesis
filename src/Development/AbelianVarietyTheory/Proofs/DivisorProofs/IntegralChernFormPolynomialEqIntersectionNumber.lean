module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothWeightIntegralCombinationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormOfWeightIsFormDbarEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartFirstChernFormOfWeightPowEqChernPartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneous
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFunctionalChernIntegral

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem integral_evalF_c1W_eq_interPoly : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ P : MvPolynomial κ ℝ, P.IsHomogeneous X.dim → (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) P) = X.interPoly Δ P := by
  intro hCD F _ σ X κ _ Δ L r ψ hψ P hP
  haveI := CxPts.compactSpace σ X.isProjOver
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ X.isProjOver
  haveI := CxPts.secondCountableTopology_of_isProjOver σ X.isProjOver
  have hform : ∀ G : MvPolynomial κ ℝ, (atlas X σ).IsForm (evalF (atlas X σ) (fun a => c1W (ψ a)) G) :=
    fun G => ((GlobalTheory.formCalculus _ _ (atlas X σ)).2.2.2.1 κ _ G
      (fun a => (GlobalTheory.T.firstChernFormOfWeight_isForm_dbar_eq_zero F σ X (L a) (ψ a) (hψ a).2).1)).1
  have Pw := GlobalTheory.LineForm.wInt_props (CxPts X.str σ) X.dim (atlas X σ)
  have hint : ∀ G : MvPolynomial κ ℝ, ∀ ε : ℤˣ,
      Integrable (fun _ => (1 : ℝ)) ((atlas X σ).part (evalF (atlas X σ) (fun a => c1W (ψ a)) G) ε) :=
    fun G ε => by
      haveI := Pw.1 _ (hform G) ε
      exact integrable_const _
  have eval_add (G₁ G₂ : MvPolynomial κ ℝ) :
      evalF (atlas X σ) (fun a => c1W (ψ a)) (G₁ + G₂) =
        evalF (atlas X σ) (fun a => c1W (ψ a)) G₁ + evalF (atlas X σ) (fun a => c1W (ψ a)) G₂ := by
    funext x
    simp [evalF, fld]
  have eval_smul (t : ℝ) (G : MvPolynomial κ ℝ) :
      evalF (atlas X σ) (fun a => c1W (ψ a)) (t • G) =
        (t : ℂ) • evalF (atlas X σ) (fun a => c1W (ψ a)) G := by
    funext x
    simp [evalF, fld, MvPolynomial.smul_eq_C_mul, Algebra.smul_def]
  have hadd : ∀ G₁ G₂ : MvPolynomial κ ℝ,
      (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) (G₁ + G₂)) =
        (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) G₁) +
          (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) G₂) := fun G₁ G₂ => by
    rw [← wInt_one, ← wInt_one, ← wInt_one, eval_add]
    exact (Pw.2.1 _ _ _ (hform G₁) (hform G₂) (hint G₁) (hint G₂)).2
  have hsmul : ∀ (t : ℝ) (G : MvPolynomial κ ℝ),
      (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) (t • G)) =
        t * (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) G) := fun t G => by
    rw [← wInt_one, ← wInt_one, eval_smul]
    exact Pw.2.2.1 _ t _ (hform G)
  have hspan : P ∈ Submodule.span ℝ (Set.range fun n : κ → ℤ => GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim) := by
    classical
    by_contra hnot
    obtain ⟨φ, hφF, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
    have hkill : ∀ n : κ → ℤ, φ (GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim) = 0 := by
      intro n
      have hm : GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim ∈ Submodule.span ℝ
          (Set.range fun n : κ → ℤ => GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim) := Submodule.subset_span ⟨n, rfl⟩
      have h2 := Submodule.mem_map_of_mem (f := φ) hm
      rw [hφ] at h2
      exact (Submodule.mem_bot ℝ).mp h2
    have hQ : GlobalTheory.PowLinSpan.polOf φ X.dim = 0 := by
      refine eq_zero_of_eval_zero_at_prod_finset _
        (fun _ => (Finset.range (X.dim + 1)).image (fun k : ℕ => (k : ℝ))) ?_ ?_
      · intro x
        rw [Finset.card_image_of_injective _ Nat.cast_injective]
        simpa using Nat.lt_succ_of_le (GlobalTheory.PowLinSpan.degreeOf_polOf_le φ X.dim x)
      · intro v hv
        have hv' : ∀ i, ∃ k : ℕ, (k : ℝ) = v i := by
          intro i
          obtain ⟨k, -, hk⟩ := Finset.mem_image.mp (hv i)
          exact ⟨k, hk⟩
        choose k hk using hv'
        rw [GlobalTheory.PowLinSpan.eval_polOf]
        have he : (∑ x, C (v x) * MvPolynomial.X x : MvPolynomial κ ℝ) = GlobalTheory.ArInt.lin (fun i => (((k i : ℤ)) : ℝ)) := by
          simp only [GlobalTheory.ArInt.lin, Int.cast_natCast, hk]
        rw [he]
        exact hkill (fun i => (k i : ℤ))
    exact hφF (GlobalTheory.PowLinSpan.homog_kill φ X.dim hQ P hP)
  clear hP
  induction hspan using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    obtain ⟨L', r', ψ', hpr, hci, hc1⟩ := GlobalTheory.T.exists_smoothWeight_integral_combination F σ X κ Δ L r ψ hψ n
    have e1 : evalF (atlas X σ) (fun a => c1W (ψ a)) (GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim) =
        fld (atlas X σ) (c1W ψ' ^ X.dim) := by
      funext x
      rw [hc1]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [evalF, fld, GlobalTheory.ArInt.lin, map_pow, map_sum, map_mul, MvPolynomial.map_C,
        MvPolynomial.map_X, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Finset.sum_apply, Pi.smul_apply, Pi.pow_apply]
      congr 2
    have e2 : X.interPoly Δ (GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim) = (X.inter fun _ => ∑ a, n a • Δ a : ℝ) := by
      have := Var.interPoly_prod_sum X Δ (fun _ a => n a)
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
      exact this
    rw [e1, e2, HolAtlas.integral, GlobalTheory.T.part_firstChernFormOfWeight_pow_eq_chernPart F σ X L' ψ' hci, GlobalTheory.T.part_firstChernFormOfWeight_pow_eq_chernPart F σ X L' ψ' hci,
      ← (hCD F X σ _ L' r' hpr ψ' hci).2]
    simp only [Weight.chernInt, Measure.restrict_univ, integral_const, smul_eq_mul, mul_one]
  | zero =>
    rw [map_zero]
    have := hsmul 0 0
    rw [zero_smul, zero_mul] at this
    exact this
  | add x y _ _ hx hy =>
    rw [map_add (f := _), hadd, hx, hy]
  | smul t x _ hx =>
    rw [map_smul, hsmul, hx, smul_eq_mul]

end GlobalTheory.ChernCalc
