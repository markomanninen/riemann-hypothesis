module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSmoothPartitionUnityHolAtlasStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIntegralFinSumCompactStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDelChartSupportedMulFormEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasDelFinsetSumStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDbarCutoffMulFormEqZeroLocalStokesStatement

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.CxFormStokesBoth

open Set

section
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem eq_sum_fn_mul {N : ℕ} (χ : Fin N → M → ℝ) (hχ : ∀ y, ∑ j, χ j y = 1) (η : A.Fld) :
    η = ∑ j, A.fn (χ j) * η := by
  rw [← Finset.sum_mul]
  have : (∑ j, A.fn (χ j)) = 1 := by
    funext x
    simp only [Finset.sum_apply, HolAtlas.fn, Pi.one_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← Complex.ofReal_sum, hχ, Complex.ofReal_one, map_one]
  rw [this, one_mul]

theorem dbar_sum {N : ℕ} (α : Fin N → A.Fld) (hα : ∀ j, A.IsForm (α j)) :
    A.dbar (∑ j, α j) = ∑ j, A.dbar (α j) := by
  funext x
  have hloc : ∀ w, A.loc (∑ j, α j) x.1.1 w = ∑ j, A.loc (α j) x.1.1 w := by
    intro w
    by_cases hw : w ∈ (A.e x.1.1).target
    · simp only [HolAtlas.loc, dite_eq_left hw]
      exact Finset.sum_apply _ _ _
    · simp [HolAtlas.loc, hw]
  have hx := (A.e x.1.1).open_target.mem_nhds (x.ch.map_source x.2)
  have hdiff : ∀ j S, DifferentiableAt ℝ (fun w => (bas n).repr (A.loc (α j) x.1.1 w) S) x.crd :=
    fun j S => (((hα j).smooth x.1.1 S).differentiableOn (by simp)).differentiableAt hx
  have hcoeff : ∀ S u,
      GlobalTheory.dbar (fun w => (bas n).repr (A.loc (∑ j, α j) x.1.1 w) S) x.crd u =
        ∑ j, GlobalTheory.dbar (fun w => (bas n).repr (A.loc (α j) x.1.1 w) S) x.crd u := by
    intro S u
    have hsum : (fun w => (bas n).repr (A.loc (∑ j, α j) x.1.1 w) S) =
        fun w => ∑ j, (bas n).repr (A.loc (α j) x.1.1 w) S := by
      funext w
      rw [hloc, map_sum, Finsupp.finsetSum_apply]
    rw [hsum, GlobalTheory.dbar_sum (fun j _ => hdiff j S), _root_.sum_apply]
  rw [Finset.sum_apply]
  simp only [HolAtlas.dbar, dbarAt, coefwise, hcoeff, Finset.sum_smul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
end

theorem stokes : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n),
    ∀ η : A.Fld, A.IsForm η → A.integral (A.del η) = 0 ∧ A.integral (A.dbar η) = 0 := by
  intro M _ _ _ _ _ _ n A η hη
  obtain ⟨N, c, χ, hs, hsupp, hone⟩ := GlobalTheory.T.exists_finite_smooth_partition_unity_holAtlas A
  have hf : ∀ j, A.IsForm (A.fn (χ j) * η) := fun j =>
    FormMul.isForm_mul A _ _ (A.isForm_fn (hs j)) hη
  have hdiff : ∀ j, A.IsForm (A.del (A.fn (χ j) * η)) ∧ A.IsForm (A.dbar (A.fn (χ j) * η)) :=
    fun j => GlobalTheory.T.holAtlas_isForm_del_dbar_smooth M n A _ (hf j)
  have hdec := eq_sum_fn_mul A χ hone η
  constructor
  · rw [hdec, GlobalTheory.T.holAtlas_del_finset_sum A _ hf,
      GlobalTheory.T.holAtlas_integral_fin_sum_compact A _ (fun j => (hdiff j).1)]
    exact Finset.sum_eq_zero fun j _ => GlobalTheory.T.integral_del_chartSupported_mul_form_eq_zero A η (χ j) (c j) hη (hs j) (hsupp j)
  · rw [hdec, dbar_sum A _ hf,
      GlobalTheory.T.holAtlas_integral_fin_sum_compact A _ (fun j => (hdiff j).2)]
    exact Finset.sum_eq_zero fun j _ => GlobalTheory.T.integral_dbar_cutoff_mul_form_eq_zero_local_stokes A η (χ j) (c j) hη (hs j) (hsupp j)

end GlobalTheory.CxFormStokesBoth
