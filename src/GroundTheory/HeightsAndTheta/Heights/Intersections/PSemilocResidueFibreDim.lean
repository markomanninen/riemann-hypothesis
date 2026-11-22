module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StSemilocResidueFibreDim
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreDivSupp
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreTail
public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 PointVertical

theorem SemilocResidueFibreDim.proof (hFD : FibreDivSupp.Statement) (hDim : FibreDimStatement)
    (hAI : FibreDimensionZero.Statement) : SemilocResidueFibreDim.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hZ hs hsP hW W' hW' G'
  classical
  have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  have hsW' : rename v s ∈ W' := by
    have h : s ∈ imageZ v W' := hW'.2.2 ▸ hsW
    exact h
  have hD' : W' ∈ divSupp P' (rename v s) := ((hFD K ι K' ι' κ v P' n s α W hv hP' hZ hs hsP hW W').1 ⟨hW', hsW'⟩).1
  have hsec' : IsSectionOn P' (HermLine.sqMetric (ι := ι') (Function.extend κ α 0)) (rename v s) :=
    ⟨Function.extend κ α 0, fun _ => rfl, isMultiHomog_rename hv hs, hsP⟩
  have hsec : IsSectionOn (imageZ v P') (HermLine.sqMetric (ι := ι) α) s := ⟨α, fun _ => rfl, hs, hsP⟩
  have divSuppArith : DivSuppArithStatement := by
    intro K _ ι _ P n A s W hP hs hW
    obtain ⟨hK, ⟨hPp, hPh, -⟩, -, hPdim⟩ := hP
    obtain ⟨a, -, hsa, hsP⟩ := hs
    obtain ⟨hWmin, hWrel⟩ := hW
    have hWp : W.IsPrime := hWmin.1.1
    have hWmh : IsMultiHomogIdeal W := isMultiHomogIdeal_of_mem_minimalPrimes hPh hsa hWmin
    have := hPp
    have h1 := dim_quot_minimal_add_one P W s hsP hWmin
    rw [hPdim] at h1
    have hdim : ringKrullDim (MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) :=
      withBot_eq_of_add_one (by rw [h1, show n + 1 + Fintype.card K = n + Fintype.card K + 1 by omega])
    exact ⟨fun hh => ⟨hK, ⟨hWp, hWmh, hWrel⟩, hh, hdim⟩,
      fun hv => ⟨⟨hWp, hWmh, hWrel⟩, charOf_prime hWp hv, hdim⟩⟩
  have hA' := divSuppArith K' ι' P' n _ _ W' hP' hsec' hD'
  have hA := divSuppArith K ι (imageZ v P') n _ _ W hZ hsec hW
  have hdW : ringKrullDim (MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    by_cases hh : IsHorizontal W
    · exact (hA.1 hh).2.2.2
    · exact (hA.2 hh).2.2
  by_cases hh' : IsHorizontal W'
  · have hh : IsHorizontal W := by
      unfold IsHorizontal at hh' ⊢
      rw [← hh', ← hW'.2.2]
      ext z
      simp [imageZ, Ideal.mem_comap]
    have hW'a : IsArithVar W' (n + 0) := hA'.1 hh'
    have hWa : IsArithVar (imageZ v W') n := hW'.2.2 ▸ hA.1 hh
    exact hDim K ι K' ι' κ v W' n 0 G' hv hW'a hWa
  · obtain ⟨hW'm, hpr, hdW'⟩ := hA'.2 hh'
    set p := charOf W' with hpdef
    have : Fact p.Prime := ⟨hpr⟩
    have hpW' : ((p : ℕ) : MRing ι') ∈ W' := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.natCast_mem_of_charOf W'
    have hpW : ((p : ℕ) : MRing ι) ∈ W := by
      rw [← hW'.2.2]
      show rename v ((p : ℕ) : MRing ι) ∈ W'
      simpa using hpW'
    have hWm : IsMultiProjPrime W := hW'.2.2 ▸ isMultiProjPrime_imageZ hv hW'm
    have hWp : IsProjVarF (W'.map (red p)) n :=
      ⟨isMultiProjPrime_red p hW'm hpW', by rw [ringKrullDim_red p hpW', hdW']⟩
    have hVi : IsProjVarF (imageVar (ZMod p) v (W'.map (red p))) n := by
      rw [imageVar_red p v hpW', hW'.2.2]
      exact ⟨isMultiProjPrime_red p hWm hpW, by rw [ringKrullDim_red p hpW, hdW]⟩
    exact hAI K ι K' ι' κ v p W' n hv hpW' hWp hVi G'

end GroundTheory.Heights₂.Heights.Inter
