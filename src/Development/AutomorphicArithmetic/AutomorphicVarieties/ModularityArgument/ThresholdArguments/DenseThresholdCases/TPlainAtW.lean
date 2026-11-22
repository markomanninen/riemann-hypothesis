module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.PlainAtW
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WStmtxx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPlainOf

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.PRep
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Sym.W
private theorem ratios {G : Type*} [CommGroup G] (a p : G) (h1 : p ≠ 1) (h2 : a ≠ p) (h3 : a ≠ p⁻¹)
    (h4 : a ^ 2 ≠ p) (h5 : a ^ 2 ≠ p⁻¹) (i j : Fin 3) :
    (![a, 1, a⁻¹] : Fin 3 → G) i ≠ (![a, 1, a⁻¹] : Fin 3 → G) j * p := by
  intro e
  fin_cases i <;> fin_cases j <;> simp at e
  · exact h1 e
  · exact h2 e
  · exact h4 (by rw [pow_two]; nth_rewrite 1 [e]; simp)
  · exact h3 (eq_inv_of_mul_eq_one_left e.symm)
  · exact h1 e.symm
  · exact h2 (inv_mul_eq_one.mp e.symm)
  · have e' : a ^ 2 * p = 1 := by rw [pow_two, mul_assoc, ← e]; simp
    exact h5 (eq_inv_of_mul_eq_one_left e')
  · exact h3 (by simpa using congrArg (·⁻¹) e)
  · exact h1 e
private theorem absOne_ne (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    absPow k 1 ≠ 1 := by
  intro h
  have e : absPow k ((1 : ℝ) : ℂ) = absPow k ((0 : ℝ) : ℂ) := by
    simpa [absPow_zero] using h
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LocGL.exists_uniformizer k
  have h1 : nabs k ϖ ≠ 1 := fun he => ValuativeRel.uniformizer_lt_one.ne (hϖ ▸ (nabs_eq_one_iff ϖ).1 he)
  have h2 : nabs k ϖ ^ (1 : ℝ) = nabs k ϖ ^ (0 : ℝ) := by
    have hx := val_absPow_ofReal k 1 ϖ
    have hy := val_absPow_ofReal k 0 ϖ
    rw [e] at hx
    exact_mod_cast hx.symm.trans hy
  have h3 := congrArg Real.log h2
  rw [Real.log_rpow (nabs_pos' k ϖ), Real.log_rpow (nabs_pos' k ϖ)] at h3
  exact one_ne_zero (mul_right_cancel₀ (Real.log_ne_zero_of_pos_of_ne_one (nabs_pos' k ϖ) h1) h3)
end UpperTheory.V.Z.Sym.W
theorem UpperTheory.V.Z.Sym.W.plain_at_w_statement :
    _root_.UpperTheory.V.Z.Sym.W.PlainAtWAlt := by
  intro hL L _ _ _ σ π hσ hl w hw a ha ⟨hs, τ₀, h₀, hq⟩ τ hτ
  have hc := hl.comp w hw τ hτ
  obtain ⟨e⟩ := UpperTheory.building_component_uniqueness L 3 σ hσ w hw _ _ _ _ h₀ hc
  have hq' : IsSubquotient τ.ρ (prinSeries ![a, 1, a⁻¹]) :=
    (IsSubquotient.of_surjective e.toIntertwiningMap e.surjective).trans hq
  have hp := absOne_ne (Kw w)
  have n1 := ha 1 (Or.inl rfl) 1 (Or.inl rfl)
  have n2 := ha 1 (Or.inl rfl) (-1) (Or.inr rfl)
  have n3 := ha 2 (Or.inr rfl) 1 (Or.inl rfl)
  have n4 := ha 2 (Or.inr rfl) (-1) (Or.inr rfl)
  simp only [pow_one, Int.cast_one, Int.cast_neg, absPow_neg] at n1 n2 n3 n4
  exact _root_.UpperTheory.V.Z.Sym.W.plain_of_statement hL L 3 w τ _ hs hq' (ratios a _ hp n1 n2 n3 n4)
end
