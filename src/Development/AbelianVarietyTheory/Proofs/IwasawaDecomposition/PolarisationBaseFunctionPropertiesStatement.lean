module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarisationBaseFunctionProperties
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisationBaseFunction_properties : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g q : ℕ) (φs : InvFun ℤ) (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], IsPolFan (id : ℤ → ℤ) g φs → Module.finrank ℚ E * q ≤ g → Module.finrank (𝓞 E) X ≤ q → (∀ B ∈ psdCone (bar := H.bar) (X := X), ∀ t : ℝ, 0 ≤ t → evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) (t • B) = t * evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) B) ∧ (∀ B ∈ psdCone (bar := H.bar) (X := X), ∀ B' ∈ psdCone (bar := H.bar) (X := X), evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) B + evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) B' ≤ evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) (B + B')) ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜).evalZ β = n) ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜).evalZ β) := by
  first | exact @GlobalTheory.PolFan.baseFun_props | exact GlobalTheory.PolFan.baseFun_props | (intros; apply GlobalTheory.PolFan.baseFun_props <;> assumption)
