module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsParameterTaylorExpansionHomFibreDerivation
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isParameterTaylorExpansionHom_fibreDerivation :
    ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R]
      (N : ℕ) (t : I → R) (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)),
      (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) →
      ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (a : Fin g) (h : Hol W),
        ρ (dw a h) = LinearMap.lTensor R (dw (W := W₀) a).toLinearMap (ρ h) := by
  intro I _ _ g R _ _ N t W W₀ hW ρ hρ a h
  have expand := isTay_expand hW hρ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [expand (dw a h), expand h, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [LinearMap.lTensor_tmul, ← dw_slTayHol hW a h k s]
  rfl
