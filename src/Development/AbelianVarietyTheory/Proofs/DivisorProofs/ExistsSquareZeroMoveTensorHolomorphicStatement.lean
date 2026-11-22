module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroMoveTensorHolomorphic
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_squareZero_move_tensor_holomorphic :
    ∀ {g : ℕ} {W₀ : Opens (Tot Empty g)} {R : Type} [CommRing R] [Algebra ℂ R]
      {C : Type} [CommRing C] (ψ : R ⊗[ℂ] Hol W₀ →+* C) (n : Fin g → C),
      (∀ a b, n a * n b = 0) → ∃ ψ' : R ⊗[ℂ] Hol W₀ →+* C,
        ∀ x, ψ' x = ψ x + ∑ a, ψ (LinearMap.lTensor R (dw (W := W₀) a).toLinearMap x) * n a := by
  intro g W₀ R _ _ C _ ψ n hn
  have hMove := GlobalTheory.SqZeroMove.gen_hom ψ
    (fun a => (LinearMap.lTensor R (dw (W := W₀) a).toLinearMap).toAddMonoidHom)
    (fun a => GlobalTheory.SqZeroMove.lTensor_one (R := R) (dw (W := W₀) a))
    (fun a x y => GlobalTheory.SqZeroMove.lTensor_leibniz (dw (W := W₀) a) x y) n hn
  exact hMove
