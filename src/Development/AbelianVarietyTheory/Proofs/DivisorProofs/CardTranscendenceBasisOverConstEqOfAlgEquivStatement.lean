module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTranscendenceBasisOverConstEqOfAlgEquiv
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_transcendenceBasisOverConst_eq_of_algEquiv : ∀ {K κ : Type} [Field K] [Field κ] [Algebra ℂ K] [Algebra ℂ κ] (e : K ≃ₐ[ℂ] κ)
  (n k : ℕ) (x : Fin n → K) (z : Fin k → κ),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ) z → n = k := by
  first | exact @GlobalTheory.trBasis_card_eq_of_algEquiv | exact GlobalTheory.trBasis_card_eq_of_algEquiv | (intros; apply GlobalTheory.trBasis_card_eq_of_algEquiv <;> assumption)
