module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginDegreeCount
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumFundCoMulSumIic

@[expose] public section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_degree_count : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (n₀ : Option (RootIx D) → ℤ) (N₀ : ℕ), (∀ r, n₀ (some r) = -Fx.n r) → n₀ none = -(Fx.q' : ℤ) → ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) ≠ 0 → ∀ w ∈ mcPts (mCoordIdeal RM.y), ∃ (dg dh : RM.K → ℕ) (G Hf : MRing RM.ι), IsMultiHomog G dg ∧ IsMultiHomog Hf dh ∧ (∀ k, (dg k : ℤ) = dh k + (combLine (RM.line 1) n₀).a k) ∧ aeval RM.y G = ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) * aeval RM.y Hf ∧ aeval RM.y Hf ≠ 0 ∧ aeval w Hf ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.origin_section_rep | exact GlobalTheory.CompanionTheory.Ar.Small.origin_section_rep | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.origin_section_rep <;> assumption)
