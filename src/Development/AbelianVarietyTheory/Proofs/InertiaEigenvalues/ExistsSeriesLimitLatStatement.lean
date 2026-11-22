module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeriesLimitLat
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_series_limit_Lat_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (M : ℕ) (c : ℕ → P.R.BdR), (∀ k, c k ∈ FilB P 0) → (∀ n : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, c k ∈ Lat AI M n) → ∃ b ∈ FilB P 0, ∀ n : ℕ, ∃ R₀ : ℕ, ∀ R ≥ R₀, b - ∑ k ∈ Finset.range R, c k ∈ Lat AI M n := by
  first | exact @GlobalTheory.ExpImage.exists_series_limit_Lat | exact GlobalTheory.ExpImage.exists_series_limit_Lat | (intros; apply GlobalTheory.ExpImage.exists_series_limit_Lat <;> assumption)
