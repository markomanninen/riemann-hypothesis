module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjector
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_dualWeylWeightProjector : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (τ : ι) (w : Fin N → ℕ), ∃ a, IsProj O N lam τ w a ∧ ∀ a', IsProj O N lam τ w a' → a' = a := by
  first | exact @GlobalTheory.ExpFrame.exists_unique_isProj | exact GlobalTheory.ExpFrame.exists_unique_isProj | (intros; apply GlobalTheory.ExpFrame.exists_unique_isProj <;> assumption)
