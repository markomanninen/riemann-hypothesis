module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsZonalSphericalFunctionUnramifiedUnitary
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSatVecUOfDiag
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

@[expose] public section

open Formalism.UG (IsUnramInv GU KU Hecke dosetInd)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zonalSphericalFunction_unramifiedUnitary : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ α : Fin (n / 2) → ℂˣ, ∃ w : GU σ n → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsZonal ϖ q α w := by
  first | exact @GlobalTheory.IndefiniteRowSideFullHecke.ZonalExists.exists_isZonal | exact GlobalTheory.IndefiniteRowSideFullHecke.ZonalExists.exists_isZonal | (intros; apply GlobalTheory.IndefiniteRowSideFullHecke.ZonalExists.exists_isZonal <;> assumption)
