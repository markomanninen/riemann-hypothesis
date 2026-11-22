module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinPadicValPowSubOneCoprimeEqClosedFormula
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateWideInd

@[expose] public section

open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minPadicValPowSubOneCoprime_eq_closedFormula : Formalism.PairingDivisionLocalBalance.MinVal → ∀ l n : ℕ, l.Prime → 2 ≤ n → Even n → mMin l n = Formalism.PairingDivisionLocalBalance.mE l n := by
  first | exact @GlobalTheory.MinValClosed.mMin_eq_mE | exact GlobalTheory.MinValClosed.mMin_eq_mE | (intros; apply GlobalTheory.MinValClosed.mMin_eq_mE <;> assumption)
