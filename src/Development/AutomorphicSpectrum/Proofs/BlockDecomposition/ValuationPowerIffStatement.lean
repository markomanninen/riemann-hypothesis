module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationPowerIff
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

@[expose] public section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_power_iff : ∀ {S : Type} [CommRing S] (ϖ : S) (k : ℕ), k ≠ 0 → (Val (ϖ ^ k) ↔ Val ϖ) ∧ (IsAdicComplete (Ideal.span {ϖ ^ k}) S → IsAdicComplete (Ideal.span {ϖ}) S) := by
  first | exact @GlobalTheory.CompanionTheory.PowComp.val_pow | exact GlobalTheory.CompanionTheory.PowComp.val_pow | (intros; apply GlobalTheory.CompanionTheory.PowComp.val_pow <;> assumption)
