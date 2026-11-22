module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnramifiedNearIntegralComplexPadic
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementC
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementK

@[expose] public section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramified_near_integral_complexPadic : ∀ (l : ℕ) [Fact l.Prime] (x : ℂ_[l]), ‖x‖ ≤ 1 → ∃ y ∈ MaximalUnramifiedExtension l, ‖y‖ ≤ 1 ∧ ‖x - y‖ < 1 := by
  first | exact @GlobalTheory.ResidueUnr.exists_near_kur | exact GlobalTheory.ResidueUnr.exists_near_kur | (intros; apply GlobalTheory.ResidueUnr.exists_near_kur <;> assumption)
