module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaVectorsSetupExistsEqSmul
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift

@[expose] public section

open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_vectors_setup_exists_eq_smul : ∀ (g : ℕ) (S : Setup g) (e F : (Fin g → ℂ) → ℂ), S.Ok → S.IsTheta e → S.IsTheta F → F ≠ 0 → ∃ c : ℂ, e = c • F := by
  first | exact @GlobalTheory.MomOne.ThetaLine.exists_eq_smul | exact GlobalTheory.MomOne.ThetaLine.exists_eq_smul | (intros; apply GlobalTheory.MomOne.ThetaLine.exists_eq_smul <;> assumption)
