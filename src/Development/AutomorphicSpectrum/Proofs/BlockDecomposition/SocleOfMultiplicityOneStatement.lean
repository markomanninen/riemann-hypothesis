module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.socle_of_multiplicity_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), jm x hd (prodIrr x hd) ≤ 1 → ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr x hd) := by
  first | exact @GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one | exact GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one | (intros; apply GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one <;> assumption)
