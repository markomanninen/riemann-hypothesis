module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contragredient_product_irreducible : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), ∃ hd' : ∑ a, (dualCl (x a)).1 = N, Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr (fun a => dualCl (x a)) hd')) := by
  first | exact @GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr | exact GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr | (intros; apply GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr <;> assumption)
