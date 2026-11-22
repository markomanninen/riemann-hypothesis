module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PiTensorIrreducibleNontrivial
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pi_tensor_irreducible_nontrivial : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ {h : ℕ} (x : Fin h → IrrGL (k := k)), Nontrivial (PiTensorProduct ℂ (fun a => (x a).2.rep.V)) := by
  first | exact @GlobalTheory.CompanionTheory.TensorIrr.nontrivial_piTensorProduct_irrGL | exact GlobalTheory.CompanionTheory.TensorIrr.nontrivial_piTensorProduct_irrGL | (intros; apply GlobalTheory.CompanionTheory.TensorIrr.nontrivial_piTensorProduct_irrGL <;> assumption)
