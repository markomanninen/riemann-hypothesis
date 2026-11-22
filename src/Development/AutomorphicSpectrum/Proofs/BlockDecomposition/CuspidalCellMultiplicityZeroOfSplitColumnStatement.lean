module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalCellMultiplicityZeroOfSplitColumn
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalMultiplicityProductZeroStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedProductDropZeroFactorsStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_cell_multiplicity_zero_of_split_column : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {h r : ℕ} (x : Fin h → IrrGL (k := k)) (y : Fin r → IrrGL (k := k)), (∀ j, (y j).IsCusp) → ∀ (b : Fin h → Fin r → ℕ) (hrow : ∀ i, ∑ j, b i j = (x i).1) (hcol : ∀ j, ∑ i, b i j = (y j).1) (j : Fin r) (i i' : Fin h), i ≠ i' → b i j ≠ 0 → b i' j ≠ 0 → jhMult (piTensor fun j => (y j).rep) (cellFunctor (c := fun i j => Fin (b i j)) (fun i => stdBlocks (b i) (hrow i)) (fun j => stdBlocks (fun i => b i j) (hcol j)) (piTensor fun i => (x i).rep)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.FineProd.CellMulti.jhMult_cell_eq_zero | exact GlobalTheory.CompanionTheory.FineProd.CellMulti.jhMult_cell_eq_zero | (intros; apply GlobalTheory.CompanionTheory.FineProd.CellMulti.jhMult_cell_eq_zero <;> assumption)
