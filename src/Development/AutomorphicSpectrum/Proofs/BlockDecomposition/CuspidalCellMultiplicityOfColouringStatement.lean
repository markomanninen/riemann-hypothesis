module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalCellMultiplicityOfColouring
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductSingleNonzeroFactorEquivStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySublistPaddingStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SubsingletonIrrClZero

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_cell_multiplicity_of_colouring : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h : ℕ} (x : Fin h → IrrGL (k := k)) (W : List (IrrGL (k := k))) (b : Fin h → Fin W.length → ℕ) (hrow : ∀ i, ∑ j, b i j = (x i).1) (hcol : ∀ j, ∑ i, b i j = (W.get j).1) (c : Fin W.length → Fin h), (∀ i j, b i j = if c j = i then (W.get j).1 else 0) → jhMult (piTensor fun j => (W.get j).rep) (cellFunctor (c := fun i j => Fin (b i j)) (fun i => stdBlocks (b i) (hrow i)) (fun j => stdBlocks (fun i => b i j) (hcol j)) (piTensor fun i => (x i).rep)) = ∏ i, jmL (sub W c i) (x i).rep := by
  first | exact @GlobalTheory.CompanionTheory.FineProdCell.jhMult_cell_colour | exact GlobalTheory.CompanionTheory.FineProdCell.jhMult_cell_colour | (intros; apply GlobalTheory.CompanionTheory.FineProdCell.jhMult_cell_colour <;> assumption)
