module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellJacquetMapSurjectiveWhittaker
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalDecompositionNormalStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellLeviUnipotentConjugationStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectionToTwistedEigenfunctionSupportStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorCompactUnipotentFixerStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactUnipotentSubgroupFiniteGenerationStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellFunctionCompactSupportUnipotentStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellJacquetIntegralVolumeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellUnipotentUniquenessClosedStatement

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_cell_jacquet_map_surjective_whittaker : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W), IsSmooth ρ → ∃ J : openFns d hd ρ →ₗ[ℂ] W, Function.Surjective J ∧ ∀ f : openFns d hd ρ, J f ∈ twKer ρ (unipM k d) (whitM d ψ) ↔ (f : IndSp (stdBlocks d hd) ρ) ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.OpenCoinv.openFns_whittaker | exact GlobalTheory.CompanionTheory.Rodier.OpenCoinv.openFns_whittaker | (intros; apply GlobalTheory.CompanionTheory.Rodier.OpenCoinv.openFns_whittaker <;> assumption)
