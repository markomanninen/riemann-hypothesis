module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLatticePeriodicity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentTopMemParabolicStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockMemParabolicStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviDecompStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulVecMidBlockDecompStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLeviUnipotentProjStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinearChangeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompParabolicMaximalCompactStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumOverCompactCosetsJacquetKernelStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedSectionSupportedOpenStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionLocallyConstantCompactStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_periodicity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (φ : (Fin t → k) → Z), IsLocallyConstant φ → HasCompactSupport φ → ∃ c : k, c ≠ 0 ∧ ∀ o ∈ Lc t c, ∀ v, φ (v + o.toAdd) = φ v := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.LatInv.exists_Lc_invariant | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.LatInv.exists_Lc_invariant | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.LatInv.exists_Lc_invariant <;> assumption)
