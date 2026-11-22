module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionLocallyConstantCompact
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

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_function_locally_constant_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k), IsLocallyConstant (fibV f g) ∧ HasCompactSupport (fibV f g) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.fibV_main | exact GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.fibV_main | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.fibV_main <;> assumption)
