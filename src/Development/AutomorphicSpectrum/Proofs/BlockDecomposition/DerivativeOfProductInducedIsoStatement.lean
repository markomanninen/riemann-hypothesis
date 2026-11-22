module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeOfProductInducedIso
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
theorem _root_.GlobalTheory.T.derivative_of_product_induced_iso : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k i) (σ : GRep k t), IsSmooth τ.ρ → IsSmooth σ.ρ → Nonempty ((psiMinus k (prodPGn τ σ).ρ).Equiv (smInd (Qp k i t) (qRep (mtw τ (((t : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ))) → GIso (psiN (prodPGn τ σ)) ((psiN τ).prod σ) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.Norm.psiN_prodPGn_of_equiv | exact GlobalTheory.CompanionTheory.BZPsiPG.Norm.psiN_prodPGn_of_equiv | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.Norm.psiN_prodPGn_of_equiv <;> assumption)
