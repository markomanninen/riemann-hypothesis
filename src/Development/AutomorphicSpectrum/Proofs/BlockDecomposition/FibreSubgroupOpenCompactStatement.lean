module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreSubgroupOpenCompact
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralIntertwinesUnipotentStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UMLeviMulUMLevi

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_subgroup_open_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin n) k)) (h : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin n)), IsOpen (K₁ : Set (GL (Fin n) k)) → IsOpen (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp n c K₁ h : Set (Mir k n)) ∧ IsCompact (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp n c K₁ h : Set (Mir k n)) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isOpen_isCompact_Bgrp | exact GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isOpen_isCompact_Bgrp | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isOpen_isCompact_Bgrp <;> assumption)
