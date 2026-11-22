module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelExpansionAbsoluteConvergenceEqualWords
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagAtScale
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DiagCLC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXClosed

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_expansion_absolute_convergence_equal_words : Formalism.L2.SG.ThmSOwn.KExpTied ∧ AbsConvTied := by
  first | exact @GlobalTheory.Core.Diag.kExp_absConv_tied | exact GlobalTheory.Core.Diag.kExp_absConv_tied | (intros; apply GlobalTheory.Core.Diag.kExp_absConv_tied <;> assumption)
