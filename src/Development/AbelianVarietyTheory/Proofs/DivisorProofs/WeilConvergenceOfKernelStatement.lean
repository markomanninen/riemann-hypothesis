module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernel
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_convergence_of_kernel : GlobalTheory.ThK.KP → GlobalTheory.ThK.WeilConv := by
  first | exact @GlobalTheory.ThKWeil.weilConv | exact GlobalTheory.ThKWeil.weilConv | (intros; apply GlobalTheory.ThKWeil.weilConv <;> assumption)
