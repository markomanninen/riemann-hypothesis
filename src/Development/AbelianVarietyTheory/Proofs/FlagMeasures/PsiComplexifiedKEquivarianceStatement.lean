module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiComplexifiedKEquivariance
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition

@[expose] public section

open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_complexifiedK_equivariance : PsEquiv := by
  first | exact @GlobalTheory.Dec.Equivar.psEquiv | exact GlobalTheory.Dec.Equivar.psEquiv | (intros; apply GlobalTheory.Dec.Equivar.psEquiv <;> assumption)
