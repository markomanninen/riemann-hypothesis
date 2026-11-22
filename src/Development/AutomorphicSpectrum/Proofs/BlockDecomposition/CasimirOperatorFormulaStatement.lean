module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirOperatorFormula
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_operator_formula : PositivityTheory.RgBcC.Fc.OmFormula := by
  first | exact @GlobalTheory.CompanionTheory.Casimir.omFormula | exact GlobalTheory.CompanionTheory.Casimir.omFormula | (intros; apply GlobalTheory.CompanionTheory.Casimir.omFormula <;> assumption)
