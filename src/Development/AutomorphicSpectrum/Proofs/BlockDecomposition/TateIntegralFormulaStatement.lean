module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateIntegralFormula
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide

@[expose] public section

open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_integral_formula : Tate := by
  first | exact @GlobalTheory.CompanionTheory.TateRes.tate | exact GlobalTheory.CompanionTheory.TateRes.tate | (intros; apply GlobalTheory.CompanionTheory.TateRes.tate <;> assumption)
