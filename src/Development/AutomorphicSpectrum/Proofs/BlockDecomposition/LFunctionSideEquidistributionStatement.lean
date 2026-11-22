module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LFunctionSideEquidistribution
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide

@[expose] public section

open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.l_function_side_equidistribution : PositivityTheory.Rg.Mass.Equi → LSide := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.lside | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.lside | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.lside <;> assumption)
