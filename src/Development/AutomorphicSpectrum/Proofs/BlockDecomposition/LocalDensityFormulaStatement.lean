module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityFormula
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide

@[expose] public section

open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_density_formula : Dens := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOne.dens | exact GlobalTheory.CompanionTheory.SW.RankOne.dens | (intros; apply GlobalTheory.CompanionTheory.SW.RankOne.dens <;> assumption)
