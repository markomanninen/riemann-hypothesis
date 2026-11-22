module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EigenOfRightInvariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionEigenfunctionMaximalCompact

@[expose] public section

open GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_eigenfunction_maximal_compact : GlobalTheory.CompanionTheory.Jp.SectionEigenfunctionMaximalCompact := by
  first | exact @GlobalTheory.CompanionTheory.Jp.B3.eigen_of_rightInvariant | exact GlobalTheory.CompanionTheory.Jp.B3.eigen_of_rightInvariant | (intros; apply GlobalTheory.CompanionTheory.Jp.B3.eigen_of_rightInvariant <;> assumption)
