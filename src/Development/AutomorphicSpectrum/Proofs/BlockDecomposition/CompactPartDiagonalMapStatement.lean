module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactPartDiagonalMap
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf

@[expose] public section

open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_part_diagonal_map : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (Z : Subgroup H), cptPart (Z.map ((MonoidHom.id H).prod (MonoidHom.id H))) = (cptPart Z).map ((MonoidHom.id H).prod (MonoidHom.id H)) := by
  first | exact @GlobalTheory.CompanionTheory.CptDiag.cptPart_diag | exact GlobalTheory.CompanionTheory.CptDiag.cptPart_diag | (intros; apply GlobalTheory.CompanionTheory.CptDiag.cptPart_diag <;> assumption)
