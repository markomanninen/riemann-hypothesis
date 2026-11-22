module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormSmul
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_form_smul : GlobalTheory.CompanionTheory.GrForm.StSmul := by
  first | exact @GlobalTheory.CompanionTheory.GrFormSmul.stSmul | exact GlobalTheory.CompanionTheory.GrFormSmul.stSmul | (intros; apply GlobalTheory.CompanionTheory.GrFormSmul.stSmul <;> assumption)
