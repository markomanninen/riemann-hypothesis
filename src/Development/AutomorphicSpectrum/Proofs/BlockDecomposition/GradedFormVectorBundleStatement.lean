module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormVectorBundle
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinatesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGoodStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstantStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpenStatement

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_form_vector_bundle : GlobalTheory.CompanionTheory.GrForm.StExists → GlobalTheory.CompanionTheory.GrForm.StAdd → GlobalTheory.CompanionTheory.GrForm.StSmul → GlobalTheory.CompanionTheory.GrForm.StRes → GlobalTheory.CompanionTheory.GrForm.StAct → GlobalTheory.CompanionTheory.GrForm.StLoc → GlobalTheory.CompanionTheory.GrForm.StVB := by
  first | exact @GlobalTheory.CompanionTheory.GrVB.main | exact GlobalTheory.CompanionTheory.GrVB.main | (intros; apply GlobalTheory.CompanionTheory.GrVB.main <;> assumption)
