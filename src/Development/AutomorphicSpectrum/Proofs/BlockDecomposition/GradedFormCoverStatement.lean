module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormCover
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmoothCoordinateCoverStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpenStatement

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_form_cover : GlobalTheory.CompanionTheory.GrForm.StCover := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.AffCover.stCover | exact GlobalTheory.CompanionTheory.GrForm.AffCover.stCover | (intros; apply GlobalTheory.CompanionTheory.GrForm.AffCover.stCover <;> assumption)
