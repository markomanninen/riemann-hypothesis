module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineFormsOfFormUniqueness
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst

@[expose] public section

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_forms_of_form_uniqueness : CrystallineSemistableComparison.Onto.FormUniq → CrystallineSemistableComparison.Onto.AffOm := by
  first | exact @GlobalTheory.CompanionTheory.AffOmP.affOm | exact GlobalTheory.CompanionTheory.AffOmP.affOm | (intros; apply GlobalTheory.CompanionTheory.AffOmP.affOm <;> assumption)
