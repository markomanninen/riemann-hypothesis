module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePartOpen
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut

@[expose] public section

noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_part_open : PositivityTheory.PfSWUS.SchInf.FinOpen := by
  first | exact @GlobalTheory.CompanionTheory.SW.FinOpenGram.finOpen | exact GlobalTheory.CompanionTheory.SW.FinOpenGram.finOpen | (intros; apply GlobalTheory.CompanionTheory.SW.FinOpenGram.finOpen <;> assumption)
