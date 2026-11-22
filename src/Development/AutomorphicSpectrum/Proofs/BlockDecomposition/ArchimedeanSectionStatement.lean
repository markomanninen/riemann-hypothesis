module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanSection
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut

@[expose] public section

noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_section : PositivityTheory.PfSWUS.SchInf.SecInf := by
  first | exact @GlobalTheory.CompanionTheory.SecInf.secInf | exact GlobalTheory.CompanionTheory.SecInf.secInf | (intros; apply GlobalTheory.CompanionTheory.SecInf.secInf <;> assumption)
