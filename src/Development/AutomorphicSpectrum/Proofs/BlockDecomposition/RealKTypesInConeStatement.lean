module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealKTypesInCone
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.MuQMemHarmSet

@[expose] public section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_k_types_in_cone : PositivityTheory.RgBcC.RealD.KTypeGenerationHighest := by
  first | exact @GlobalTheory.CompanionTheory.KTypeCone.k_types_in_weight_cone | exact GlobalTheory.CompanionTheory.KTypeCone.k_types_in_weight_cone | (intros; apply GlobalTheory.CompanionTheory.KTypeCone.k_types_in_weight_cone <;> assumption)
