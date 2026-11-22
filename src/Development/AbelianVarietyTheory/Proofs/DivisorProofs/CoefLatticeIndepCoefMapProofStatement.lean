module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefLatticeIndepCoefMapProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefLattice_indep_coefMap_proof : GlobalTheory.BaseCmp.CoefIndep := by
  first | exact @GlobalTheory.CoefIndepProof.coefIndep | exact GlobalTheory.CoefIndepProof.coefIndep | (intros; apply GlobalTheory.CoefIndepProof.coefIndep <;> assumption)
