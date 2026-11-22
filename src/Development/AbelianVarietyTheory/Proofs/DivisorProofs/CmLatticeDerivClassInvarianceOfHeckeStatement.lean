module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeDerivClassInvarianceOfHecke
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DefiningCoordinates
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmLattice_derivClassInvariance_of_hecke : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HeckeWeightTwo → GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement := by
  first | exact @GlobalTheory.DerivAtOrigin.statement | exact GlobalTheory.DerivAtOrigin.statement | (intros; apply GlobalTheory.DerivAtOrigin.statement <;> assumption)
