module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormCore
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HilbertSchmidtBlocks.HSBlocksMain

@[expose] public section

theorem hilbert_schmidt_blocks : Formalism.L2.SG.NormCut.HSBlocks :=
  NormHilbertSchmidtBlocks.hSBlocks_main
