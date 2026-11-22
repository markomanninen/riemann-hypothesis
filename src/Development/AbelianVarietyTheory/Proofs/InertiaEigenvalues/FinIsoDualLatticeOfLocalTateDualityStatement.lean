module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinIsoDualLatticeOfLocalTateDuality
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finIso_dualLattice_of_localTateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ReciprocityTheory.ChartRestriction.T2.FinIso := by
  first | exact @GlobalTheory.FinIsoDualLattice.finIso_of_localTateDuality | exact GlobalTheory.FinIsoDualLattice.finIso_of_localTateDuality | (intros; apply GlobalTheory.FinIsoDualLattice.finIso_of_localTateDuality <;> assumption)
