module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrFiniteOverPadicTopologiesExist
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_finite_over_padic_topologies_exist : ReciprocityTheory.ChartRestriction.T2.TopEx := by
  first | exact @GlobalTheory.PadicTop.topEx | exact GlobalTheory.PadicTop.topEx | (intros; apply GlobalTheory.PadicTop.topEx <;> assumption)
