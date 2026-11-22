module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedPadicDecompositionHomExists
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_padic_decomposition_hom_exists : ReciprocityTheory.ChartRestriction.T2.UnrDec := by
  first | exact @GlobalTheory.UnrChar.unrDec | exact GlobalTheory.UnrChar.unrDec | (intros; apply GlobalTheory.UnrChar.unrDec <;> assumption)
