module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHomModuloUnramifiedShapeOfLocalDuality
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisHom_modulo_unramified_shape_of_localDuality : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ReciprocityTheory.ChartRestriction.T2.ShapeUnr := by
  first | exact @GlobalTheory.ShapeUnrTriv.shapeUnr_of_localDuality | exact GlobalTheory.ShapeUnrTriv.shapeUnr_of_localDuality | (intros; apply GlobalTheory.ShapeUnrTriv.shapeUnr_of_localDuality <;> assumption)
