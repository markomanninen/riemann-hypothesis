module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.GenericUnitaryDualGLHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GenericUnlinkedGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericUnitaryDualGlStatement

@[expose] public section

namespace PositivityTheory.Gud

theorem generic_unitary_dual_GL : True → GlobalTheory.Published.SquareIntegrableSegment → GlobalTheory.Published.GenericUnlinkedGL → GlobalTheory.Published.LanglandsMultisegments →
    GlobalTheory.Published.StandardCosocleGL → GlobalTheory.Published.GenericUnitaryDualGL := fun _ _ _ _ _ => Fin.genericUnitaryDualGL_holds

end PositivityTheory.Gud
