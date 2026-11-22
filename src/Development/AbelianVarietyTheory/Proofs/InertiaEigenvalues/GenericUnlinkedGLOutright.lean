module

public import Mathlib
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegmentRepresentation
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo

@[expose] public section

namespace GlobalTheory

theorem genericUnlinkedGL_outright : GlobalTheory.Published.GenericUnlinkedGL :=
  GlobalTheory.RgGu.Holds.genericUnlinkedGL_holds

end GlobalTheory
