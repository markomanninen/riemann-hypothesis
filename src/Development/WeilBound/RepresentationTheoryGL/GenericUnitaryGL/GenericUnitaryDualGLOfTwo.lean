module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.GenericUnlinkedGLOfSegRep2
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.UnlinkedIrreducibility.LUnlinkedCommPole
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.SquareIntegrableSegment
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehLanglandsQuotient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SegmentLinkedShift
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGLOfExhaustion
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegmentRepresentation

@[expose] public section

noncomputable section

namespace GlobalTheory.RgGu.Holds

theorem genericUnlinkedGL_holds : GlobalTheory.Published.GenericUnlinkedGL :=
  GlobalTheory.RgGu.genericUnlinkedGL_of_segRep2 PositivityTheory.RgGu.segmentRepresentation

theorem lUnlinkedIrr_holds :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.LUnlinkedIrr k :=
  GlobalTheory.RgGu.Unl.lUnlinkedIrr_pole PositivityTheory.RgGu.segmentRepresentation

theorem lUnlinkedComm_holds :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.LUnlinkedComm k :=
  GlobalTheory.RgGu.Unl.lUnlinkedComm_pole PositivityTheory.RgGu.segmentRepresentation

end GlobalTheory.RgGu.Holds

end
