module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.FormTraceDistrGL
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.DetPfTrGL
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.MemSBIffSupportedIn
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.DetUpdateRowOneLast
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.EventuallyConjGL
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.IsLocallyConstantIndicatorOne
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.FiniteImageOfEventually

@[expose] public section

namespace PositivityTheory.RgUd.AB.Final

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem thmA : ThmT k → ThmA k :=
  Pf.thmA_of_core k (Pf.coreX k (Pf.recover k (Pf.phiIndep (k := k)) (Pf.phiLin (k := k)) (Pf.phiInt (k := k)) (Pf.phiNear (k := k)) (Pf.pfAct (k := k))
    (Pf.ltEquiv (k := k) (Pf.phiEquiv (k := k)))))

theorem thmB : ThmA k → ThmB k := Pf.thmB k

end PositivityTheory.RgUd.AB.Final
