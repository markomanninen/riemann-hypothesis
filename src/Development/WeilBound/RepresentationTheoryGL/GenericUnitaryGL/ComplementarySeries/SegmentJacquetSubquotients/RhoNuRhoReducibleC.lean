module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.CuspPairIrr
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.PosMkIff
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ComplementaryOf
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Compact
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.BoundB
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ConjProd
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ConjDual
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ThetaContra
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.PiTensorTwist
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SomeRed
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.RhoNuRhoOfC

@[expose] public section

namespace PositivityTheory.RgGu.NR

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem redClC : RedCl k :=
  redCl_ofC k (someRed_of k (complementary_of signature) (compact k) (boundB k) (herm_ofB k (conjProd k) (conjDual k))
    (prodModel k)) (cuspUnit k) (cuspPairIrr k)

theorem rhoNuRhoReducibleC : PositivityTheory.Pf1.SegRepC.SegTwo.RhoNuRhoReducible := rhoNuRho_ofC fun k _ _ _ _ => redClC k

end PositivityTheory.RgGu.NR
