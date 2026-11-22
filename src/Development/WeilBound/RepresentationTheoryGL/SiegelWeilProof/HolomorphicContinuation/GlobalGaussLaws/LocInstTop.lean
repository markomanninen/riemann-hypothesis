module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocInst
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawL
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawB
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLaw
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRho
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocVac
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocKvac
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellTop

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem locInst_of_cell_kvac (hc : LIcell) (hk : LIkvac) (hT : TensMem) : LocInst :=
  locInst_of hT lIl lIlin lIlaw hc lIcont lIrho lIkact lIvac hk

theorem locInst_of_cell (hc : LIcell) (hT : TensMem) : LocInst := locInst_of_cell_kvac hc lIkvac hT

theorem locInst_of_away (hA : AwayAct) (hT : TensMem) : LocInst :=
  locInst_of_cell (lIcell_of' hA lIcont lIlaw lIvac) hT

end PositivityTheory.Rg.Sw.Glob
