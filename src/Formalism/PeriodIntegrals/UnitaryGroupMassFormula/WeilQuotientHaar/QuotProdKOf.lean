module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.HaarExist

@[expose] public section

namespace QPK

theorem quotProdK_of (hA : GlobAsm) (hU : HaarUniq) (hL : LocPack) : PI.QuotProdK.QuotProdK :=
  hA hU hL

end QPK
