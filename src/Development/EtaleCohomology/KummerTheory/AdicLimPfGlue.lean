module

public import Development.EtaleCohomology.KummerTheory.AdicLimPfCok

@[expose] public section

namespace LateralTheory.KummerTheory

theorem AdicLim_of_fin (hF : AdicFin) : AdicLim := AdicLim_of AdicKer_holds hF AdicCok_holds

end LateralTheory.KummerTheory
