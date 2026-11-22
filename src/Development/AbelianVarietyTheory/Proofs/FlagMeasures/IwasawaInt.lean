module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralEquivariantLeftInvariant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompComplexifiedMaxCompactStatement

@[expose] public section

namespace GlobalTheory.IwaInt

theorem iwasawaInt : GlobalTheory.Dec.IwasawaInt := iwasawaInt_of GlobalTheory.T.iwasawa_decomp_complexifiedMaxCompact

end GlobalTheory.IwaInt
