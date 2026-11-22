module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PhiAsm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPhiQis
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PExtRes
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFamHom

@[expose] public section

namespace UpperTheory.Gal.TranscendenceTraces

theorem fL_of : PhiEx → FL := fL_of_parts phiQis_of extRes_of famHom_of

end UpperTheory.Gal.TranscendenceTraces
