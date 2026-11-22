module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PhiAsm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPhiUniv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PDSOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PDSLoc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPhiExact

@[expose] public section

namespace UpperTheory.Gal.TranscendenceTraces

theorem phiEx_of : LocFinSec → PhiEx := fun h => phiEx_of_parts phiUniv_of (phiExact_of (dSLoc_of (dSOne_of h)))

end UpperTheory.Gal.TranscendenceTraces
