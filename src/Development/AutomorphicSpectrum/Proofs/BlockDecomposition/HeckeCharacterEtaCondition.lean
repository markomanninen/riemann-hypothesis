module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero

@[expose] public section

open PositivityTheory.Rg.Rsw

namespace GlobalTheory.CompanionTheory.HeckeEtaExist

theorem heckeEta : HeckeEta :=
  GlobalTheory.RawLift.exists_hecke_resEta

end GlobalTheory.CompanionTheory.HeckeEtaExist
