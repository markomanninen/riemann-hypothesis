module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LandherrAndLandherrSt
public import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.SaOpen
public import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.LocalToAdelic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmTypeLetterFrameColumnDictionary
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtIffIsDerivAt0
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelBlockOfEq

@[expose] public section

namespace PositivityTheory.EqVol

theorem indexEq : IndexEq := indexEq_of (coSA saOpen) divisible

theorem levelIndexEq : LevelIndexEq :=
  levelIndexEq_of indexEq (levelCO hatCompactOpen) levelConj (levelRat hatRat)

end PositivityTheory.EqVol
