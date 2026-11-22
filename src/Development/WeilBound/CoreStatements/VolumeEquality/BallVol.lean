module

public import Development.WeilBound.CoreStatements.VolumeEquality.BallVolMoeb
public import Development.WeilBound.CoreStatements.VolumeEquality.BallVolStdZ
public import Development.WeilBound.CoreStatements.VolumeEquality.BallVolModel
public import Development.WeilBound.CoreStatements.VolumeEquality.BallVolArith
public import Development.WeilBound.CoreStatements.VolumeEquality.BallVolLevel
public import Development.WeilBound.CoreStatements.VolumeEquality.BallVolFam
public import Development.WeilBound.CoreStatements.VolumeEquality.BallVolRed

@[expose] public section

namespace SheetDecomposition

theorem famVol : FamVol := famVol_of moebVol (stdModel_of stdZ) arithIdx levelDict

theorem ballVolEq : BallVolEq := ballVolEq_of famVol

end SheetDecomposition
