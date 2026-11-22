module

public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushAsm
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDim
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushPullB
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushUnit
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushNumEq
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushMap
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushPF
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushFib
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushTest
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushMass
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushCentre
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushJoin
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushLat
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushFibLink
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushMuLink

@[expose] public section

namespace SheetDecomposition

theorem degPush : DegPush :=
  have hEq : NumEq := numEq ptDim numPull (unitZero ptDim)
  degPush_of hEq (geoPF ptDim) (fibNum hEq) trdegU testRelabel geoTest numMap muMass fieldJoin genIso
    (fibLink chartVal centre coordLat) (muLink chartVal centre coordLat)

end SheetDecomposition
