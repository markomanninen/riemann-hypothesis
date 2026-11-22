module

public import Mathlib
public import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
public import Development.DiscreteGroups.GlobalIrreducibility.LConvGlue
public import Development.DiscreteGroups.GlobalIrreducibility.LConvUnitOf
public import Development.DiscreteGroups.GlobalIrreducibility.LConvDens
public import Development.DiscreteGroups.GlobalIrreducibility.LConv
public import Development.DiscreteGroups.GlobalIrreducibility.LConvComm
public import Development.DiscreteGroups.GlobalIrreducibility.LConvUnif
public import Development.DiscreteGroups.GlobalIrreducibility.LConvKM
public import Development.DiscreteGroups.GlobalIrreducibility.LConvIrr
public import Development.DiscreteGroups.GlobalIrreducibility.LConvSep
public import Development.DiscreteGroups.GlobalIrreducibility.LConvGen
public import Development.DiscreteGroups.GlobalIrreducibility.LConvKir
public import Development.DiscreteGroups.GlobalIrreducibility.LConvBig

@[expose] public section

namespace DiscreteGroups.sglob.LConv

theorem localConverseGL : GlobalTheory.Published.LocalConverseGL :=
  localConverseGL_of_leaves cuspGen kirBump bigCell extremeExists extremeIrred sepOfExtreme commBound unifOfComm
    altIdentity finiteOfAlt unitOfUnif glue

end DiscreteGroups.sglob.LConv
