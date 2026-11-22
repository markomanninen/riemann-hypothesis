module

public import Development.WeilBound.CoreStatements.JacobiBlockDeterminants.DetInvNe
public import Development.WeilBound.CoreStatements.JacobiBlockDeterminants.JacobiBlocks
public import Development.WeilBound.CoreStatements.JacobiBlockDeterminants.ValDetFac
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.IsValueAtValAtOfRegAt
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.BlockDiagMinorNeZero
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.SameOrbitTrans

@[expose] public section

theorem HeightCancellation.stSing : SquareStatements.StSing :=
  SquareStatements.Sing.stSing_of SquareStatements.Sing.c0 HeightCancellation.G.c1 HeightCancellation.c2 SquareStatements.Sing.c5 HeightCancellation.G.c3w HeightCancellation.G.c3o HeightCancellation.c4
