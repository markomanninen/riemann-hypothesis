module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.TLiftK

@[expose] public section

theorem UpperTheory.TP.K.tLiftK : UpperTheory.TP.TLiftK :=
  UpperTheory.TP.tLift_holds_k
