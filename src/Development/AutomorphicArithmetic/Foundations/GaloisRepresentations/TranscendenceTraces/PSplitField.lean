module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SplittingFieldConstruction

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.splitField_of :
    SplitField :=
  _root_.UpperTheory.Reformulated.B.SplittingFieldConstruction.splitField_of
