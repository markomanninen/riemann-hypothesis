module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchurTwistHolds

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

theorem UpperTheory.schur_twist_holds :
    UpperTheory.V.Af.Bc.SchurTw :=
  _root_.UpperTheory.Reformulated.B.H13.schur_twist_holds
