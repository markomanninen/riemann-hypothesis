module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsoOfFrob
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsMonoOdd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadBC0OfQuadBaseChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.GaloisRepRankTwoRealOf

@[expose] public section

namespace UpperTheory.V.Af

open UpperTheory.V.Published

structure Hypotheses₂ : Prop where
  litN : GlobalTheory.Mem.LiteralAutomorphy.LitN
  cohC : ClozelCohC
  conjC : ClozelConjC
  borelC : BorelInjC
  galR : Z.Bc.GaloisRepRankTwoReal
  smoR : StrongMultOneReal
  gkR : GelfandKazhdanReal
  admR : AdmissibleReal
  bc : Br.QuadBC0
  newform : NewformRep
  ss : Lev.CsdSs := Lev.csdSs_of_full litN.aut.car
  mono : Lev.CsdMonoOdd := Lev.csdMonoOdd_of_full litN.aut.car

end UpperTheory.V.Af
