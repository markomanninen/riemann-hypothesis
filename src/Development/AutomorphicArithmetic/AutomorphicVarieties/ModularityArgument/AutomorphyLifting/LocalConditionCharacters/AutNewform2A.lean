module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocalConditionCharacters.CharPolSupp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.OrdPlain
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocalConditionCharacters.AutNewformAOfEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.PlainGd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.CompatTOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.ExistsGaloisRepRankTwoOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.RowOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.AutNew

@[expose] public section

open UpperTheory.V UpperTheory.V.Af UpperTheory.Gal.SV

namespace UpperTheory.V.Z.Win.RR

theorem gd : GdOf := fun E Ω _ _ _ _ _ A w h rc hrc a σ hp => Gu.plainGd E Ω A w h rc hrc a σ hp

end UpperTheory.V.Z.Win.RR
