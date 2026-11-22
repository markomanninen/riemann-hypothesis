module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.ConjAut
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.IdeleStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.OrdEmb
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.InvFun
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.OrdAut
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.OrdLine
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.MemOrd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.MemDual
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.LineEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.PosEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.StdHerm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.LineSkew
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.BaseEx

@[expose] public section

namespace UpperTheory.Gal.TP.Skew

theorem lineEx_holds : LineEx := lineEx ordAut (ordLine conjAut (ideleStep conjAut) ordEmb invFun ordAut) memOrd memDual

theorem spacesEx_holds : SpacesEx := spacesEx_of lineEx_holds posEx stdHerm lineSkew

theorem baseEx_holds : BaseEx := baseEx

theorem skewLine_holds : SkewLine := skewLine_of spacesEx_holds baseEx_holds

end UpperTheory.Gal.TP.Skew
