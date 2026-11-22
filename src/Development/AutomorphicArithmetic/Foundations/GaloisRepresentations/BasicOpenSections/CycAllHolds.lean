module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PResClosed
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PHensSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PValLiftB
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PFibExt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PSecGen
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PClopenAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PWtVal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PCycRes
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PCycExt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PCycAll
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PNwtOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PullHQComp

@[expose] public section

namespace UpperTheory.Gal.Mod

theorem wtVal_holds : WtVal := by
  exact wtVal fibExt secGen (clopenAt resClosed hensSplit)

theorem cycAll_holds : CycAll := by
  exact cycAll resClosed valLiftB (cycRes wtVal_holds) (cycExt fibExt)

theorem esPt_holds : ESPt := esPt cycAll_holds

end UpperTheory.Gal.Mod
