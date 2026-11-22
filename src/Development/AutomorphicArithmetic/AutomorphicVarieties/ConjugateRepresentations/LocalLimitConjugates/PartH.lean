module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ExactSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.FrameEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.HarmSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.HarmSS
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.HodgeEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CharOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AutOf

@[expose] public section

theorem UpperTheory.V.Cj.partH : UpperTheory.V.Cj.PartH :=
  UpperTheory.V.Cj.H.partH_of UpperTheory.V.Cj.exactSub UpperTheory.V.Lit.Bor.frameEx UpperTheory.V.Lit.Bor.oneReal UpperTheory.V.Cj.H.harmSub
    UpperTheory.V.Cj.H.harmSS UpperTheory.V.Cj.H.hodgeEx UpperTheory.V.Cj.H.charOf UpperTheory.V.Cj.H.autOf
