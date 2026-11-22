module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.ExistsRec
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTUnique

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem uniqRec (N : GlobalTheory.Mem.LiteralAutomorphy.LitN) {h : IsPlaceOver A w} {rc rc' : IrrGL (k := w.adicCompletion E) → WD h}
    (H : IsRec h rc) (H' : IsRec h rc') (x : IrrGL (k := w.adicCompletion E)) (_ : Good x) : rc x = rc' x :=
  congrFun ((((GlobalTheory.LocLanglandsBridge.localLanglandsGL_of_depthZero_zelevinsky_bernstein N.loc.llc N.loc.conv N.loc.dzc N.loc.dzi N.loc.brauer N.loc.chev
    N.aut.art N.loc.exh N.loc.multi N.loc.cos N.loc.zel N.loc.geo N.loc.bz).1 E Ω A w h).unique) H H') x

end UpperTheory.V.Z.Win
