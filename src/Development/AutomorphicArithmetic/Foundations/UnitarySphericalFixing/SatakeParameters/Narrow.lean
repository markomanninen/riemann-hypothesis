module

public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentral
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SwOn
public import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.One.M

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {rc : IrrGL (k := w.adicCompletion E) → WD h}

theorem New.typeS (_s : TrivialCondition) (H : IsRecT h rc) : TypeLaw h rc := H.choose_spec.choose_spec.type

end UpperTheory.One.M
