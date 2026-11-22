module

public import Mathlib
public import Development.DiscreteGroups.GlobalIrreducibility.DzTypeCut
public import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def nmChar {g : ℕ} (K : Type) [Field K] [Algebra (ZMod g) K] (χ : (ZMod g)ˣ →* ℂˣ) : Kˣ →* ℂˣ :=
  χ.comp (Units.map (Algebra.norm (ZMod g) : K →* ZMod g))

end DiscreteGroups.sglob.DzType
