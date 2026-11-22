module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralCharacterEqProdSupercuspidalSupport
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralCharacter_eq_prod_supercuspidalSupport : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)) (s : Multiset (IrrGL (k := k))) (ω : kˣ →* ℂˣ), HasSupport x.rep s → HasCentralChar x.rep ω → ∃ f : IrrGL (k := k) → kˣ →* ℂˣ, (∀ y ∈ s, HasCentralChar y.rep (f y)) ∧ ∀ z, ω z = (s.map fun y => f y z).prod := by
  first | exact @GlobalTheory.CentralSupport.centralChar_eq_prod_support | exact GlobalTheory.CentralSupport.centralChar_eq_prod_support | (intros; apply GlobalTheory.CentralSupport.centralChar_eq_prod_support <;> assumption)
