module

public import Mathlib
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TScalarFull

@[expose] public section

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

theorem UpperTheory.Lit.Cas.scalarProd :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h : ℕ) (y : Fin h → IrrGL (k := k)) (x : IrrGL (k := k)) (hc : ∑ i, (y i).1 = x.1) (t : kˣ) (c : Fin h → ℂ), (∀ i, ScalarBy (y i) t (c i)) → jhMult x.rep (prodIrr y hc) ≠ 0 → ScalarBy x t (∏ i, c i) := by
  intro k _ _ _ _ h y x hc t c hy hm w
  exact GlobalTheory.SmGL.Model.scalar_of_isSubquotient (jhMult_ne_zero_iff.1 hm)
    (UpperTheory.Lit.Cas.scalarFull k h x.1 y hc t c hy) w
