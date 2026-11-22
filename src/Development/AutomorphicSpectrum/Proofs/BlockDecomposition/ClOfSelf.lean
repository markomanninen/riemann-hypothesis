module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.WordProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


open Classical in
def clOf (a : IrrGL (k := k)) (d : ℕ) : IrrCl (GL (Fin d) k) :=
  if h : a.1 = d then h ▸ a.2 else (IrrRep.det (Fin d) 1 isSmoothChar_one).cl

theorem clOf_self (a : IrrGL (k := k)) : clOf a a.1 = a.2 := by
  simp [clOf]

end GlobalTheory.CompanionTheory.WordProd

end
