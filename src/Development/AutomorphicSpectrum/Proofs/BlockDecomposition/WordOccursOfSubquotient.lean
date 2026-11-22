module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.Words

theorem wd_of_isSubquotient {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (hπ : IsSmooth π) (h : IsSubquotient σ π) (w : List (IrrGL (k := k))) (hw : Wd σ w) : Wd π w := by
  obtain ⟨hd, hne⟩ := hw
  refine ⟨hd, ?_⟩
  exact jhMult_ne_zero_iff.2
    ((jhMult_ne_zero_iff.1 hne).trans (GlobalTheory.JacquetExact.isSubquotient_jac _ hπ h))

end GlobalTheory.CompanionTheory.Words
