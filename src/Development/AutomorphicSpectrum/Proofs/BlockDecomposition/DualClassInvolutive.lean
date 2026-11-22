module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.Zcore

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isAdmissible_rep (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) : IsAdmissible x.rep := by
  exact hA k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr

theorem isIrreducible_contra_rep (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) :
    (contra x.rep).IsIrreducible := by
  exact GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k x.1) (isAdmissible_rep hA x) x.2.rep.irr

theorem dualCl_eq_of (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) :
    dualCl x = IrrGL.of (contra x.rep) (isSmooth_smoothRep _) (isIrreducible_contra_rep hA x) := by
  unfold dualCl
  rw [dite_eq_left (isIrreducible_contra_rep hA x)]

private theorem dualCl_eq_of_eq_contra (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x y : IrrGL (k := k))
    (hy : y = IrrGL.of (contra x.rep) (isSmooth_smoothRep _) (isIrreducible_contra_rep hA x)) :
    dualCl y = x := by
  subst hy
  rw [dualCl_eq_of hA]
  conv_rhs => rw [← IrrGL.of_rep x]
  exact IrrGL.of_eq_of.mpr ⟨(GlobalTheory.ContraRefl.contraEquiv (IrrGL.equivOf (contra x.rep) _ _)).trans
    (GlobalTheory.ContraRefl.evEquiv (GlobalTheory.SqIntUnit.compactOpen_basis k x.1) (isAdmissible_rep hA x)).symm⟩

theorem dualCl_dualCl : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)),
    dualCl (dualCl x) = x := by
  intro k _ _ _ _ hA x
  exact dualCl_eq_of_eq_contra hA x _ (dualCl_eq_of hA x)

end GlobalTheory.CompanionTheory.Zcore

end
