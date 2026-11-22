module

public import Mathlib
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

namespace UpperTheory.Lit.Red

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def FirstIn (x : IrrGL (k := k)) (P : Set (IrrGL (k := k))) : Prop :=
  ∀ (q : Fin 2 → IrrGL (k := k)) (hq : ∑ a, (q a).1 = x.1), (q 0).IsCusp → jm q hq x.rep ≠ 0 → q 0 ∈ P

def LastIn (x : IrrGL (k := k)) (P : Set (IrrGL (k := k))) : Prop :=
  ∀ (q : Fin 2 → IrrGL (k := k)) (hq : ∑ a, (q a).1 = x.1), (q 1).IsCusp → jm q hq x.rep ≠ 0 → q 1 ∈ P

def SuppIn (x : IrrGL (k := k)) (P : Set (IrrGL (k := k))) : Prop :=
  ∃ A : Multiset (IrrGL (k := k)), HasSupport x.rep A ∧ ∀ y ∈ A, y ∈ P

def Emb (x y z : IrrGL (k := k)) : Prop :=
  ∃ (hd : ∑ a, (![y, z] a).1 = x.1) (f : x.rep.IntertwiningMap (prodIrr ![y, z] hd)), Function.Injective f

def Occ (x y z : IrrGL (k := k)) : Prop :=
  ∃ hd : ∑ a, (![y, z] a).1 = x.1, jhMult x.rep (prodIrr ![y, z] hd) ≠ 0

def up (ρ : IrrGL (k := k)) : Set (IrrGL (k := k)) := {y | ∃ n : ℕ, y = ρ.nu (n : ℂ)}

end UpperTheory.Lit.Red

end
