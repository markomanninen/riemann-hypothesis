module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthBaseChangeQuotientOfMapMaximalIdeal

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SelmerLevel

section Comp

variable {O O' : Type} [CommRing O] [CommRing O'] [Algebra O O'] {ι : Type} [Fintype ι]
  (b : Module.Basis ι O O')

structure Comp (A A' : Type) [AddCommGroup A] [Module O A] [AddCommGroup A'] [Module O' A'] where
  inc : A →+ A'
  p : ι → A' →+ A
  sum_p : ∀ x, ∑ a, b a • inc (p a x) = x
  p_inc : ∀ a c x, p a (c • inc x) = b.repr c a • x

def Comp.self : Comp b O O' where
  inc := (algebraMap O O').toAddMonoidHom
  p a := (b.coord a).toAddMonoidHom
  sum_p x := by
    conv_rhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Algebra.smul_def, mul_comm]
  p_inc a c x := by
    have : c • (algebraMap O O').toAddMonoidHom x = x • c := by simp [Algebra.smul_def, mul_comm]
    rw [this]; simp [mul_comm]

variable {b} {A A' : Type} [AddCommGroup A] [Module O A] [AddCommGroup A'] [Module O' A']

namespace Comp

variable (S : Comp b A A')


def Compat (N : Submodule O A) (N' : Submodule O' A') : Prop := ∀ x, x ∈ N' ↔ ∀ a, S.p a x ∈ N

variable {S}

variable (S)

section Coh

variable [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalAddGroup A] [ContinuousConstSMul O A]
  [TopologicalSpace A'] [DiscreteTopology A'] [IsTopologicalAddGroup A'] [ContinuousConstSMul O' A']
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] {ρ : Representation O Γ A} {ρ' : Representation O' Γ A'}
  (he : ∀ a g m, S.p a (ρ' g m) = ρ g (S.p a m))
include he

end Coh

end Comp

end Comp

section Frac

variable {O O' : Type} [CommRing O] [IsDomain O] [CommRing O'] [IsDomain O'] [Algebra O O']
  [FaithfulSMul O O'] [Module.Finite O O'] {ι : Type} [Fintype ι] (b : Module.Basis ι O O')

attribute [local instance] FractionRing.liftAlgebra

def fracBasis : Module.Basis ι (FractionRing O) (FractionRing O') :=
  b.localizationLocalization (FractionRing O) (nonZeroDivisors O) (FractionRing O')

def fracComp : Comp b (FractionRing O) (FractionRing O') where
  inc := (algebraMap (FractionRing O) (FractionRing O')).toAddMonoidHom
  p a := ((fracBasis b).coord a).toAddMonoidHom
  sum_p x := by
    conv_rhs => rw [← (fracBasis b).sum_repr x]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Algebra.smul_def, mul_comm, fracBasis]
  p_inc a c x := by
    have : c • (algebraMap (FractionRing O) (FractionRing O')).toAddMonoidHom x =
        x • algebraMap O' (FractionRing O') c := by simp [Algebra.smul_def, mul_comm]
    rw [this]
    change (fracBasis b).repr (x • _) a = _
    rw [map_smul, Finsupp.smul_apply, fracBasis, Module.Basis.localizationLocalization_repr_algebraMap,
      Algebra.smul_def (b.repr c a), smul_eq_mul, mul_comm]

theorem fracComp_inc (x : FractionRing O) :
    (fracComp b).inc x = algebraMap (FractionRing O) (FractionRing O') x := rfl

theorem frac_compat : (fracComp b).Compat (LinearMap.range (Algebra.linearMap O (FractionRing O)))
    (LinearMap.range (Algebra.linearMap O' (FractionRing O'))) := by
  intro x
  constructor
  · rintro ⟨c, rfl⟩ a
    refine ⟨b.repr c a, ?_⟩
    have := (fracComp b).p_inc a c 1
    simpa [fracComp_inc, ← Algebra.algebraMap_eq_smul_one] using this.symm
  · intro h
    choose m hm using h
    rw [← (fracComp b).sum_p x]
    refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ⟨algebraMap O O' (m a), ?_⟩
    rw [← hm, fracComp_inc]
    simp [← IsScalarTower.algebraMap_apply]

open Formalism.MainNotions.BlochKatoReduction

end Frac

section Len

variable {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O']
  [IsDiscreteValuationRing O'] [Algebra O O'] [FaithfulSMul O O'] [Module.Finite O O']
  {ι : Type} [Fintype ι] {b : Module.Basis ι O O'}

end Len

section Main

open Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.GaloisCohomology

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i)


end Main

end GlobalTheory.SelmerLevel

end
