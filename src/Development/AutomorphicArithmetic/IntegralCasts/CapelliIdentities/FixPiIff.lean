module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.LevelModule
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwThetaEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FixedSubgroup

@[expose] public section

namespace UpperTheory.Reformulated.B.Gr34

open ValuativeRel IsLocalRing UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools
  UpperTheory.V.Pa UpperTheory.V.Pa.Lev

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem fix_pi_iff {ι : Type} [Finite ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)]
    {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (∀ i, G i) M)
    (K : ∀ i, Subgroup (G i)) (m : M) :
    (∀ k ∈ Subgroup.pi Set.univ K, ρ k m = m) ↔
      ∀ j, ∀ k ∈ K j, ρ (Pi.mulSingle j k) m = m := by
  refine ⟨fun h j k hk => h _ fun i _ => ?_, fun h k hk => ?_⟩
  · rcases eq_or_ne i j with rfl | hij
    · simpa using hk
    · simp [Pi.mulSingle_eq_of_ne hij]
  · let H : Subgroup (∀ i, G i) :=
      { carrier := {g | ρ g m = m}
        one_mem' := by simp
        mul_mem' := fun {a b} (ha : ρ a m = m) (hb : ρ b m = m) =>
          show ρ (a * b) m = m by simp [ha, hb]
        inv_mem' := fun {a} (ha : ρ a m = m) => show ρ a⁻¹ m = m by
          conv_lhs => rw [← ha, Representation.inv_self_apply] }
    exact Subgroup.pi_mem_of_mulSingle_mem (H := H) k fun i => h i _ (hk i trivial)

theorem mem_UC {L : Type} [Field L] [NumberField L] {n q : ℕ} {w : Fin q → Plc L}
    {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (ρ : Representation A (GV n w) M)
    (C : ∀ j : Fin q, Subgroup 𝓀[(w j).adicCompletion L]ˣ) (m : M) :
    m ∈ fixd ρ (UC n w C) ↔ ∀ j, m ∈ fixd (ρ.comp (atJ n w j)) (iwC _ n (C j)) :=
  fix_pi_iff (G := fun j => GLw n (w j)) ρ _ m

end UpperTheory.Reformulated.B.Gr34
