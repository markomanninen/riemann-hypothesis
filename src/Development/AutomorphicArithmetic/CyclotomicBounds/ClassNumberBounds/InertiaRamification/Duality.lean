module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ConductorLocalPartDvdIff

@[expose] public section

namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N] (l : ℕ) [Fact l.Prime]

private theorem annihilator_eq_iso (H : Subgroup (ZMod N)ˣ) :
    annihilator ℂ (H : Set (ZMod N)ˣ) =
      (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod N) ℂ H).ofDual := by
  ext χ
  simp [mem_annihilator_iff]

private theorem charKer_eq_iso (X : Subgroup (DirichletCharacter ℂ N)) :
    charKer X =
      (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod N) ℂ).symm (OrderDual.toDual X) := by
  ext m
  simp [charKer, Subgroup.mem_iInf, MonoidHom.mem_ker, Units.ext_iff]

private theorem card_annihilator_eq (H : Subgroup (ZMod N)ˣ) :
    Nat.card (annihilator ℂ (H : Set (ZMod N)ˣ)) = H.index := by
  rw [annihilator_eq_iso, MulChar.card_subgroupOrderIsoSubgroupMulChar]
  rfl

theorem annihilator_charKer (X : Subgroup (DirichletCharacter ℂ N)) (H : Subgroup (ZMod N)ˣ) :
    annihilator ℂ (charKer X : Set (ZMod N)ˣ) = X ∧
      charKer (annihilator ℂ (H : Set (ZMod N)ˣ)) = H ∧ Nat.card X = (charKer X).index := by
  have h1 : annihilator ℂ (charKer X : Set (ZMod N)ˣ) = X := by
    rw [charKer_eq_iso, annihilator_eq_iso, OrderIso.apply_symm_apply]
    rfl
  refine ⟨h1, ?_, ?_⟩
  · rw [annihilator_eq_iso, charKer_eq_iso]
    simp
  · rw [← card_annihilator_eq, h1]

end KStar.Ram
