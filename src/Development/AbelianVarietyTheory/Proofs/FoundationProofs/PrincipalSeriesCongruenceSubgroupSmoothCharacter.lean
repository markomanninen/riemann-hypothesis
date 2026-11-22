module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupInvMemStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupMulClosedStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterEqOneNearOneStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupIsOpenIsCompactStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterMulStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTrivialOnUnitsModConductorUnitCharacterValuePrStatement

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem grp_theta_datum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → Datum (grp ψ) (theta ψ) ∧ IsOpen (grp ψ) := by
  intro k _ _ _ _ n ψ hs ho
  have hoc := GlobalTheory.T.principalSeriesCongruenceSubgroup_isOpen_isCompact k n ψ hs
  have hnear := GlobalTheory.T.principalSeriesTypeCharacter_eq_one_near_one k n ψ hs
  have hone : (1 : GL (Fin n) k) ∈ grp ψ := by
    refine ⟨(KO k (Fin n)).one_mem, fun i j hij => ?_⟩
    have h0 : (1 : GL (Fin n) k).val i j = 0 := by
      simp [Matrix.one_apply_ne (ne_of_lt hij)]
    rw [h0]
    exact (GlobalTheory.T.isTrivialOnUnitsModConductor_unitCharacterValue_props k).2.2.1 _
  refine ⟨⟨hone, GlobalTheory.T.principalSeriesCongruenceSubgroup_mul_closed k n ψ ho, GlobalTheory.T.principalSeriesCongruenceSubgroup_inv_mem k n ψ ho, hoc.2, hnear.1,
    GlobalTheory.T.principalSeriesTypeCharacter_mul k n ψ ho, ?_⟩, hoc.1⟩
  obtain ⟨U, hU, hUt⟩ := hnear.2
  exact ⟨U, hU, fun g hg _ => hUt g hg⟩

end GlobalTheory.PsType
