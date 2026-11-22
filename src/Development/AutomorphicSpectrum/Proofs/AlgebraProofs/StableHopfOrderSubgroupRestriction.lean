module

public import Mathlib
public import ReciprocityTheory.DualLattices.CotangentSurjective
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RangeSubtypeEq

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem subquoHopfOrder : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ (K : Submodule F N) [Fintype K] [DecidableEq K] [Fintype (N ⧸ K)] [DecidableEq (N ⧸ K)], (∃ AK : HopfOrder (C := C) R K, AK.carrier = (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) ∧ FStable (F := F) AK.carrier) ∧ (∃ AQ : HopfOrder (C := C) R (N ⧸ K), AQ.carrier = (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) ∧ FStable (F := F) AQ.carrier) ∧ invFun AA.carrier K.toAddSubgroup = (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))).map (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K)) ∧ ∀ c cQ cK, HasColen R v AA.carrier c → HasColen R v (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) cQ → HasColen R v (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) cK → c = cQ ^ Fintype.card K * cK ^ Fintype.card (N ⧸ K) :=
  by
    intro p _ C _ _ _ v R _ _ hv _ F _ _ _ _ f _ N _ _ _ _ AA hAA K _ _ _ _
    have hres : FStable (F := F)
        (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) := by
      rintro a _ ⟨g, hg, rfl⟩
      exact ⟨_, hAA a g hg, rfl⟩
    have hquo : FStable (F := F)
        (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) := by
      intro a g hg
      have h := hAA a _ hg
      show LinearMap.funLeft R C (K.mkQ : N → N ⧸ K) _ ∈ AA.carrier
      convert h using 1
      funext x
      show g (K.mkQ (a • x)) = g (a • K.mkQ x)
      rw [map_smul]
    have hrange : K.subtype.toAddMonoidHom.range = K.mkQ.toAddMonoidHom.ker := by
      ext x
      simp [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨AK, hAK⟩ := PositivityTheory.HtPt.Rc.exists_res hv AA
        K.subtype.toAddMonoidHom Subtype.val_injective
      exact ⟨AK, hAK, hAK ▸ hres⟩
    · obtain ⟨AQ, hAQ⟩ := PositivityTheory.HtPt.Rc.exists_quo hv AA
        K.mkQ.toAddMonoidHom K.mkQ_surjective
      exact ⟨AQ, hAQ, hAQ ▸ hquo⟩
    · exact PositivityTheory.HtPt.Rc.invFun_eq _ K.mkQ.toAddMonoidHom
        K.mkQ_surjective _ (fun x => by simp)
    · intro c cQ cK hc hQ hK
      exact PositivityTheory.HtPt.Rc.colen_ses hv AA K.subtype.toAddMonoidHom
        Subtype.val_injective K.mkQ.toAddMonoidHom K.mkQ_surjective hrange c cQ cK hc hQ hK

end GlobalTheory.CompanionTheory.Ar.GR
