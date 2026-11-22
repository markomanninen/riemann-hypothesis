module

public import Mathlib
public import ReciprocityTheory.DualLattices.CotangentSurjective
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ProdIccFin

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open PositivityTheory.HtPt.Rc ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.stable_hopf_order_subgroup_characters : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ (K : Submodule F N) (χ : MulChar F R) (a b c : NNReal), HasLen v R (OmType (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) χ) a → HasLen v R (OmType (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) χ) b → HasLen v R (OmType AA.carrier χ) c → a * b ≤ c := by
  intro p _ C _ _ _ v R _ _ hv hvp F _ _ _ _ f _ N _ _ _ _ AA hAA K χ a b c ha hb hc
  have hu := exists_inv_card (F := F) hv p hvp
  have hQ : FStable (F := F) (AA.carrier.comap (LinearMap.funLeft R C K.mkQ)) := by
    intro a g hg
    have hg' := hAA a _ hg
    show LinearMap.funLeft R C K.mkQ _ ∈ AA.carrier
    convert hg' using 1
    funext x
    show g (a • K.mkQ x) = g (K.mkQ (a • x))
    rw [map_smul]
  have hsq : FStable (F := F) (sqIdeal (augIdeal AA.carrier)) :=
    fun a _ hg => sq_pull (LinearMap.lsmul F N a).toAddMonoidHom _ _ (hAA a) hg
  have proj_mem {X : Type} [AddCommGroup X] [Module F X] (χ : MulChar F R)
      (S : Submodule R (X → C)) (hS : FStable (F := F) S) {g : X → C} (hg : g ∈ S) :
      projL χ g ∈ S := by
    obtain ⟨u, hu⟩ := hu
    have hproj : projL χ g = u • ∑ a : Fˣ, χ⁻¹ (a : F) • (fun x => g ((a : F) • x)) := by
      funext x
      rw [projL_apply, Pi.smul_apply, Finset.sum_apply, Algebra.smul_def, hu]
      exact congrArg _ (Finset.sum_congr rfl fun a _ => (Algebra.smul_def _ _).symm)
    rw [hproj]
    exact S.smul_mem _ (S.sum_mem fun a _ => S.smul_mem _ (hS _ g hg))
  have proj_eig {X : Type} [AddCommGroup X] [Module F X] (χ : MulChar F R)
      {M : Submodule R (X → C)} (hM : FStable (F := F) M) {g : X → C} (hg : g ∈ augIdeal M) :
      projL χ g ∈ eig M χ := by
    rw [mem_aug] at hg
    refine ⟨proj_mem χ M hM hg.1, fun a x => ?_⟩
    by_cases ha : a = 0
    · rw [ha, zero_smul, MulChar.map_zero, map_zero, zero_mul, projL_apply]
      simp only [smul_zero, hg.2, mul_zero, Finset.sum_const_zero]
    · obtain ⟨a, rfl⟩ := isUnit_iff_ne_zero.2 ha
      rw [projL_apply, projL_apply, mul_left_comm, Finset.mul_sum Finset.univ _ (algebraMap R C _),
        ← Equiv.sum_comp (Equiv.mulRight a) (fun b : Fˣ => algebraMap R C (χ (a : F)) *
          (algebraMap R C (χ⁻¹ (b : F)) * g ((b : F) • x)))]
      congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Equiv.coe_mulRight, Units.val_mul, mul_smul, ← mul_assoc, ← map_mul, map_mul χ⁻¹,
        mul_left_comm, mul_inv_unit, mul_one]
  rw [mul_comm]
  refine len_mul_le hv (omMap χ K.mkQ (AA.carrier.comap (LinearMap.funLeft R C K.mkQ)) AA.carrier
      (fun _ hg => hg))
    (omMap χ K.subtype AA.carrier (AA.carrier.map (LinearMap.funLeft R C K.subtype))
      (fun _ hg => Submodule.mem_map_of_mem hg)) ?_ ?_ hb hc ha
  · intro y
    obtain ⟨⟨h, hh⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨g, hg, hgh⟩ := hh.1
    have hga : g ∈ augIdeal AA.carrier := by
      rw [mem_aug]
      refine ⟨hg, ?_⟩
      have := ((mem_aug _ _).1 (eig_le_aug _ χ hh)).2
      rw [← hgh] at this
      exact this
    refine ⟨Submodule.Quotient.mk ⟨projL χ g, proj_eig χ hAA hga⟩, ?_⟩
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    show LinearMap.funLeft R C K.subtype (projL χ g) = h
    rw [← projL_funLeft, ← projL_self χ hh, ← hgh]
  · intro x hx
    obtain ⟨⟨g, hg⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' := (Submodule.Quotient.mk_eq_zero _).1 hx
    obtain ⟨q, hq, hgq⟩ := om_exact hv AA K.subtype.toAddMonoidHom K.mkQ.toAddMonoidHom
      K.mkQ_surjective Subtype.val_injective (range_subtype_eq K) g (eig_le_aug _ χ hg) hx'
    refine ⟨Submodule.Quotient.mk ⟨projL χ q, proj_eig χ hQ hq⟩, ?_⟩
    symm
    refine (Submodule.Quotient.eq _).2 ?_
    show g - LinearMap.funLeft R C K.mkQ (projL χ q) ∈ sqIdeal (augIdeal AA.carrier)
    have := proj_mem χ _ hsq hgq
    rw [map_sub, projL_self χ hg] at this
    rw [← projL_funLeft]
    exact this
