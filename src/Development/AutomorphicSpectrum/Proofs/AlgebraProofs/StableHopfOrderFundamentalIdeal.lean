module

public import Mathlib
public import ReciprocityTheory.DualLattices.CotangentSurjective
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ProdIccFin

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
open PositivityTheory.HtPt.Rc ReciprocityTheory.PGsh.L2.SecondCohomologyLattice in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.stable_hopf_order_fundamental_ideal : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ σ : MulChar F R, IsFund p σ → (∀ χ : MulChar F R, ∃ r : NNReal, r ≠ 0 ∧ HasLen v R (OmType AA.carrier χ) r) ∧ ∀ r : ℕ → NNReal, (∀ m ∈ Finset.Icc 1 (p ^ f - 1), HasLen v R (OmType AA.carrier (σ ^ m)) (r m)) → HasLen v R (OmAA AA.carrier) (∏ m ∈ Finset.Icc 1 (p ^ f - 1), r m) := by
  intro p _ C _ _ _ v R _ _ hv hvp F _ _ _ _ f hf N _ _ _ _ AA hAA σ hσ
  have := hv.hom_inj.isDomain
  have hfg := fg_of_isLat AA.lat
  constructor
  · intro χ
    obtain ⟨-, -, cO, -, -, hcO0, -, -, hcO⟩ := lens p C v R hv hvp N (fun x => by
      rw [← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul]) AA
    obtain ⟨r, hr⟩ := exists_hasLen hv _ _ (eig_fg hv _ hfg χ) (sq_aug_fg hv _ hfg)
    refine ⟨r, ?_, hr⟩
    obtain ⟨s, hs0, hs⟩ := (len_ne_zero_iff hv hcO).1 hcO0
    refine (len_ne_zero_iff hv hr).2 ⟨s, hs0, fun m => ?_⟩
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    have h := hs (Submodule.Quotient.mk ⟨g, eig_le_aug _ χ g.2⟩)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h ⊢
    exact h
  · intro r hr
    obtain ⟨u, hu⟩ := exists_inv_card (F := F) hv p hvp
    have proj_mem (χ : MulChar F R) (S : Submodule R (N → C))
        (hS : FStable (F := F) S) {g : N → C} (hg : g ∈ S) : projL χ g ∈ S := by
      have heq : projL χ g = u • ∑ a : Fˣ, χ⁻¹ (a : F) • (fun x => g ((a : F) • x)) := by
        funext x
        rw [projL_apply, Pi.smul_apply, Finset.sum_apply, Algebra.smul_def, hu]
        exact congrArg _ (Finset.sum_congr rfl fun a _ => (Algebra.smul_def _ _).symm)
      rw [heq]
      exact S.smul_mem _ (S.sum_mem fun a _ => S.smul_mem _ (hS _ g hg))
    have proj_eig (χ : MulChar F R) {g : N → C} (hg : g ∈ augIdeal AA.carrier) :
        projL χ g ∈ eig AA.carrier χ := by
      rw [mem_aug] at hg
      refine ⟨proj_mem χ _ hAA hg.1, fun a x => ?_⟩
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
    obtain ⟨hord, -, -, -, hsep⟩ := GlobalTheory.CompanionTheory.Ar.GR.FundGen.main p C v R hv hvp F f hf σ hσ
    have hn : p ^ f - 1 = Fintype.card Fˣ := by rw [Fintype.card_units, hf]
    rw [hn] at hr hord ⊢
    have hsum := sum_projL (C := C) (N := N) σ (fun a ha => by
      by_contra hne
      have := hsep a 1 (fun h => hne (Units.ext h))
      rw [ha, map_one, sub_self, map_zero, map_zero] at this
      exact zero_ne_one this)
    let Ψ : augIdeal AA.carrier →ₗ[R]
        ((i : Fin (Fintype.card Fˣ)) → OmType AA.carrier (σ ^ ((i : ℕ) + 1))) :=
      LinearMap.pi fun i => Submodule.mkQ _ ∘ₗ
        (projL (σ ^ ((i : ℕ) + 1))).restrict fun _ hg => proj_eig _ hg
    have hsurj : Function.Surjective Ψ := by
      intro y
      choose g hg using fun i => Submodule.Quotient.mk_surjective _ (y i)
      refine ⟨⟨∑ i, (g i : N → C), Submodule.sum_mem _ fun i _ => eig_le_aug _ _ (g i).2⟩, ?_⟩
      funext i
      rw [← hg i]
      refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
      show projL (σ ^ ((i : ℕ) + 1)) (∑ i, (g i : N → C)) = g i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_eq_single i, projL_self _ (g i).2]
      · intro j _ hj
        refine projL_ne (fun h => hj ?_) (g j).2
        rw [pow_succ, pow_succ] at h
        exact Fin.ext (pow_injOn_Iio_orderOf (by rw [hord]; exact j.2) (by rw [hord]; exact i.2)
          (mul_right_cancel h).symm)
      · simp
    have hker : (sqIdeal (augIdeal AA.carrier)).comap (augIdeal AA.carrier).subtype =
        LinearMap.ker Ψ := by
      ext g
      rw [LinearMap.mem_ker, funext_iff]
      constructor
      · intro hg i
        have hstable : FStable (F := F) (sqIdeal (augIdeal AA.carrier)) :=
          fun a _ ha => sq_pull (LinearMap.lsmul F N a).toAddMonoidHom
            AA.carrier AA.carrier (hAA a) ha
        exact (Submodule.Quotient.mk_eq_zero _).2 (proj_mem _ _ hstable hg)
      · intro hg
        show (g : N → C) ∈ sqIdeal (augIdeal AA.carrier)
        rw [← hsum g]
        refine Submodule.sum_mem _ fun i _ => ?_
        have h1 : (Submodule.Quotient.mk
            (⟨projL (σ ^ ((i : ℕ) + 1)) (g : N → C), proj_eig _ g.2⟩ :
              eig AA.carrier (σ ^ ((i : ℕ) + 1))) :
            OmType AA.carrier (σ ^ ((i : ℕ) + 1))) = 0 := hg i
        rw [Submodule.Quotient.mk_eq_zero] at h1
        exact h1
    rw [prod_Icc_fin]
    exact hasLen_of_equiv ((Submodule.quotEquivOfEq _ _ hker).trans
      (Ψ.quotKerEquivOfSurjective hsurj)) (Tot.hasLen_pi _ _ fun i =>
        hr _ (Finset.mem_Icc.2 ⟨by omega, i.2⟩))
