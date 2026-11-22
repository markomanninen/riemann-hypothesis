module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderFundamentalCharacter
public import ReciprocityTheory.DualLattices.CotangentSurjective
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_fundamental_character : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ g ∈ augIdeal AA.carrier, (∀ χ : MulChar F R, proj χ g ∈ eig AA.carrier χ) ∧ g = ∑ m ∈ Finset.Icc 1 (p ^ f - 1), proj (σ ^ m) g ∧ (g ∈ afFun p AA.carrier → ∀ χ : MulChar F R, proj χ g ∈ afFun p AA.carrier) ∧ (∀ K : Submodule F N, g ∈ invFun AA.carrier K.toAddSubgroup → ∀ χ : MulChar F R, proj χ g ∈ invFun AA.carrier K.toAddSubgroup) ∧ (g ∈ sqIdeal (augIdeal AA.carrier) → ∀ χ : MulChar F R, proj χ g ∈ sqIdeal (augIdeal AA.carrier)) := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hc N _ _ _ _ AA hFS σ hσ g hg
  have sum_Icc_pow_eq_mul_sum_range (ζ : R) (n : ℕ) :
      ∑ m ∈ Finset.Icc 1 n, ζ ^ m = ζ * ∑ m ∈ Finset.range n, ζ ^ m := by
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ, mul_add, pow_succ']
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj
  have : IsDomain R := Function.Injective.isDomain (algebraMap R C) hinj
  obtain ⟨h0, w, hw⟩ := PositivityTheory.HtPt.Rb.exists_inv_card (F := F) hv hp hc
  have hgA : g ∈ AA.carrier := (Submodule.mem_inf.1 hg).1
  have hg0 : g 0 = 0 := by simpa using LinearMap.mem_ker.1 (Submodule.mem_inf.1 hg).2
  refine ⟨fun χ => ⟨PositivityTheory.HtPt.Rb.proj_mem hw AA.carrier χ g (fun a => hFS a g hgA),
      fun a x => PositivityTheory.HtPt.Rb.proj_smul_apply χ g hg0 a x⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hord, -, -, -, hsep⟩ := FundGen.main p C v R hv hp F f hc σ hσ
    have hcardU : Fintype.card Fˣ = p ^ f - 1 := by rw [Fintype.card_units, hc]
    have hσq : σ ^ (p ^ f - 1) = 1 := hord ▸ pow_orderOf_eq_one σ
    have hz : ∀ a : Fˣ, ∑ m ∈ Finset.Icc 1 (p ^ f - 1), (σ ^ m)⁻¹ (a : F) =
        if a = 1 then ((p ^ f - 1 : ℕ) : R) else 0 := by
      intro a
      have hpow : ∀ m : ℕ, (σ ^ m)⁻¹ (a : F) = (σ⁻¹ (a : F)) ^ m := fun m => by
        rw [← inv_pow, MulChar.pow_apply_coe]
      simp only [hpow]
      split_ifs with ha
      · subst ha
        simp
      · have hroot : (σ⁻¹ (a : F)) ^ (p ^ f - 1) = 1 := by
          rw [← MulChar.pow_apply_coe, inv_pow, hσq, inv_one, MulChar.one_apply_coe]
        have hneRoot : σ⁻¹ (a : F) ≠ 1 := by
          intro h1
          have hne : (a : F) ≠ 1 := fun h => ha (Units.val_eq_one.1 h)
          have hs := hsep (a : F) 1 hne
          have hsa : σ (a : F) = 1 := by
            have := PositivityTheory.HtPt.Rb.inv_mul_apply σ a
            rwa [h1, one_mul] at this
          rw [hsa, MulChar.map_one, sub_self, map_zero, map_zero] at hs
          exact zero_ne_one hs
        rw [sum_Icc_pow_eq_mul_sum_range]
        have hgeom := geom_sum_mul (σ⁻¹ (a : F)) (p ^ f - 1)
        rw [hroot, sub_self] at hgeom
        rw [(mul_eq_zero.1 hgeom).resolve_right (sub_ne_zero.2 hneRoot), mul_zero]
    funext x
    have hsum : (∑ m ∈ Finset.Icc 1 (p ^ f - 1), proj (σ ^ m) g) x =
        (Fintype.card Fˣ : C)⁻¹ * ∑ a : Fˣ, algebraMap R C
          (∑ m ∈ Finset.Icc 1 (p ^ f - 1), (σ ^ m)⁻¹ (a : F)) * g ((a : F) • x) := by
      rw [Finset.sum_apply]
      simp only [proj]
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_mul]
    rw [hsum]
    simp only [hz, apply_ite (algebraMap R C), ite_mul, map_zero, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, Units.val_one, one_smul, map_natCast]
    rw [← hcardU, inv_mul_cancel_left₀ h0]
  · intro haf χ
    have hA : g ∈ AA.carrier := (Submodule.mem_inf.1 haf).1
    have hadd : ∀ x y, g (x + y) - g x - g y ∈ pInt (C := C) R p := (Submodule.mem_inf.1 haf).2
    refine PositivityTheory.HtPt.Rb.proj_mem hw _ χ g fun a => Submodule.mem_inf.2 ⟨hFS a g hA, fun x y => ?_⟩
    simpa [smul_add] using hadd (a • x) (a • y)
  · intro K hK χ
    obtain ⟨hA, hinv⟩ := hK
    refine PositivityTheory.HtPt.Rb.proj_mem hw _ χ g fun a => ⟨hFS a g hA, fun y k hk => ?_⟩
    simp only [smul_add]
    exact hinv (a • y) (a • k) (K.smul_mem a hk)
  · intro hsq χ
    refine PositivityTheory.HtPt.Rb.proj_mem hw _ χ g fun a => ?_
    let L : (N → C) →ₗ[R] (N → C) := LinearMap.funLeft R C (fun x : N => a • x)
    have haug (u : N → C) (hu : u ∈ augIdeal AA.carrier) : L u ∈ augIdeal AA.carrier := by
      obtain ⟨huA, hu0⟩ := Submodule.mem_inf.1 hu
      refine Submodule.mem_inf.2 ⟨hFS a u huA, LinearMap.mem_ker.2 ?_⟩
      have huZero : u 0 = 0 := by simpa using LinearMap.mem_ker.1 hu0
      simpa [L, smul_zero] using huZero
    have hle : sqIdeal (augIdeal AA.carrier) ≤ (sqIdeal (augIdeal AA.carrier)).comap L := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, hu, u', hu', rfl⟩
      exact Submodule.subset_span ⟨L u, haug u hu, L u', haug u' hu', rfl⟩
    exact hle hsq
