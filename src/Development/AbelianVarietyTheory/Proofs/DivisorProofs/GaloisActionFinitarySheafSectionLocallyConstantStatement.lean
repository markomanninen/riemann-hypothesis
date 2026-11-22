module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisActionFinitarySheafSectionLocallyConstant
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantApply

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

open GlobalTheory.EtC.GalSmooth in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisAction_finitarySheafSection_locallyConstant :
    ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F →
      ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
        (x : Sec F (Spec (CommRingCat.of Ω))),
        IsLocallyConstant (fun τ : Ω ≃ₐ[K] Ω =>
          Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) x) := by
  intro R _ F hF K Ω _ _ _ _ x
  classical
  have elements :=
    (GlobalTheory.T.preservesFilteredColimits_moduleCat_iff_forget_iff_elements
      (ULift.{1} R) (onRings F)).2.mp hF
  obtain ⟨s, y, hy⟩ := (elements (Finset Ω) (diag Ω) (cocone Ω) (coconeIsColimit Ω)).1 x
  have restrict_eq (τ : Ω ≃ₐ[K] Ω) :
      Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) x =
        ((onRings F).map (CommRingCat.ofHom ((τ : Ω →+* Ω).comp (sr Ω s).subtype))).hom y := by
    rw [← hy, cocone_ι]
    show _ = ((onRings F).map (CommRingCat.ofHom (sr Ω s).subtype ≫
      CommRingCat.ofHom (τ : Ω →+* Ω))).hom y
    rw [Functor.map_comp]
    rfl
  rw [IsLocallyConstant.iff_eventually_eq]
  intro τ₀
  have : FiniteDimensional K (IntermediateField.adjoin K (s : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin (fun a _ => Algebra.IsIntegral.isIntegral a)
  have hopen : IsOpen {σ : Ω ≃ₐ[K] Ω |
      τ₀⁻¹ * σ ∈ (IntermediateField.adjoin K (s : Set Ω)).fixingSubgroup} :=
    (IntermediateField.fixingSubgroup_isOpen _).preimage (continuous_const.mul continuous_id)
  filter_upwards [hopen.mem_nhds (by simp)] with τ hτ
  have hs : Set.EqOn (τ : Ω →+* Ω) (τ₀ : Ω →+* Ω) (s : Set Ω) := fun b hb => by
    have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ b
      (IntermediateField.subset_adjoin K _ hb)
    simpa [AlgEquiv.mul_apply] using congrArg τ₀ hfix
  have hc : (τ : Ω →+* Ω).comp (sr Ω s).subtype =
      (τ₀ : Ω →+* Ω).comp (sr Ω s).subtype := by
    ext a
    exact RingHom.eqOn_set_closure hs a.2
  rw [restrict_eq τ, restrict_eq τ₀, hc]
