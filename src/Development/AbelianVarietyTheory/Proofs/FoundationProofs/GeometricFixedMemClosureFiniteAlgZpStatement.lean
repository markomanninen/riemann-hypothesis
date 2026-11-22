module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricFixedMemClosureFiniteAlgZp
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

@[expose] public section

open GlobalTheory.K5

private theorem mem_geoField_of_fixed_local {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω]
    [Algebra (O0 p) Ω] (h : IsClo p Ω) (x : Ω)
    (hx : ∀ g ∈ Ggeo (p := p) Ω, g x = x) :
    x ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {y : Ω | IsAlgZp (p := p) y}) := by
  haveI := h.clo
  haveI : CharZero Ω := Basic.charZero_of_isClo h
  let F : Subfield Ω := Subfield.closure
    (Set.range (algebraMap (O0 p) Ω) ∪ {y : Ω | IsAlgZp (p := p) y})
  have hR : ∀ a : O0 p, algebraMap (O0 p) Ω a ∈ F := fun a =>
    Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
  let f : O0 p →+* F := (algebraMap (O0 p) Ω).codRestrict F hR
  have hf : (algebraMap F Ω).comp f = algebraMap (O0 p) Ω := by ext; rfl
  have hfi : Function.Injective f := fun a b hab => h.inj (congrArg Subtype.val hab)
  have hAlg : Algebra.IsAlgebraic F Ω := ⟨fun a => by
    obtain ⟨P, hP0, hP⟩ := h.alg.isAlgebraic a
    refine ⟨P.map f, (Polynomial.map_ne_zero_iff hfi).2 hP0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hf, ← Polynomial.aeval_def, hP]⟩
  letI : Algebra.IsAlgebraic F Ω := hAlg
  haveI : IsAlgClosure F Ω := ⟨h.clo, hAlg⟩
  haveI : CharZero F := ⟨fun m n e => CharZero.cast_injective (congrArg Subtype.val e)⟩
  haveI : IsGalois F Ω := inferInstance
  have hbot : x ∈ (⊥ : IntermediateField F Ω) := by
    refine (InfiniteGalois.mem_bot_iff_fixed x).2 fun σ => ?_
    let τ : Ω ≃ₐ[O0 p] Ω := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv)
      (fun a => σ.commutes ⟨_, hR a⟩)
    have hτ : τ ∈ Ggeo (p := p) Ω := fun y hy =>
      σ.commutes ⟨y, Subfield.subset_closure (Or.inr hy)⟩
    exact hx τ hτ
  obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.1 hbot
  exact y.2

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_fixed_mem_closure_finite_algZp : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ x : Ω, (∀ g ∈ Ggeo (p := p) Ω, g x = x) → ∃ S : Finset Ω, (∀ s ∈ S, IsAlgZp (p := p) s) ∧
    x ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S : Set Ω)) := by
  intro p hp Ω hΩ hΩalg h x hx
  obtain ⟨S, hS, hxS⟩ := GlobalTheory.K5.GeoFix.exists_finset_of_mem_closure _ _
    (mem_geoField_of_fixed_local h x hx)
  exact ⟨S, fun s hs => hS hs, hxS⟩
