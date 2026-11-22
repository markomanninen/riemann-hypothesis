module

public import Mathlib

@[expose] public section

namespace GlobalTheory

attribute [local instance] Subgroup.finiteIndex_of_finite_quotient

attribute [local instance] Ideal.Quotient.field in
theorem Ideal.Quotient.normal_of_profinite
    {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (G : Type) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup G]
    [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B] [Algebra.IsInvariant A B G]
    (P : Ideal A) (Q : Ideal B) [Q.LiesOver P] [P.IsMaximal] [Q.IsMaximal] :
    Normal (A ⧸ P) (B ⧸ Q) := by
  have hint : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral_of_profinite (G := G)
  have hint' : Algebra.IsIntegral (A ⧸ P) (B ⧸ Q) := Ideal.Quotient.algebra_isIntegral_of_liesOver Q P
  refine normal_iff.2 fun ξ => ⟨Algebra.IsIntegral.isIntegral ξ, ?_⟩
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective ξ
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (stabilizer_isOpen G b) (one_mem _)
  let B' := FixedPoints.subalgebra A B N.1.1
  let b' : B' := ⟨b, fun g => hN g.2⟩
  let Q' : Ideal B' := Q.under B'
  have hintB : Algebra.IsIntegral B' B := Algebra.IsIntegral.tower_top A
  have hQ' : Q'.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal Q
  have : Q'.LiesOver P := ⟨by
    rw [Ideal.under_under (A := A) (B := B') (C := B)]
    exact Ideal.LiesOver.over⟩
  have hn : Normal (A ⧸ P) (B' ⧸ Q') := Ideal.Quotient.normal (G ⧸ N.1.1) P Q'
  let f : (B' ⧸ Q') →ₐ[A ⧸ P] B ⧸ Q :=
    { toRingHom := Ideal.quotientMap _ B'.val le_rfl,
      commutes' := Quotient.ind fun _ ↦ rfl }
  have hf : Function.Injective f := f.toRingHom.injective
  have hfb : f (Ideal.Quotient.mk Q' b') = Ideal.Quotient.mk Q b := rfl
  rw [← hfb, minpoly.algHom_eq f hf]
  have hs := hn.splits (Ideal.Quotient.mk Q' b')
  have := hs.map f.toRingHom
  rw [Polynomial.map_map] at this
  have hc : (f : (B' ⧸ Q') →+* B ⧸ Q).comp (algebraMap (A ⧸ P) (B' ⧸ Q')) = algebraMap (A ⧸ P) (B ⧸ Q) := f.comp_algebraMap
  simpa only [AlgHom.toRingHom_eq_coe, hc] using this

end GlobalTheory
