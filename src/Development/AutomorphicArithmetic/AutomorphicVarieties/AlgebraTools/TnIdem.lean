module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TopNilDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TnAlgMapSmulMem

@[expose] public section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.exists_idem_topNil :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (κ : Type) (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] (T : κ → Module.End R M), (∀ i j, Commute (T i) (T j)) →
      ∃ e ∈ Algebra.adjoin R (Set.range T), IsIdempotentElem e ∧ LinearMap.range e = topNil (IsLocalRing.maximalIdeal R) T := by
  intro R _ _ _ _ κ M _ _ _ T hT
  classical
  let S := Algebra.adjoin R (Set.range T)
  have : Module.Finite R S := by
    have : IsNoetherian R (Subalgebra.toSubmodule S) := inferInstance
    exact (inferInstance : Module.Finite R (Subalgebra.toSubmodule S))
  have : IsMulCommutative S := Algebra.isMulCommutative_adjoin R (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hT i j)
  let _ : CommRing S := by
    open scoped IsMulCommutative in
    exact inferInstance
  let t : κ → S := fun i => ⟨T i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  obtain ⟨e, he, -, hx⟩ := topNil_eq_idem R S κ t
  have hfun : (fun i => (Algebra.lsmul R R M) (t i)) = T := by
    funext i
    rfl
  have he' : IsIdempotentElem (e : Module.End R M) := congrArg Subtype.val he
  refine ⟨(e : Module.End R M), e.2, he', ?_⟩
  ext x
  have h := hx M x
  rw [hfun] at h
  rw [h]
  constructor
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun he' y
  · intro h2
    exact ⟨x, h2⟩
