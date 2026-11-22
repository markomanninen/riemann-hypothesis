module

public import Mathlib
public import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.cmFree :
    ∀ {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B] [Module.Finite A B]
      [Module.Free A B], ReciprocityTheory.CA.IsCM A → ReciprocityTheory.CA.IsCM B := by
  intro A B _ _ _ _ _ _ _ h
  obtain ⟨hN, n, hdim, rs, hlen, hmem, hreg⟩ := h
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have hm : (maximalIdeal B).comap (algebraMap A B) = maximalIdeal A :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal B))
  refine ⟨IsNoetherianRing.of_finite A B, n, ?_, rs.map (algebraMap A B), by simpa using hlen, ?_,
    hreg.of_faithfullyFlat⟩
  · rw [← hdim]
    exact ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj
  · intro r hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    have := hmem a ha
    rw [← hm] at this
    exact this
