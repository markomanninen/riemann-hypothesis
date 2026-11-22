module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyEndCharpolySpecStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomDegreeIntegerCombinationIsHomogeneousStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativePolynomialFunctionEqNormFormStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyCompIffAndDegreeMul

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem deg_aeval_eq_prod_aroots :
    ∀ (K : Type) [Field K] (A : AbVar K) (f : End A) (Ω : Type) [Field Ω]
      [IsAlgClosed Ω] [Algebra ℚ Ω] (R : Polynomial ℤ),
      algebraMap ℚ Ω (deg (Polynomial.aeval f R).asHom : ℚ) =
        ((((charpoly f).map (Int.castRingHom ℚ)).aroots Ω).map
          (fun a => Polynomial.aeval a R)).prod := by
  intro K _ A f Ω _ _ _ R
  obtain ⟨⟨hm, hd, hev⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec K A f
  refine GlobalTheory.T.multiplicative_polynomialFunction_eq_normForm Ω A.dim
    (fun F => (deg (Polynomial.aeval f F).asHom : ℚ))
    ((charpoly f).map (Int.castRingHom ℚ)) ?_ ?_ ?_ ?_ ?_ R
  · intro F G
    have h := (isIsogeny_comp_iff_and_deg_comp K A A A
      (Polynomial.aeval f G).asHom (Polynomial.aeval f F).asHom rfl rfl).2
    rw [map_mul, End.mul_asHom, h, Nat.cast_mul, mul_comm]
  · intro n u
    obtain ⟨Φ, hΦ, hΦev⟩ := GlobalTheory.T.homDegree_integerCombination_isHomogeneous
      K A A rfl n (fun i => (Polynomial.aeval f (u i)).asHom)
    refine ⟨Φ, hΦ, fun m => ?_⟩
    rw [hΦev m]
    change (deg (∑ i, m i • End.addEquiv (Polynomial.aeval f (u i))) : ℚ) =
      (deg (End.addEquiv (Polynomial.aeval f (∑ i, m i • u i))) : ℚ)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul]
  · exact hm.map _
  · rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _)]
    exact hd
  · intro n
    rw [Polynomial.eval_intCast_map, Int.cast_id, hev n]
    have e : Polynomial.aeval f (Polynomial.C n - Polynomial.X) = ((n : End A) - f) := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, eq_intCast]
    rw [e]
    exact Int.cast_natCast _

end GlobalTheory.AV.AbVar
