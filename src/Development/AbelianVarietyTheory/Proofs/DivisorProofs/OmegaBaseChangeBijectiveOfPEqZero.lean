module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero

@[expose] public section

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDiv

theorem liftSemi_toBaseChange_cot_bijective (R R' A : Type) [CommRing R] [CommRing R'] [Algebra R R']
    [CommRing A] [Bialgebra R A] : Function.Bijective (liftSemi (toBaseChange R R' A).cot) := by
  have heq : (counitAlgHom R' (R' ⊗[R] A)).comp
      ((AlgEquiv.refl : (R' ⊗[R] A) ≃ₐ[R'] (R' ⊗[R] A)) : (R' ⊗[R] A) →ₐ[R'] (R' ⊗[R] A)) =
      AugCot.baseChangeAug R' (counitAlgHom R A) := by
    apply Algebra.TensorProduct.ext'
    intro r a
    simp [AugCot.baseChangeAug_tmul, Algebra.smul_def, mul_comm]
  let E : R' ⊗[R] Cot R A ≃ₗ[R'] Cot R' (R' ⊗[R] A) :=
    (AugCot.baseChangeEquiv R' (counitAlgHom R A)).trans (AugCot.congr AlgEquiv.refl heq)
  have hmap : liftSemi (toBaseChange R R' A).cot = E.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r m
    obtain ⟨a, rfl⟩ := AugCot.d_surjective (counitAlgHom R A) m
    simp only [liftSemi_tmul, LinearEquiv.coe_coe, E, LinearEquiv.trans_apply,
      AugCot.baseChangeEquiv_tmul_d, map_smul, AugCot.congr_d]
    exact congrArg (r • ·) ((toBaseChange R R' A).cot_d a)
  rw [hmap]
  exact E.bijective

end PDiv

namespace PDivGroup

theorem omega_baseChange_bijective {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (R' : Type)
    [CommRing R'] [Algebra R R'] (hp : (p : R) = 0) :
    Function.Bijective (liftSemi (G.toBase R').omega) := by
  have hp' : (p : R') = 0 := by rw [← map_natCast (algebraMap R R'), hp, map_zero]
  have hL := G.omegaLevel_one_bijective hp
  have hL' := (G.baseChange R').omegaLevel_one_bijective hp'
  have hg := liftSemi_toBaseChange_cot_bijective R R' (G.A 1)
  let e : R' ⊗[R] G.omega ≃ₗ[R'] R' ⊗[R] Cot R (G.A 1) :=
    LinearEquiv.baseChange R R' _ _ (LinearEquiv.ofBijective (G.omegaLevel 1) hL)
  have hcomp : ((G.baseChange R').omegaLevel 1).comp (liftSemi (G.toBase R').omega) =
      (liftSemi (toBaseChange R R' (G.A 1)).cot).comp e.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, liftSemi_tmul, map_smul, e,
      LinearEquiv.baseChange_tmul, LinearEquiv.ofBijective_apply]
    rfl
  refine Function.Bijective.of_comp_left ?_ hL'.injective
  change Function.Bijective (((G.baseChange R').omegaLevel 1).comp (liftSemi (G.toBase R').omega))
  rw [hcomp]
  exact hg.comp e.bijective

end PDivGroup

end GlobalTheory
