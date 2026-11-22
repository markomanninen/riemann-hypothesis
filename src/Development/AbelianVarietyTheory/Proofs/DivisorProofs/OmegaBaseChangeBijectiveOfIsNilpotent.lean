module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeBijectiveOfPEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaLevelBijectiveOfPowEqZero

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PDivGroup

theorem omega_baseChange_bijective_of_isNilpotent : ∀ (p : ℕ) [Fact p.Prime] (R R' : Type) [CommRing R]
    [CommRing R'] [Algebra R R'], IsNilpotent (p : R) → ∀ G : PDivGroup p R,
    Function.Bijective (PDiv.liftSemi (G.toBase R').omega) := by
  intro p _ R R' _ _ _ hnil G
  obtain ⟨N, hN⟩ := hnil
  have hN' : (p : R') ^ N = 0 := by
    rw [← map_natCast (algebraMap R R'), ← map_pow, hN, map_zero]
  have hL := omegaLevel_bijective_of_pow_eq_zero p R N hN G N le_rfl
  have hL' := omegaLevel_bijective_of_pow_eq_zero p R' N hN' (G.baseChange R') N le_rfl
  have hg := PDiv.liftSemi_toBaseChange_cot_bijective R R' (G.A N)
  let e : R' ⊗[R] G.omega ≃ₗ[R'] R' ⊗[R] Cot R (G.A N) :=
    LinearEquiv.baseChange R R' _ _ (LinearEquiv.ofBijective (G.omegaLevel N) hL)
  have hcomp : ((G.baseChange R').omegaLevel N).comp (PDiv.liftSemi (G.toBase R').omega) =
      (PDiv.liftSemi (toBaseChange R R' (G.A N)).cot).comp e.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, PDiv.liftSemi_tmul, map_smul, e,
      LinearEquiv.baseChange_tmul, LinearEquiv.ofBijective_apply]
    rfl
  refine Function.Bijective.of_comp_left ?_ hL'.injective
  change Function.Bijective (((G.baseChange R').omegaLevel N).comp (PDiv.liftSemi (G.toBase R').omega))
  rw [hcomp]
  exact hg.comp e.bijective

end GlobalTheory.PDivGroup
