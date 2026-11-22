module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveHodgeToPdivisibleOmegaSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_hodge_to_pdivisible_omega_surjective :
    GlobalTheory.Published.AbelianHodgeDeRham →
    ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K], (p : K) = 0 →
    ∀ (A : Over (Sp K)) [GrpObj A] (g : ℕ),
      IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
      ∀ (G : PDivGroup p K) (t : PDivGroup.TorsionTower G A)
        (ψ : PrimitiveSubmodule A →ₗ[K] G.omega),
        (∀ c : PrimitiveSubmodule A, GlobalTheory.PtExt.IsCan t c.1 (G.rigOfOmega (ψ c))) →
        Function.Surjective ψ :=
  @GlobalTheory.PtExt.surjective_of_isCan_field
