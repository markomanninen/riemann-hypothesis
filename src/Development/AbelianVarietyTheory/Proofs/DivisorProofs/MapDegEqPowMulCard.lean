module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSqZeroNaturality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqZeroPointEqOfCotangentFormEqStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveCotangentGlobalSectionsGroupScheStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCotangentFrameSmoothGroupSchemeStatement
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyTorusExtensionOfIsGt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisible
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapDegreeEqExpCharPowMulCardKernel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPullbackPow
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankSecPullSandwich
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFlatTorsion

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.ZV GlobalTheory.DegKer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiAbelianTower

theorem finrank_eq_of_mapDeg {X Y : Scheme.{0}} [IsIntegral Y] (φ : X ⟶ Y) [IsFinite φ] [Flat φ] {D : ℕ}
    (hD : MapDeg φ D) (y : Y) : φ.finrank y = D := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  replace hU : IsAffineOpen U := hU
  haveI : Nonempty U := ⟨⟨_, hy⟩⟩
  letI := (φ.app U).hom.toAlgebra
  haveI : Module.Finite Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := φ.finite_app U hU
  haveI : Module.Flat Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := by
    have := φ.flat_appLE hU (hU.preimage φ) le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at this
  have hp : IsPullback (hU.preimage φ).fromSpec (Spec.map (φ.app U)) φ hU.fromSpec :=
    (IsOpenImmersion.isPullback _ _ _ _ (by
      rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec φ hU (hU.preimage φ)])
      (by simp)).flip
  obtain ⟨q, rfl⟩ : y ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hy
  rw [← hD.finrank_eq U hU ⟨_, hy⟩, ← FiniteCover.rankAtStalk_bot,
    Module.rankAtStalk_eq_of_le_of_finite_of_flat _ (p := ⊥) (q := q) bot_le,
    ← Scheme.Hom.finrank_of_isPullback _ _ _ _ hp q]
  exact Scheme.Hom.finrank_SpecMap_algebraMap Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) _

end GlobalTheory.SemiAbelianTower
