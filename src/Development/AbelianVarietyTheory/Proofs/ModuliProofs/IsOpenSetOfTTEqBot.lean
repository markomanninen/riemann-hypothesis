module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
open Classical

namespace GlobalTheory

theorem isOpen_setOf_TT_eq_bot : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (M : GlobalTheory.ZH.RatModel o Ω) (I : Type) (d : I → Ω) (e : ℕ), M.HasDiv S.th → (∀ z : M.Z, ∀ x₀ ∈ S.supI M z, (S.TT M z = ⊥ ↔ ∃ k, d k ≠ 0 ∧ S.th x₀ ^ e / d k ∈ M.O z)) → IsOpen {z : M.Z | S.TT M z = ⊥} := by
  intro o Ω _ _ _ S M I d e hdiv h
  haveI : NeZero (S.r * S.N) :=
    ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  refine isOpen_iff_forall_mem_open.2 fun z hz => ?_
  obtain ⟨x₀, hx₀⟩ := hdiv z
  obtain ⟨k, hk, hreg⟩ := (h z x₀ hx₀).1 hz
  refine ⟨{w | M.Div S.th x₀ w} ∩ {w | S.th x₀ ^ e / d k ∈ M.O w}, ?_,
    (M.isOpen_setOf_div S.th x₀).inter (M.isOpen_setOf_mem_O _), hx₀, hreg⟩
  rintro w ⟨hw1, hw2⟩
  exact (h w x₀ hw1).2 ⟨k, hk, hw2⟩

end GlobalTheory
