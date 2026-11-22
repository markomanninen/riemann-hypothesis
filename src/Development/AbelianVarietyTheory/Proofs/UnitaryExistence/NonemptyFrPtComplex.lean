module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ModuliExistsNumberFieldPointStatement
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
public import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
public import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
public import Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem nonempty_frPt_complex : N1c → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ σ : c.F →+* ℂ, Nonempty (FrPt Xo c (CAt σ)) := by
  intro hN hT E _ _ _ H Dw l Xo c h σ
  classical
  obtain ⟨L, _, _, j, x, hx⟩ := GlobalTheory.T.xoNumPt_of_p_add_q_pos hN E H Dw l Xo c h
  let _ : Algebra c.F L := j.toAlgebra
  let _ : Algebra c.F ℂ := σ.toAlgebra
  have : Algebra.IsAlgebraic c.F L := by
    have : IsScalarTower ℚ c.F L := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    exact Algebra.IsAlgebraic.tower_top (K := ℚ) c.F
  let φ : L →ₐ[c.F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let _ : Algebra L ℂ := φ.toRingHom.toAlgebra
  obtain ⟨_, y, _⟩ := gfp_frPt_gen (Xo := Xo) (c := c) (L := L) (L' := ℂ) hT
    (fun r => (φ.commutes r).symm) x hx (fun τ i j => if i = j then 1 else 0)
    (fun τ i => by simp) (fun τ i j hij => by simp [hij.ne'])
  exact ⟨y⟩

end GlobalTheory
