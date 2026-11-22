module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentVecC
public import Formalism.LocalToGlobal.ProjectiveLattices.FrCovA

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieLocFrame

section Alg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj
open GlobalTheory.LieMet (tanOf isTan_tv isTan_map tan_ext)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {S T U : Type} [CommRing S] [CommRing T] [CommRing U] {x : Sp S ⟶ X} {x' : Sp T ⟶ X} {x'' : Sp U ⟶ X}

def res (ψ : S →+* T) (hx : spMap ψ ≫ x = x') (v : TanM x t.G) : TanM x' t.G := tanOf (isTan_map ψ hx (isTan_tv v))

theorem res_res (ψ : S →+* T) (hx : spMap ψ ≫ x = x') (χ : T →+* U) (hx' : spMap χ ≫ x' = x'') {ω : S →+* U}
    (e : χ.comp ψ = ω) (hx'' : spMap ω ≫ x = x'') (v : TanM x t.G) :
    res χ hx' (res ψ hx v) = res ω hx'' v := by
  subst e
  refine tan_ext ?_
  show spMap (Formalism.L2.Pj.dualMap χ) ≫ spMap (Formalism.L2.Pj.dualMap ψ) ≫ _ = spMap (Formalism.L2.Pj.dualMap (χ.comp ψ)) ≫ _
  rw [← Category.assoc, spMap_comp_spMap]
  congr 2
  exact RingHom.ext fun a => by ext <;> simp [Formalism.L2.Pj.dualMap]

theorem res_sum (ψ : S →+* T) (hx : spMap ψ ≫ x = x') {κ : Type} [Fintype κ] (a : κ → S) (n : κ → TanM x t.G) :
    res ψ hx (∑ k, a k • n k) = ∑ k, ψ (a k) • res ψ hx (n k) := by
  subst hx
  have dual_alg : (Formalism.L2.Pj.dualMap ψ).comp (algebraMap S (DualNumber S)) =
      (algebraMap T (DualNumber T)).comp ψ := by
    refine RingHom.ext fun z => ?_
    ext <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have eps_dual (b : S) : spMap (Formalism.L2.Pj.dualMap ψ) ≫ spMap (epsMul b) =
      spMap (epsMul (ψ b)) ≫ spMap (Formalism.L2.Pj.dualMap ψ) := by
    rw [spMap_comp_spMap, spMap_comp_spMap]
    congr 1
    refine RingHom.ext fun z => ?_
    ext <;> simp [Formalism.L2.Pj.dualMap, epsMul, mul_comm]
  let ρ : overAt (spMap ψ ≫ x) (DualNumber T) ⟶ overAt x (DualNumber S) := Over.homMk (spMap (Formalism.L2.Pj.dualMap ψ)) (by
    show spMap _ ≫ spMap _ ≫ x = spMap _ ≫ spMap _ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, dual_alg])
  let f : TanM x t.G →+ TanM (spMap ψ ≫ x) t.G :=
    AddMonoidHom.mk' (res ψ rfl) fun a b => by
      apply tan_ext
      have h := congrArg (fun f => f.left) (MonObj.comp_mul ρ (tv a) (tv b))
      rw [tv_add]
      exact h
  refine (map_sum f _ _).trans (Finset.sum_congr rfl fun k _ => tan_ext ?_)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (tv (n k)).left) (eps_dual (a k))).trans
    (Category.assoc _ _ _))


end Alg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts GlobalTheory.TrueCx
open GlobalTheory.AllWt (Psi)
attribute [local instance] Over.cartesianMonoidalCategory

end GlobalTheory.LieLocFrame
