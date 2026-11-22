module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameBaseHolds

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht
open MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.Cht.FlagBase

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem comp_listProd {B : Scheme.{0}} {G : Over B} [GrpObj G] {X Y : Over B} (e : X ⟶ Y) (L : List (Y ⟶ G)) :
    e ≫ L.prod = (L.map (e ≫ ·)).prod := by
  induction L with
  | nil => exact MonObj.comp_one e
  | cons a L ih => rw [List.prod_cons, MonObj.comp_mul, ih, List.map_cons, List.prod_cons]

theorem isCombAtG_bc {X : Scheme.{0}} (t : SAB H X) {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S')
    {x : Sp S ⟶ X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {a : Fin m → S}
    {w : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x v a w) :
    IsCombAtG t (spMap ψ ≫ x) (fun j => spMap (dualMap ψ) ≫ v j) (fun j => ψ (a j)) (spMap (dualMap ψ) ≫ w) := by
  obtain ⟨u, hu, hw⟩ := h
  have he : spMap (dualMap ψ) ≫ (tEpsG x).hom = (tEpsG (spMap ψ ≫ x)).hom := by
    show spMap (dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap ψ ≫ x
    rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    congr 2
    apply RingHom.ext
    intro r
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let e : tEpsG (spMap ψ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap ψ)) he
  refine ⟨fun i => e ≫ u i, fun i => ?_, ?_⟩
  · show spMap (dualMap ψ) ≫ (u i).left = spMap (epsMul (ψ (a i))) ≫ spMap (dualMap ψ) ≫ v i
    rw [hu i, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    congr 2
    apply RingHom.ext
    intro r
    ext <;> simp [dualMap, epsMul, _root_.mul_comm]
  · have hl : (List.ofFn fun i => e ≫ u i) = (List.ofFn u).map (e ≫ ·) := by
      rw [List.map_ofFn]
      rfl
    rw [hl, ← comp_listProd, Over.comp_left, hw]
    rfl

end GlobalTheory.LocM.Cht.FlagBase
