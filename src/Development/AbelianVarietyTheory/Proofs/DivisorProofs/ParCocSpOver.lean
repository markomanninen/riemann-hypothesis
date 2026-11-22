module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem parCoc_spOver (R : Type) [CommRing R] (A B : Over (Sp R)) (J : Type) [Fintype J]
    (a : J → Fn1 A) (b : J → Fn1 B) (n : Fn1 (A ⊗ B)) (ha : ∀ i, IsCoc (whole A) (a i))
    (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (x : Pt A D) :
    parCoc (D := D') a b n (spOver φ ≫ x) =
      ((parCoc (D := D) a b n x).pull (spOver φ ▷ B)).add
        (sumMul (D := D') (fun i ↦ a i D D' φ x) b) := by
  funext E _ _ E' _ _ ψ z
  simp only [parCoc, Fn1.pull, Fn1.add, sumMul]
  have h1 : z ≫ (spOver φ ≫ x) ▷ B = (z ≫ spOver φ ▷ B) ≫ x ▷ B := by
    rw [comp_whiskerRight, Category.assoc]
  have h2 : (z ≫ spOver φ ▷ B) ≫ snd _ _ = z ≫ snd _ _ := by
    rw [Category.assoc, whiskerRight_snd]
  have h3 : ptAlg ((z ≫ spOver φ ▷ B) ≫ fst _ _) =
      (ptAlg (z ≫ fst (SpAlg R D') B)).comp φ := by
    rw [Category.assoc, whiskerRight_fst, ← Category.assoc]
    conv_lhs => rw [← spOver_ptAlg (z ≫ fst (SpAlg R D') B)]
    rw [spOver_comp, ptAlg_spOver]
  rw [h1, h2, h3]
  have hc : ∀ i, a i D E ((ptAlg (z ≫ fst _ _)).comp φ) x =
      ptAlg (z ≫ fst _ _) (a i D D' φ x) + a i D' E (ptAlg (z ≫ fst _ _)) (spOver φ ≫ x) :=
    fun i ↦ ha i D D' E φ _ x (sm_whole x)
  simp only [hc, map_add (f := _), add_mul, Finset.sum_add_distrib]
  ring

end GlobalTheory.PtExt
