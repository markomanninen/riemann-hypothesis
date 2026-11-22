module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueSectionOfNaturalPointwiseFunction
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

theorem GlobalTheory.T.exists_unique_section_of_natural_pointwise_function
    (R : Type) [CommRing R] (Y : Over (Sp R)) (U : Y.left.Opens) (t : Fn0 Y)
    (ht : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : E →ₐ[R] E') (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U → t E' (spOver ψ ≫ z) = ψ (t E z)) :
    ∃! a : Γ(Y.left, U), ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E),
      ⊤ ≤ z.left ⁻¹ᵁ U → evU (D := E) z.left U a = t E z :=
  GlobalTheory.PtExt.NatSec.exists_unique_section R Y U t ht
