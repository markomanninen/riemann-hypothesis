module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
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

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.PtExt.fv_linear (R : Type) [CommRing R] (X : Over (Sp R)) :
    (∀ (f f' : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))), fv (f + f') = (fv f).add (fv f')) ∧
    (∀ (r : R) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _)))
      (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
      (φ : D →ₐ[R] D') (x : Pt X D),
      fv (r • f) D D' φ x = algebraMap R D' r * fv f D D' φ x) ∧
    (∀ g : C0 (O (dp0 R) (X.hom ≫ 𝟙 _)),
      ∃ k : Fn0 X, IsCob (whole X) (fv ⟨d0 _ g, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g⟩) k) := by
  refine ⟨fun f f' ↦ rfl, ?_, fun g ↦ ⟨fun D _ _ x ↦ g (trivAt x), ?_⟩⟩
  · intro r f D _ _ D' _ _ φ x
    exact Algebra.smul_def r (ev f (trivMap φ x))
  · intro D _ _ D' _ _ φ x _
    rfl

alias GlobalTheory.T.crystallineCocycleOnTrivialThickenings_additive_linear := GlobalTheory.PtExt.fv_linear
