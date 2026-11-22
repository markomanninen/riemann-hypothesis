module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableAlt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.YonedaAddNaturalityLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TlLevSurjKer

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et.CovChar

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

variable {R} {X Y : Scheme.{0}} (f : Y ⟶ X)

end GlobalTheory.Et.CovChar

namespace GlobalTheory.AV.AbVar

open ReciprocityTheory.ChartRestriction.G.Geo.Tor MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

variable {K : Type} [Field K]

abbrev geomX (A : AbVar K) : Scheme.{0} := GlobalTheory.Et.geom (AlgebraicClosure K) A.X.hom

abbrev geomOver (A : AbVar K) : Over (Sp K) :=
  Over.mk (pullback.fst A.X.hom (spMap (algebraMap K (AlgebraicClosure K))) ≫ A.X.hom)

def transl (A : AbVar K) (a : A.Pt) : geomX A ⟶ geomX A :=
  pullback.lift
    ((lift (Over.homMk (pullback.fst _ _) : geomOver A ⟶ A.X)
      (Over.homMk (pullback.snd _ _ ≫ a.left) (by
        rw [Category.assoc, Over.w a]; exact pullback.condition.symm) : geomOver A ⟶ A.X) ≫ μ[A.X]).left)
    (pullback.snd _ _) (by
      rw [Over.w]; exact pullback.condition)

end GlobalTheory.AV.AbVar
