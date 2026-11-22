module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusIsOpenOfOpenImmersionCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesOfAmpFrames

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianLocus_isOpen_of_openImmersion_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, AbOpen (u i).G) → AbOpen t.G := by
  first | exact @GlobalTheory.AbLocusLocal.abOpen_of_cover | exact GlobalTheory.AbLocusLocal.abOpen_of_cover | (intros; apply GlobalTheory.AbLocusLocal.abOpen_of_cover <;> assumption)
