module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.siegelPullback_id_comp_cancel : ∀ (h k : ℕ) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (ζ : B) (ζ' : B') (ζ'' : B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (c : SiegPre h k ζ s) (c' : SiegPre h k ζ' s') (c'' : SiegPre h k ζ'' s'') (f : S' ⟶ S) (f' : S'' ⟶ S'), SiegPB c c (𝟙 _) ∧ (SiegPB c' c f → (SiegPB c'' c' f' ↔ SiegPB c'' c (f' ≫ f))) := by
  first | exact @GlobalTheory.SiegelPullComp.id_comp_cancel | exact GlobalTheory.SiegelPullComp.id_comp_cancel | (intros; apply GlobalTheory.SiegelPullComp.id_comp_cancel <;> assumption)
