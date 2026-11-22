module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientExistsListedKernelsSmoothBase
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeQuotient_exists_listed_kernels_smooth_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o : Ob D l s) (σ : Fin n → (𝟙_ (Over S) ⟶ o.t.G)) (K : Set o.t.G.left), 1 ≤ D.p + D.q → admitted l 𝔓 p → Smooth s → Lists (p ^ 2) σ K → HeckeSet D o.t 𝔓 p i K → HasQuot o p K := by
  first | exact @GlobalTheory.hasQuot_of_lists_of_smooth | exact GlobalTheory.hasQuot_of_lists_of_smooth | (intros; apply GlobalTheory.hasQuot_of_lists_of_smooth <;> assumption)
