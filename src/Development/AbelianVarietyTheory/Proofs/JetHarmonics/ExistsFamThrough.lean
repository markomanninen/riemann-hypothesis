module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCSt
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsLeastOfDiscrete
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsRepresentativesModNsmul
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfEq
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FamEqOnClassOfEq
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LinOfSval
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsBoxFamilyMultilinearMapStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsBoxFamilyPowerDegree

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.UnitBallBox

section Fam

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

variable {j : ℕ} {D D' : DegPre R} (pD : IsPowDeg D' D j)

theorem box_secScal {S : Fam D' F k} {s : Fin j → Fam D F k} (hS : IsBoxFam pD F k S s)
    {f' : ∀ α : D'.X, D'.SecB k α} {f : Fin j → ∀ α : D.X, D.SecB k α} (hf : IsBoxFamB pD k f' f) (α' : D'.X)
    (h : ∀ i, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F (pD.xe α' i)) (DegPre.famε k) ((s i).s (pD.xe α' i))
      (D.famφB (pD.xe α' i)) (DegPre.famε k) (f i (pD.xe α' i)) (DegPre.prB D F).left 1) :
    GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' F α') (DegPre.famε k) (S.s α')
      (D'.famφB α') (DegPre.famε k) (f' α') (DegPre.prB D' F).left 1 := by
  obtain ⟨hφ, H⟩ := hS α'
  obtain ⟨hψ, H'⟩ := hf α'
  have e₄ : ∀ i, (DegPre.prB D' F).left ≫ (pD.pw.pr i).left =
      prB pD F i ≫ (DegPre.prB D F).left := fun i => by
    rw [← Over.comp_left, ← Over.comp_left]; congr 1; exact (whiskerLeft_snd _ _).symm
  exact BoxFamScalar.secScal_box D.P.isLB D'.P.isLB pD.w (GC.famφ_eq D' F α') e₄
    (S.s α') (fun i => (s i).s (pD.xe α' i)) (f' α') (fun i => f i (pD.xe α' i))
    (fun y _ _ hJ hJ' => BoxFamScalar.box_sval pD.w hφ (S.s α') (fun i => (s i).s (pD.xe α' i)) _ H (𝟙 _) y hJ hJ')
    (fun y _ _ hJ hJ' => BoxFamScalar.box_sval pD.w hψ (f' α') (fun i => f i (pD.xe α' i)) _ H' _ y hJ hJ')
    (fun _ => 1) 1 (fun y => by simp only [NuBox.gs_one, Finset.prod_const_one]) h

end Fam


end GlobalTheory.UnitBallBox
