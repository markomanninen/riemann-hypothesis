module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulSecK
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StalkMapInjectiveOfFlat
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulAFiniteFlatSurjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftFrobenius

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mulFam_exists_ne_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (m : ℕ), Odd m → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)), MulFam m F₁ G → (∃ α j, (F₁.f α).f j ≠ 0) → ∃ α j, (G.f α).f j ≠ 0 := by
  intro R _ _ _ _ D m hm F₁ G hG ⟨α, j, hj⟩
  by_contra hcon
  push_neg at hcon
  apply hj
  have hfinite : IsFinite (mulA D.toPre.P.A m).left := GlobalTheory.MulFinite.isFinite_mulA
    (GlobalTheory.MulPull.mulPull_of_cube_of_symm GlobalTheory.AbLaw.CubeAssembly.cube_gen
      (GlobalTheory.exists_gen_negLB GlobalTheory.laws_without_cohomology.1)).1 GlobalTheory.laws_without_cohomology.2.2.1
      GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ D.toPre.P m hm.pos
  have hc := D.toPre.P.isAb.comm
  have hsm := D.toPre.P.isAb.smooth
  have hmhom := GlobalTheory.AbLaw.MulN.isMonHom_mulA D.toPre.P.A m
  have hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ _),
      Flat ((Over.pullback t).map (mulA D.toPre.P.A m)).left ∧
        Surjective ((Over.pullback t).map (mulA D.toPre.P.A m)).left := fun K _ _ t =>
    GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
      GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
      (TLinPf.isAb_pullback t D.toPre.P.A D.toPre.P.isAb) _ inferInstance
      (MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) hfinite)
  have h₂ : Flat (mulA D.toPre.P.A m).left :=
    GlobalTheory.flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres _ _ _ _ inferInstance inferInstance
      inferInstance hfinite fun K _ _ t => (hgeo K t).1
  have h₃ : Surjective (mulA D.toPre.P.A m).left :=
    GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t => (hgeo K t).2
  obtain ⟨u, -, -, e⟩ := hG.1 α
  refine GlobalTheory.PullLin.sec_eq_zero_of_flat D.toPre.P.isLB (F₁.f α) (mulA D.toPre.P.A m).left (fun x J hJ => ?_) j
  have e₁ := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 e _ (𝟙 _) x J hJ
  rw [ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftFrobenius.sval_zero _ (hcon _), Category.id_comp] at e₁
  exact (Units.mul_left_eq_zero _).1 e₁.symm

end GlobalTheory.Mum
