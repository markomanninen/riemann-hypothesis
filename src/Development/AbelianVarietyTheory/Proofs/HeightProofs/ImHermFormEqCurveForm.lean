module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.CurveFormSign
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsHomFamilyBaseChange
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRing
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilEqIffHermFormEqComplex
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOfCmTriplePullback
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPatOfObj
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AbelianSchemeSurjectiveOfOntoComplexPoints
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniversalTorsionPairPolAV
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LbIsoPowOfHermFormPullEq
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenOfIsLocallyNoetherian
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearLiftOfIsMonHomPolAV
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.PrimeSpectrumDualEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.CurveFormSign

namespace GlobalTheory.CMPointCompare

section Dictionary

variable {S X Y : Scheme.{0}} {C : Over S} {G : Over X} {B G' : Over Y} [GrpObj C] [GrpObj G] [GrpObj B] [GrpObj G']
  {f : Y ⟶ S} {x : Y ⟶ X} {β : B.left ⟶ C.left} {π : G'.left ⟶ G.left}

variable (hβ : IsGrpPullback B C f β) (hπ : IsGrpPullback G' G x π)

end Dictionary

section Intertwine

variable {S X Y : Scheme.{0}} {C : Over S} {G : Over X} [GrpObj C] [GrpObj G] {f : Y ⟶ S} {x : Y ⟶ X}
  {Φ : MapOver C G f x}

end Intertwine

section General

open GlobalTheory.CM

theorem hom_ext_of_complexPoints {R : Type} [CommRing R] (σ : R →+* ℂ) (hσ : Function.Injective σ)
    {B G : Over (Sp R)} [Smooth B.hom] [IsSeparated G.hom] {a b : B ⟶ G}
    (h : ∀ p : Over.mk (spMap σ) ⟶ B, p ≫ a = p ≫ b) : a = b := by
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom σ) hσ
  refine ExtUnique.over_hom_ext_of_isPullback (IsPullback.of_hasPullback B.hom (spMap σ)) ?_
  have : IsReduced (pullback B.hom (spMap σ)) :=
    isReduced_of_smooth_complex _ (pullback.snd B.hom (spMap σ)) inferInstance
  refine ComplexPoints.hom_ext_of_points (pullback.snd B.hom (spMap σ)) G.hom (by simp) fun x hx => ?_
  have e := congrArg (fun z => z.left) (h (Over.homMk (x ≫ pullback.fst _ _) (by
    show (x ≫ _) ≫ _ = spMap σ
    rw [Category.assoc, pullback.condition, reassoc_of% hx])))
  exact (Category.assoc _ _ _).symm.trans (e.trans (Category.assoc _ _ _))

end General

section Linear

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

variable {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)

end Linear

end GlobalTheory.CMPointCompare
