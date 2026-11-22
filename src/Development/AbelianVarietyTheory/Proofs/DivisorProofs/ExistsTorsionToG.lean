module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaMovesTameRootStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactor
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinFlatEtSplitTorus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionToG
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassifiedTorusTorsionPointEqUniformisationTorus
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniversalTorsionPairPolAV
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionToG
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePartImageGeneric
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOfIsPullF
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralClosureFiniteLocalOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePairIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePartOfIsFinitePart
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoPolarisedAbelianSchemesDvrOfFieldExtens
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsToricTorsionSectionsUniformisation

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.ToricTorsionSecUnif

section FinitePart

open GlobalTheory.TorusModel GlobalTheory.TorsionFormCompare GlobalTheory.KernelNoTorsion

theorem exists_torsion_toG (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R]
    (hR : AdmBase R (maximalIdeal R)) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ (N : Over (Sp R)) (g₀ : GtPt D.toPre N) (x₀ : N ⟶ G), IsFinite N.hom ∧ Flat N.hom ∧ GtTors k g₀ ∧
      (∀ (T : Over (Sp R)) (g : GtPt D.toPre T), GtTors k g → ∃! h : T ⟶ N, GtPt.IsPull h.left g₀ g) ∧
      x₀ ^ k = 1 ∧ FormalEq U.toUnifPre x₀ g₀ := by
  obtain ⟨_, -, -, hc⟩ := hR
  have hL := abelianSchemeLaws_all.1
  obtain ⟨Gt, _, _, hH⟩ := exists_isGt hL.globalFns (splitExt D.toPre)
  obtain ⟨Φ, hΦ⟩ := exists_points hL.globalFns hH
  have hΦ : Represents Φ := hΦ
  have hfin : IsFinite (torsion Gt k).hom ∧ Flat (torsion Gt k).hom := by
    obtain ⟨h₁, h₂, -⟩ := hL.mulN _ D.toPre.P k hk
    have h₁' : IsFinite (𝟙 D.toPre.P.A ^ k).left := h₁
    have h₂' : Flat (𝟙 D.toPre.P.A ^ k).left := h₂
    rw [← MulEtaleDvr.mulN_eq_pow] at h₁' h₂'
    have Q := MulEtaleDvr.isPullback_torsion D.toPre.P.A k
    exact isFinite_flat_torsion_of_isGt _ (splitExt D.toPre) Gt hH k hk
      (MorphismProperty.of_isPullback (P := @IsFinite) Q h₁') (MorphismProperty.of_isPullback (P := @Flat) Q h₂')
  obtain ⟨hf, hl⟩ := hfin
  obtain ⟨J, hJ⟩ := exists_mulEquiv U.toUnifPre hL.globalFns hΦ
  have hN := isAdicColimit_of_isFinite hc (torsion Gt k)
  refine ⟨torsion Gt k, Φ _ (torsion.ι Gt k), J _ hN (torsion.ι Gt k), hf, hl,
    (tors_iff hΦ k _).2 (torsionι_pow Gt k), fun T g hg => ?_, ?_,
    (formalEq_iff _ _ _).2 ((hJ _ hN _ _).1 rfl)⟩
  · obtain ⟨x, rfl⟩ := (Φ T).surjective g
    have hx := (tors_iff hΦ k x).1 hg
    refine ⟨torsionLift x hx, (isPull_iff_comp hΦ _ _ _).2 (torsionLift_ι _ _), fun h hh => torsion_hom_ext ?_⟩
    rw [torsionLift_ι]
    exact (isPull_iff_comp hΦ _ _ _).1 hh
  · rw [← map_pow, torsionι_pow, map_one]

open GlobalTheory.FinitePartGeneric ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ConstLin GlobalTheory.FormalPoint

end FinitePart

section TorusPoint

end TorusPoint

section Main

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj
open Classical

open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator ReciprocityTheory.ChartRestriction.G.DVR

end Main

end GlobalTheory.ToricTorsionSecUnif
