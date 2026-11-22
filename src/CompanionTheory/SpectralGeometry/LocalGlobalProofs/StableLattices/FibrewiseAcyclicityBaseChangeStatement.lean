module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibrewiseAcyclicityBaseChange
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineOpenBiInfOfLe
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyFiniteOfAffineCover
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulHomologyEqZeroOfAcyclicFibre
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SubsingletonOfPoints
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechFiniteVanishesOffOrigin
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechCohomologyFinrank
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfAmpleOnClosedSubschemeLocalBase
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibAc

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibrewise_acyclicity_base_change : ∀ {k : Type} [Field k] [IsAlgClosed k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) (ha : IsProjBy a) [IsSeparated a] [Flat a] (G : LB Z) (hG : G.IsLB)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) [LocallyOfFiniteType (t ≫ b)] (Y : Scheme.{0})
    (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)) (Hy : IsPullback π f q t)
    (hfib : ∀ (s : Sp k ⟶ Spec (CommRingCat.of R)) (σ : X ⟶ Z), s ≫ t ≫ b = 𝟙 _ → σ ≫ p = 𝟙 X →
      σ ≫ q = a ≫ s ≫ t → FibAc a (G.pull σ)), FibAc f (G.pull π) := by
  first | exact @GlobalTheory.CompanionTheory.PointSurjectivity.fibAc_of_closed_fibres | exact GlobalTheory.CompanionTheory.PointSurjectivity.fibAc_of_closed_fibres | (intros; apply GlobalTheory.CompanionTheory.PointSurjectivity.fibAc_of_closed_fibres <;> assumption)
