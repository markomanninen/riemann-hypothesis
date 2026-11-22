module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CechAcyclicityOverAffineBase
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
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlatBoundedAcyclicBaseChangeStatement

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_cover_cechLB_fibre_acyclic : ∀ {k : Type} [Field k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) [IsSeparated a] [Flat a] (G : LB Z) (hG : G.IsLB)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0})
    (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)) (Hy : IsPullback π f q t)
    {κ : Type} [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens) (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤)
    (hac : (cechLB f (G.pull π) D).Acyclic)
    (s : Sp k ⟶ Spec (CommRingCat.of R)) (σ : X ⟶ Z) (hs : s ≫ t ≫ b = 𝟙 _) (h₁ : σ ≫ p = 𝟙 X)
    (h₂ : σ ≫ q = a ≫ s ≫ t), ∃ D' : κ → X.Opens, (∀ i, IsAffineOpen (D' i)) ∧ ⨆ i, D' i = ⊤ ∧ (cechLB a (G.pull σ) D').Acyclic := by
  first | exact @GlobalTheory.CompanionTheory.PointSurjFibre.cech_fibre_acyclic | exact GlobalTheory.CompanionTheory.PointSurjFibre.cech_fibre_acyclic | (intros; apply GlobalTheory.CompanionTheory.PointSurjFibre.cech_fibre_acyclic <;> assumption)
