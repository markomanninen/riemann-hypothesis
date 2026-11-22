module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KGroupTrivialDescendsFlatSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAlongIdIff

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kGroup_trivial_descends_flat_surjective : ∀ {S S' S'' : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (g : S' ⟶ S) (f : S'' ⟶ S') [Flat f] [Surjective f], L.IsLB → GlobalTheory.KTrivSpread.TrivAlong G L (f ≫ g) → GlobalTheory.KTrivSpread.TrivAlong G L g := by
  first | exact @GlobalTheory.KTrivFlatDescent.trivAlong_of_flat_surjective | exact GlobalTheory.KTrivFlatDescent.trivAlong_of_flat_surjective | (intros; apply GlobalTheory.KTrivFlatDescent.trivAlong_of_flat_surjective <;> assumption)
