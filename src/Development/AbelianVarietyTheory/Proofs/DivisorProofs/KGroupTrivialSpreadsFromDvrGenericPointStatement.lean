module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KGroupTrivialSpreadsFromDvrGenericPoint
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
theorem _root_.GlobalTheory.T.kGroup_trivial_spreads_from_dvr_generic_point : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left), IsAbelianScheme G → L.IsLB → Out.RelAmple G L → Out.Rigidified G L → Out.Sym G L → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (g : Sp V ⟶ S), GlobalTheory.KTrivSpread.TrivAlong G L (spMap (algebraMap V (FractionRing V)) ≫ g) → GlobalTheory.KTrivSpread.TrivAlong G L g := by
  first | exact @GlobalTheory.KTrivDvrSpread.trivAlong_of_generic | exact GlobalTheory.KTrivDvrSpread.trivAlong_of_generic | (intros; apply GlobalTheory.KTrivDvrSpread.trivAlong_of_generic <;> assumption)
