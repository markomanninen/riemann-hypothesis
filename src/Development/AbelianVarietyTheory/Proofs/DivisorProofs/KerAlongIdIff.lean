module

public import Mathlib
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

noncomputable section
namespace GlobalTheory.PrincSubring

def powLB {S : Scheme.{0}} (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) : LB (Out.powObj A 8).left :=
  LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (Out.powPr A uv.1) (Out.powPr A uv.2)).left)
    fun uv => GlobalTheory.W8 uv.1 uv.2

def KerAlong {S : Scheme.{0}} (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) {S' : Scheme.{0}} (g : S' ⟶ S) : Prop :=
  ∀ (T : Over S) (a : T.left ⟶ S'), a ≫ g = T.hom → ∀ x : T ⟶ A, IsTrivial (slice A P x) → x = 1

end GlobalTheory.PrincSubring
