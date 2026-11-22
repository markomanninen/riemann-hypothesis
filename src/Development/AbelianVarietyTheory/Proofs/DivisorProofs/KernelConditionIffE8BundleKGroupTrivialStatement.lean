module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConditionIffE8BundleKGroupTrivial
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
theorem _root_.GlobalTheory.T.kernel_condition_iff_e8Bundle_kGroup_trivial : ∀ {S : Scheme.{0}} (h : ℕ) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (A ⊗ A).left), IsSymmetricPair h A P → Out.RelAmple A (diagPull A P) → ∀ {S' : Scheme.{0}} (g : S' ⟶ S), KerAlong A P g ↔ GlobalTheory.KTrivSpread.TrivAlong (Out.powObj A 8) (powLB A P) g := by
  first | exact @GlobalTheory.PrincSubring.kerAlong_iff_trivAlong | exact GlobalTheory.PrincSubring.kerAlong_iff_trivAlong | (intros; apply GlobalTheory.PrincSubring.kerAlong_iff_trivAlong <;> assumption)
