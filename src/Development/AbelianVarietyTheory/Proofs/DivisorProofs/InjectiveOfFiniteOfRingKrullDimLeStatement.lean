module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfFiniteOfRingKrullDimLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionEtaleCompletionToCompleteLocal

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_of_finite_of_ringKrullDim_le' : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R] (b : A →+* R), b.Finite → ringKrullDim A ≤ ringKrullDim R → Function.Injective b := by
  first | exact @GlobalTheory.FiniteMapInj.injective_of_finite_of_ringKrullDim_le | exact GlobalTheory.FiniteMapInj.injective_of_finite_of_ringKrullDim_le | (intros; apply GlobalTheory.FiniteMapInj.injective_of_finite_of_ringKrullDim_le <;> assumption)
