module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVROfFiniteEtaleBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedCubicalRootPolarisationEtaleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackPasteFactorisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSharpGen
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completeDVR_of_finite_etale_baseChange : ∀ (A R V : Type) [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V] (ρ : A →+* R) (ψ : A →+* V), IsLocalHom ρ → ρ.Finite → ρ.Etale → IsCN V → IsDiscreteValuationRing V → IsLocalHom ψ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (κ : R →+* V'), IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp ρ = f.comp ψ := by
  first | exact @GlobalTheory.HenselLift.exists_dvr_of_finite_etale | exact GlobalTheory.HenselLift.exists_dvr_of_finite_etale | (intros; apply GlobalTheory.HenselLift.exists_dvr_of_finite_etale <;> assumption)
