module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegPreDataDescendsFg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedCommGroupSchemeArtinFibreProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftedPolarisationKernelKilledOfUnit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpecMapFieldCancel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPotentialBlockDecomposition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifyingMapSymplecticLevelEquivariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeTjCorrespondenceTargetFiniteEtal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionKilledByIdealCharZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdemKernel
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtLevZero

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.ESOrdM

theorem stalk_normal_of_smooth (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f] (x : X) :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  refine GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth f (fun y => ?_) x
  have : y.asIdeal.IsPrime := PrimeSpectrum.isPrime y
  let _ : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk y) := StructureSheaf.stalkAlgebra R y
  have h : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R y
  have hle : y.asIdeal.primeCompl ≤ nonZeroDivisors R := y.asIdeal.primeCompl_le_nonZeroDivisors
  have hd : IsDomain ((Spec (CommRingCat.of R)).presheaf.stalk y) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  exact ⟨hd, isIntegrallyClosed_of_isLocalization _ _ hle⟩

end GlobalTheory.ESOrdM
