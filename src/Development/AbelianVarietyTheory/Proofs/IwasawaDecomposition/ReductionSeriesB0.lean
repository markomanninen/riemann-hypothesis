module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterGridData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsToricCharactersInTwistCoefficientRingsStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisRepFamilyBounded
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAlgWeightFWeightTensorDualRepOfEmbeddingsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightTensorDualRepDualHighestWeightAtEmbeddingStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightTensorRepOfEmbeddingsIsIrreducibleStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContragredientIsIrreducibleFiniteDimensionalStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIrreducibleBaseChangeWeightTensorDualRepOfEmbeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HighestWeightDoubleDualCoefficientSpaceUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmTypeEmbeddingAtSideDistinctNonconjugateStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharZeroFractionRingCoefficientRingStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftWeightParamEqInfinitesimalCharacterOfHalfIntStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedLatticeFinitelyGeneratedSpanningStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCentralGroupAlgebraIdempotentUniversalStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeStableRationalLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSignatureDataSpan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeBasisFreeModulePlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeComparisonUnitAtFrobeniusEqDeltaStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistLiftFormsEqBaseChangeRationalDatumFormsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistIndexOfCoefficientFieldPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericUnipotentCharacterAtSideEqThetaSideStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalCharacterAdmissibleConductorInertiaSurjStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTameBlockCharacterTypePlaceNotOverLStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverRealSubfieldSplit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistRingsCharactersClassGroupsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBasisCoordLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNatCastNotMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormLeOneOfMemClC
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideDataOverSetLevels
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConductorPrimesInLowSetStatement

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

noncomputable section
namespace GlobalTheory.HeightCounting.Up.PointwiseSettings
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

theorem exists_Sx (D : D7) : ∃ Sx : Finset (PlE D.host), (∀ p ∈ lowAll D, placesOver D.host.E p ⊆ ↑Sx) ∧
    OverSet D Sx (lowAll D) ∧ (∀ P P', P ∈ Sx → IsConjPl D.host P P' → P' ∈ Sx) := by
  have hne : ∀ p ∈ lowAll D, p ≠ 0 := by
    intro p hp
    simp only [lowAll, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hp | rfl | rfl | rfl | rfl
    · exact lowPr_ne_zero D p hp
    · exact (D.host.g_prime 0).ne_zero
    · exact (D.host.g_prime 1).ne_zero
    · exact D.host.pde_prime.ne_zero
    · exact D.host.pde'_prime.ne_zero
  have hfin : (⋃ p ∈ (lowAll D : Set ℕ), placesOver D.host.E p).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun p hp => Formalism.L2.TwC.placesOver_finite' D.host.E p (hne p hp)
  refine ⟨hfin.toFinset, fun p hp Q hQ => ?_, fun Q hQ => ?_, fun Q Q' hQ hc => ?_⟩
  · rw [Set.Finite.coe_toFinset]
    exact Set.mem_biUnion (Finset.mem_coe.2 hp) hQ
  · obtain ⟨p, hp, hQp⟩ := Set.mem_iUnion₂.1 ((Set.Finite.mem_toFinset hfin).1 hQ)
    exact ⟨p, hp, hQp⟩
  · obtain ⟨p, hp, hQp⟩ := Set.mem_iUnion₂.1 ((Set.Finite.mem_toFinset hfin).1 hQ)
    exact (Set.Finite.mem_toFinset hfin).2 (Set.mem_biUnion hp (placesOver_conj D p hQp hc))


end GlobalTheory.HeightCounting.Up.PointwiseSettings
