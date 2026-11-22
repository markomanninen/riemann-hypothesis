module

public import Mathlib
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
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SecondStep

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_cusp_multiplicity_input_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw) (In : RatIn D S) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (M : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (Q : D.what₂.places.Pl → Finset (PlE D.host)), MtInput D M tup Q → (∀ v, NG.OverPl (Pq v) v) → GalEx D → RowCusp D A.row → GlobalTheory.RowTie.ChebSplit D.nd → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → ∃ c0 : Big D, ∀ (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T), (∀ (l : ℕ) [Fact l.Prime] j, (c0 l j).1 ≤ (b0 l j).1) → In.Sb ⊆ Sx → (∀ P P', P ∈ Sx → IsConjPl D.host P P' → P' ∈ Sx) → (∀ p ∈ low, placesOver D.host.E p ⊆ ↑Sx) → ∃ (F : TwF T) (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw A.bare F (TwL.empty T))) (h0 : _), (∀ i j b, (ex.Bsup i j b).FG ∧ Submodule.span (FractionRing ((T.ntw A.bare F (TwL.empty T)).O i)) (ex.Bsup i j b : Set (ex.Fm i j b)) = ⊤) ∧ ∀ th, Nonempty (SideB (⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).toD7 ((⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).cf cf) ((⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).row A.row) low Pq ((⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).rat S) In.hL In.eig In.θ) := by
  first | exact @_root_.GlobalTheory.HeightCounting.FormsStep.second_step_alt | exact _root_.GlobalTheory.HeightCounting.FormsStep.second_step_alt | (intros; apply _root_.GlobalTheory.HeightCounting.FormsStep.second_step_alt <;> assumption)
end
