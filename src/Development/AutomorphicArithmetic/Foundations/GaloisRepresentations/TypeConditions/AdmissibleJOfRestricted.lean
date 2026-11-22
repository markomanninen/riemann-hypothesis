module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.DistinctAbsIrredConstituents
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.RhoBar
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
public import ReciprocityTheory.Hypotheses.GalCoh
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenPeriodOfLocalGlobal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.H1H2LocalDualityStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepBaseChange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepUniqueBaseChange
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2PairOfAdmissible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleDictionaryOfParams
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateJumpsReadingRowAdmStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDescent
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrrDistinctConstituentsAfterExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowFiveOneOfCoefRingTakenAtLiveLocalisationsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowFiveOneTypePrimeOfCoefRingTakenAtLiveStatement

@[expose] public section

noncomputable section

namespace UpperTheory.GalS

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory GlobalTheory.StringRepresentationDecomposition UpperTheory.GalC

theorem g2g' {D : D7} (h : DeRhamJumpsDistinctCondition D) : ∀ i r, GoodR D.nd i r → (D.nd.l i = D.host.g 0 ∨ D.nd.l i = D.host.g 1) →
    ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ x, D.naut.IsdRW i (AdmissibleParameterJ.rQ D i r x) w ∧
      ∀ τ₀, InducesW D.nd i τ₀ w → D.naut.jumpsW i (AdmissibleParameterJ.rQ D i r x) τ₀ = D.naut.locAutHodgeTateWeightsLevelZero i τ₀ := h.1

theorem jc_of_u {D : D7} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))} (hr : GoodR D.nd i r)
    (hS : GlobalTheory.SplitCoef.OSplit D) (h : DistinctAbsIrredConstituents D.nd i r) : AbsIrreducibleDistinct D i r := by
  obtain ⟨K', hK', hA, _, hK⟩ := h
  exact GlobalTheory.T.absIrr_distinct_constituents_after_extension D i r (hS i) hr K' (algebraMap (Kf D.nd i) K') (fun x => (hK x).2)

end UpperTheory.GalS
