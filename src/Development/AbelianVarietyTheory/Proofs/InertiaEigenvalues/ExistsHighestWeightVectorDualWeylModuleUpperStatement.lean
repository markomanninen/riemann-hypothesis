module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHighestWeightVectorDualWeylModuleUpper
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolynomialRepGLComplexAlgebraicWeightEvalPointStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroupStatement

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_highest_weight_vector_dualWeylModule_upper : ∀ (n : ℕ) (lam : DomWeight n), ∃ v : nablaSq ℂ n lam, v ≠ 0 ∧ ∀ B : GL (Fin n) ℂ, (B : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id → GlobalTheory.Branching.sqRep ℂ n lam B v = (∏ i, ((B : Matrix (Fin n) (Fin n) ℂ) i i) ^ (lam.w i)) • v := by
  first | exact @GlobalTheory.HwUpper.exists_hw_upper | exact GlobalTheory.HwUpper.exists_hw_upper | (intros; apply GlobalTheory.HwUpper.exists_hw_upper <;> assumption)
