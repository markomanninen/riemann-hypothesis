module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
public import GroundTheory.GlobalFields.Adele.BaseChange
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
public import GroundTheory.GlobalFields.TateThesis.IdeleMeasureNormOne
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

open scoped GroundTheory.Global.AdeleBaseChange NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.IdeleLogHom

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange

section Transfer

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def toE : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ →* IdeleGroup E :=
  Units.map (adeleTensorAlgEquivLeft F E : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →ₐ[AF F] AdeleRing (𝓞 E) E).toMonoidHom

theorem absE_eq_ideleModule (x : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) :
    (absE F E x : ℝ) = (IdeleGroup.ideleModule E (toE F E x) : ℝ) := by
  rw [← GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := F), ← GlobalTheory.ModuAdele.modu_norm_eq_absE]
  have h2 : ∀ u : (AF F)ˣ, (((adeleClass F).modu u : ℝ≥0) : ℝ) = (IdeleGroup.ideleModule F u : ℝ) := fun u => by
    change (distribHaarChar (AdeleRing (𝓞 F) F) u : ℝ) = _
    exact GlobalTheory.ModuAdele.distribHaarChar_adeleRing F u
  have h3 : Units.map (Algebra.norm (AF F) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →* AF F) x = ideleNorm F E (toE F E x) := by
    ext
    simp [toE, ideleNorm, Algebra.norm_eq_of_algEquiv]
  rw [h2, h3]

end Transfer

section OnE

variable {E : Type} [Field E] [NumberField E]

end OnE

end GlobalTheory.IdeleLogHom
