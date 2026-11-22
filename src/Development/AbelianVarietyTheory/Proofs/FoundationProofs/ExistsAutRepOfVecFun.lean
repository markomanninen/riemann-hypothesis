module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAutFormUCoef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeLeOfColW
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphicRepDualPairing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenericDetPowMulHw
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBilinearFischerPairingMatrixEntryPolynomia
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualWeylModuleTensorCoefficientUniversal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroupStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqBotOrTopOfTensor
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SpanRangeEqTopOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualWeylModuleTensorCoefficientUniversalStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryArchimedean

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AutRec

theorem continuous_coord_emb {E : Type} [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ) :
    Continuous (coord (E := E) τ) := by
  unfold coord
  split_ifs
  · exact continuous_apply _
  · exact Complex.continuous_conj.comp (continuous_apply _)

theorem continuous_cEmb_emb {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (τ : E →+* ℂ) :
    Continuous (cEmb (E := E) (n := n) τ) :=
  (Continuous.units_map _ (continuous_id.matrix_map (continuous_coord_emb τ))).comp GlobalTheory.DefU.continuous_cInf

end GlobalTheory.AutRec

end
