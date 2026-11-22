module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzOneParameterGroupFormula
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSymplecticLieEqExpOneParamStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticTransfer
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionUnitaryCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchActOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanWeilOperatorsLinearOneMulStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanWeilOperatorIntertwinesSchroedingerStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanCoordinateActionLinearMulStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanCoordinateActionSymplecticStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousOneParameterUnitaryCoordinateActionStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousOneParameterArchimedeanWeilOperatorStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchWeilOperatorUnitaryWLintegralNormEqStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
open scoped Classical

namespace GlobalTheory.Twist.SmoothLine

theorem finprod_add_of_at {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) (x z : κ → AF F) (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evI F) z) :
    (∏ᶠ v, φ v fun i => evFin F v ((x + z) i)) = ∏ᶠ v, φ v fun i => evFin F v (x i) := by
  refine finprod_congr fun v => ?_
  have hv : (fun i => evFin F v ((x + z) i)) = fun i => evFin F v (x i) := by
    funext i
    rw [Pi.add_apply, map_add (f := _), GlobalTheory.ThK.EvUniqInf.evFin_eq_zero_of_at z hz v i, add_zero]
  rw [hv]

end GlobalTheory.Twist.SmoothLine
