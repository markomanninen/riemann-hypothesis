module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConvergenceOfSiegelSet
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

@[expose] public section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
namespace GlobalTheory.WeilConv
theorem twisted_weil_representation_convergence : GlobalTheory.Published.SiegelSetUnitary → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.SquareSt.WeilConvergence :=
  fun hRT _ => weilConvergence_of_siegelSet hRT
end GlobalTheory.WeilConv
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_theta_integral_converges : GlobalTheory.Published.SiegelSetUnitary → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.SquareSt.WeilConvergence := by
  first | exact @_root_.GlobalTheory.WeilConv.twisted_weil_representation_convergence | exact _root_.GlobalTheory.WeilConv.twisted_weil_representation_convergence | (intros; apply _root_.GlobalTheory.WeilConv.twisted_weil_representation_convergence <;> assumption)
end
