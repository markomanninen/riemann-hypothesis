module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankConvergesColumnStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunOfMemCusp
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunTransportS
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AuxiliaryPrimeLtFirstTypePrimeOfSizes
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasColOfChoice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorOPerm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SizesOfSizeRows
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftAutomorphicOfConvergent

@[expose] public section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
namespace GlobalTheory.RowTest
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem twist_linear_independence_test (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hL : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal) : GlobalTheory.RowClaim.LinK := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc a u => ?_⟩⟩
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.T.twisted_theta_lift_automorphic hP hL large₂ hS ch hch CF hsc a u
  exact ⟨h1, GlobalTheory.T.besselPeriodCorank_converges_column ch.W ch.M hch.vol ch.ξ _ (col_mem ch a) _ h2⟩
end GlobalTheory.RowTest
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_characters_linearly_independent : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.LinK := by
  first | exact @_root_.GlobalTheory.RowTest.twist_linear_independence_test | exact _root_.GlobalTheory.RowTest.twist_linear_independence_test | (intros; apply _root_.GlobalTheory.RowTest.twist_linear_independence_test <;> assumption)
end
