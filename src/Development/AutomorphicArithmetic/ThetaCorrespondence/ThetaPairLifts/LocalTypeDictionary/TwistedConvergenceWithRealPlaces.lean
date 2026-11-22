module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankConvergesColumnStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunOfMemCusp
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunTransportS
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AuxiliaryPrimeLtFirstTypePrimeOfSizes
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasColOfChoice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorOPerm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SizesOfSizeRows
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedBaseChangeLiftExists

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem GlobalTheory.RowTest.twisted_convergence_with_real_places (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hL : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal) :
    GlobalTheory.RowClaim.Big (fun ch => ∀ ρ ξ a u, GlobalTheory.RowTest.ConvK (ch.withReal ρ ξ) a u) := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc ρ ξ a u => ?_⟩⟩
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.T.twisted_base_change_lift_exists hP hL large₂ hS (ch.withReal ρ ξ) (hch.toIsBase.withReal ρ ξ) CF hsc a u
  exact ⟨h1, GlobalTheory.T.besselPeriodCorank_converges_column ch.W ch.M hch.vol ξ _ (col_mem ch a) _ h2⟩
end
