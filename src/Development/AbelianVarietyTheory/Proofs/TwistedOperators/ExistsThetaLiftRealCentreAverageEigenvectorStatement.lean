module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftRealCentreAverageEigenvector
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalListedTopForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinCoefMultT
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaLift_realCentre_average_eigenvector : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → S.SigOK → S.IsDefinite → ∀ (ν : Measure (GA D S)) (fd : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) fd ν → ∀ (χ φ : GA D S → ℂ), GlobalTheory.SeeSaw.HasCen S χ φ → GlobalTheory.Unf.IsContAut S φ → ∀ Φ, IsThetaFunO ψ S T Φ → (∀ h, IntegrableOn (fun g => thetaKO om g h Φ * φ g) fd ν) → ∃ Φ', IsThetaFunO ψ S T Φ' ∧ (∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → om (z, 1) Φ' = (χ z)⁻¹ • Φ') ∧ ∀ h, ∫ g in fd, thetaKO om g h Φ * φ g ∂ν = ∫ g in fd, thetaKO om g h Φ' * φ g ∂ν := by
  first | exact @GlobalTheory.CenAvgOne.exists_central_average_one | exact GlobalTheory.CenAvgOne.exists_central_average_one | (intros; apply GlobalTheory.CenAvgOne.exists_central_average_one <;> assumption)
