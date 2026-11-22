module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealInvariantSesquilinearFormEqSmulInner
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_invariant_sesquilinear_form_eq_smul_inner : ∀ (D : D7) (V : HSp D) (c : CoefA V), c.Is → ∀ (B : c.W →ₗ⋆[ℂ] c.W →ₗ[ℂ] ℂ), (∀ u ∈ GinfC V, ∀ x y, B (c.ρ u x) (c.ρ u y) = B x y) → ∃ z : ℂ, ∀ x y, B x y = z * ⟪x, y⟫_ℂ := by
  first | exact @GlobalTheory.CoefRealSchur.form_eq_smul_inner | exact GlobalTheory.CoefRealSchur.form_eq_smul_inner | (intros; apply GlobalTheory.CoefRealSchur.form_eq_smul_inner <;> assumption)
