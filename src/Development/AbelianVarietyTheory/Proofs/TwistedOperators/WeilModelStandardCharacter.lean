module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanPointPureTensorKeepsFiniteFactorStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelCmExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClmThetaSumRhoPure

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

noncomputable section
open scoped Classical
namespace GlobalTheory.ThetaLineDer

theorem schwartz_diffQuotient_eval_mul_eq_slope {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F] (s : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (y : κ → mixedEmbedding.mixedSpace F) (R : ℂ) (t : ℝ) :
    (t⁻¹ • (s t - s 0)) y * R = slope (fun t => s t y * R) 0 t := by
  simp only [slope_def_module, sub_zero, SchwartzMap.smul_apply, SchwartzMap.sub_apply, smul_mul_assoc, sub_mul]

theorem rho_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) {m : ℕ}
    (Φ : Fin m → (Fin n × Fin d → AF F) → ℂ) (hΦ : ∀ i, Φ i ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d)) :
    GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (∑ i, Φ i)) = ∑ i, GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (Φ i)) := by
  have hsum : M.co.rho ψ u (∑ i, Φ i) = ∑ i, M.co.rho ψ u (Φ i) := by
    funext x
    simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Finset.sum_apply, Finset.mul_sum]
  have hmem : ∀ i, M.co.rho ψ u (Φ i) ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    fun i => GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ u (Φ i) (hΦ i)
  rw [hsum]
  have key := map_sum (GlobalTheory.WeilM.thetaLin F (Fin n × Fin d))
    (fun i => (⟨M.co.rho ψ u (Φ i), hmem i⟩ : GlobalTheory.WeilM.schA F (Fin n × Fin d))) Finset.univ
  simpa only [GlobalTheory.WeilM.thetaLin_apply, Submodule.coe_sum] using key

end GlobalTheory.ThetaLineDer
