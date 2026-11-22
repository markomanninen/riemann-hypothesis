module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantUnipotentTranslate
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_sum_invariant_unipotent_translate : ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω,
  PositivityTheory.GramSchwartzFunctions.HidaSetting D n V ψ χ θ μ ω →
  ∀ (g : G D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat g = blk4 1 (b.map (incA D)) 0 1 →
  ∀ Φ : schwartzA θ V.rank n,
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  intro D n V ψ χ θ μ ω hS g b hg Φ
  obtain ⟨-, -, hψ, -, -, -, -, hW⟩ := hS
  refine tsum_congr fun ξ => ?_
  have hmul : (b.map (incA D) * inner V (ξ.map (incA D)) (ξ.map (incA D)) : Mx D n n) =
      (b * (ξᴴ * (V.gram * ξ))).map (incA D) := by
    change rat b * (adj (rat ξ) * (gA V * rat ξ)) = rat (b * (ξᴴ * (V.gram * ξ)))
    rw [rat_mul, rat_mul, rat_mul, rat_conjTranspose, gA]
  have htrace (M : Matrix (Fin n) (Fin n) D.host.E) :
      Matrix.trace (M.map (incA D)) = incA D (Matrix.trace M) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
  rw [hW.unip g (b.map (incA D)) hg Φ (ξ.map (incA D)), hmul, htrace,
    GlobalTheory.CompanionTheory.ThetaInv.halfTr_incA, hψ.2.2.1, one_mul]
