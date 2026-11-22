module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormDerivCharacterSymplecticPairingRealLine
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharAnnihilatorOpenSubgroupFinPartCompact
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAnnihilatorOpenSubgroupInBox
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffRapidDecayRealFunctional
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergVacuumCommutantPreservesLatticeVacua
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_deriv_character_symplecticPairing_realLine : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (w : WO S T), ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ = 2 * Real.pi * |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ z (compAt θ τ w)| := by
  first | exact @GlobalTheory.LatSum.norm_deriv_psi_symplO_lineAt | exact GlobalTheory.LatSum.norm_deriv_psi_symplO_lineAt | (intros; apply GlobalTheory.LatSum.norm_deriv_psi_symplO_lineAt <;> assumption)
