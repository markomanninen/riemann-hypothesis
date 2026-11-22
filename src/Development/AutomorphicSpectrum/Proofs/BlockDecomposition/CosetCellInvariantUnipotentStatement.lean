module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCellInvariantUnipotent
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCell
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummableCell
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCellsDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinRationalPoints
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHalfTr

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_cell_invariant_unipotent : ∀ {D : D7} {n : ℕ} (q : Cosets (P D n) (GF D n)) (γ : GF D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat (γ : G D n) = blk4 1 (b.map (incA D)) 0 1 → cosetCell (rmulEquiv (P D n) (GF D n) γ q) = cosetCell q := by
  first | exact @GlobalTheory.CompanionTheory.SwUnf.cosetCell_rmulEquiv | exact GlobalTheory.CompanionTheory.SwUnf.cosetCell_rmulEquiv | (intros; apply GlobalTheory.CompanionTheory.SwUnf.cosetCell_rmulEquiv <;> assumption)
