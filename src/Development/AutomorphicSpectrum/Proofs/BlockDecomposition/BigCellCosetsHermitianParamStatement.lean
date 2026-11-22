module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellCosetsHermitianParam
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
theorem _root_.GlobalTheory.T.big_cell_cosets_hermitian_param : ∀ {D : D7} {n : ℕ} {w : G D n}, mat w = blk4 0 1 (-1) 0 → ∀ {nb : hermA D n → G D n}, IsNMap nb → ∃ e : ratHerm D n → Cosets (P D n) (GF D n), Function.Injective e ∧ (∀ q, cosetCell q = ⊥ ↔ q ∈ Set.range e) ∧ ∀ f : G D n → ℂ, LeftInv (P D n ⊓ GF D n) f → ∀ (l : ratHerm D n) (y : G D n), term (P D n) (GF D n) f y (e l) = f (w * nb l.1 * y) := by
  first | exact @GlobalTheory.CompanionTheory.SwUnf.BigCell.bigCell | exact GlobalTheory.CompanionTheory.SwUnf.BigCell.bigCell | (intros; apply GlobalTheory.CompanionTheory.SwUnf.BigCell.bigCell <;> assumption)
