module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem sh_mul_nzx {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (y : Mx D ρ p)
    (z : hermA D ρ) (x : Mx D ρ p) :
    M.sh y * M.nzx z x = M.nzx (z + GlobalTheory.CompanionTheory.FJE.jc y x) x * M.sh y := by
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  rw [GlobalTheory.CompanionTheory.PcB.mat_mul', GlobalTheory.CompanionTheory.PcB.mat_mul',
    M.nzx_mat, M.nzx_mat, M.sh_mat]
  simp only [blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]
  simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]
  congr 2
  simp only [jc]
  congr 2
  rw [Matrix.mul_neg]
  change z.1 + y * adj x = (z.1 + (y * adj x + x * adj y)) + -(x * adj y)
  abel

end GlobalTheory.CompanionTheory.FJE
