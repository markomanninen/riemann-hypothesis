module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarSubgroupBiInvariant
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Formalism.RealPlaceAnalysis.FinalF

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_subgroup_bi_invariant : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → (∀ m ∈ NW ε W, ν.map (fun x => x * m) = ν) ∧ ν.map (fun x => x⁻¹) = ν := by
  first | exact @GlobalTheory.UnipUnimod.unimodular_NW | exact GlobalTheory.UnipUnimod.unimodular_NW | (intros; apply GlobalTheory.UnipUnimod.unimodular_NW <;> assumption)
