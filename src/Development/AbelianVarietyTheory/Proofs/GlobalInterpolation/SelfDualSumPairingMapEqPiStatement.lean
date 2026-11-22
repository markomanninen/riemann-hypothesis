module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualSumPairingMapEqPi
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.DualExponentDensity
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ActionCoordinates
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDensityEuler
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeTensorUnfolding

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_sumPairing_map_eq_pi : ∀ (T V W : Type) [Fintype T] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup W] [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] (e : W ≃ₜ+ (T → V)) (ε : ℝ) (β : V → V → ℝ) (μ₀ : Measure V), μ₀.IsAddHaarMeasure → ActionCoordinates.IsSelfDualFor ε β μ₀ → ∀ (μ : Measure W) (χ : W → W → ℂ), (∀ x y, χ x y = Complex.exp (2 * Real.pi * Complex.I * ((ε * ∑ ρ, β (e x ρ) (e y ρ) : ℝ) : ℂ))) → SelfDual μ χ → μ.map e = Measure.pi fun _ : T => μ₀ := by
  first | exact @GlobalTheory.SelfDualProduct.map_eq_pi | exact GlobalTheory.SelfDualProduct.map_eq_pi | (intros; apply GlobalTheory.SelfDualProduct.map_eq_pi <;> assumption)
