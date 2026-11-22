module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurePreservingPolarGaussianProbabilityComplex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFirstCoords
public import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
public import ReciprocityTheory.SemistableReduction.SJCoreA

@[expose] public section

open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurePreserving_polar_gaussianProbabilityComplexSpace : ∀ (n : ℕ), 0 < n → MeasurePreserving (fun p : UnitSphereC n × Ioi (0:ℝ) => (p.2 : ℝ) • (p.1 : EuclideanSpace ℂ (Fin n))) ((sphereProb n).prod (radProb n)) (gaussProb n) := by
  first | exact @GlobalTheory.SphereMeanDrop.measurePreserving_polar_gaussProb | exact GlobalTheory.SphereMeanDrop.measurePreserving_polar_gaussProb | (intros; apply GlobalTheory.SphereMeanDrop.measurePreserving_polar_gaussProb <;> assumption)
