module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitCentreDerivativeCommuteCentralEigen
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableAutomorphicSpace
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.SquareIntegrableSegment
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitCentreDerivative_commute_central_eigen : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ), (∀ o : Op E N, zc E N * act o = act o * zc E N) ∧ zc E N ∈ Zalg E N ∧ ∀ (φ : Sm E N) (c : ℂ), zc E N φ = c • φ ↔ ∀ (t : ℝ) (g : GA E N), φ.1 (splitCentre E N t * g) = Complex.exp (c * t) * φ.1 g := by
  exact GlobalTheory.ResW.zc_comm_mem_eigen
