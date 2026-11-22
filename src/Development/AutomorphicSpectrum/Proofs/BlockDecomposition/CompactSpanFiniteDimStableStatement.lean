module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSpanFiniteDimStable
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmMemArchSmooth
public import Development.AutomorphicSpectrum.Proofs.HermitianForms.CasOfCapelliVec
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOpCommLiB

@[expose] public section

set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_span_finite_dim_stable : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a)
    (Z : (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra),
    Matrix.conjTranspose (AutomorphicForm.mat (Z : AutomorphicForm.ArchMatrix E a)) =
      -AutomorphicForm.mat (Z : AutomorphicForm.ArchMatrix E a) →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) →
    ∀ ψ ∈ Submodule.span ℂ (Set.range fun k => cptRep E a k φ),
      GlobalTheory.CompanionTheory.HCRep.liB Z ψ ∈ Submodule.span ℂ (Set.range fun k => cptRep E a k φ) := by
  first | exact @GlobalTheory.CompanionTheory.HCRep.liB_skew_mem_span | exact GlobalTheory.CompanionTheory.HCRep.liB_skew_mem_span | (intros; apply GlobalTheory.CompanionTheory.HCRep.liB_skew_mem_span <;> assumption)
