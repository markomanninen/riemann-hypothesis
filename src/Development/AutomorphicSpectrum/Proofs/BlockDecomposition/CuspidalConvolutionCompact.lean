module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactOperatorOfScaledIsometricIntertwiner
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactOperatorRepOpRcuspZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalL2NormOneIsometryStatement

@[expose] public section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.CuspidalCompact

theorem isCompactOperator_repOp_Rcusp (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E a → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) :
    IsCompactOperator (repOp (Rcusp μ) μ f) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact GlobalTheory.CompanionTheory.CuspRank.isCompactOperator_repOp_Rcusp_zero E μ f
  · let ν : Measure (GroundTheory.Automorphic.Reduction.normOneGL (K := E) (n := a)) := Measure.haar
    have : ν.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
    have htransfer := GlobalTheory.T.cuspidal_L2_norm_one_isometry E a ha μ ν
    obtain ⟨Φ, c, hc0, hΦ, hint⟩ := htransfer
    obtain ⟨f₁, hf₁⟩ := hint f hf hc
    exact GlobalTheory.CompanionTheory.CompactOperators.isCompactOperator_of_scaled_isometric_intertwiner (repOp (Rcusp μ) μ f) _ Φ c hc0 hΦ hf₁
      (GroundTheory.Automorphic.CuspidalSpectrum.isCompactOperator_cuspRep (K := E) (n := a) ν f₁)

end GlobalTheory.CompanionTheory.CuspidalCompact
