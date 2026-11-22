module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalRestrictMemCuspidalL2
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousResQ
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicGLNormOneSplitStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureNormOneProductStatement

@[expose] public section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.CompanionTheory.CuspTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_restrict_mem_cuspidal_l2 : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (normOneGL (K := E) (n := a))) [ν.IsHaarMeasure] (φ : GA E a → ℂ), φ ∈ cuspCont E a → ∀ h : MemLp (resQ φ) 2 (RightCosetSpace.quotientMeasure (rationalGLOne (K := E) (n := a)) ν), h.toLp (resQ φ) ∈ cuspidalL2 ν := by
  first | exact @GlobalTheory.CompanionTheory.CuspTransfer.toLp_restrict_mem_cuspidalL2 | exact GlobalTheory.CompanionTheory.CuspTransfer.toLp_restrict_mem_cuspidalL2 | (intros; apply GlobalTheory.CompanionTheory.CuspTransfer.toLp_restrict_mem_cuspidalL2 <;> assumption)
