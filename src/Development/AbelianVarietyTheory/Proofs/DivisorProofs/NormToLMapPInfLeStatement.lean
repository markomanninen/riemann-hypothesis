module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormToLMapPInfLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
public import GroundTheory.AutomorphicForms.ReductionSiegel

@[expose] public section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_toL_map_pInf_le' : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ c : ℝ, 0 ≤ c ∧
    ∀ M : Matrix (Fin a) (Fin a) (Ad E),
      ‖toL (M.map (pInf E))‖ ≤ c * ‖GroundTheory.Automorphic.CuspidalSpectrum.archMat E a M‖ := by
  first | exact @GlobalTheory.GLCuspNorm.norm_toL_map_pInf_le | exact GlobalTheory.GLCuspNorm.norm_toL_map_pInf_le | (intros; apply GlobalTheory.GLCuspNorm.norm_toL_map_pInf_le <;> assumption)
