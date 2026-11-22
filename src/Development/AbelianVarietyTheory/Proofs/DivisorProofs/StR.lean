module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagBlockNormContInvStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoUnitaryOffDiagNormSqZeroIffMemMaxCompactStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPseudoUnitaryOffDiagNormSublevelStatement

@[expose] public section

namespace GlobalTheory.PsCo.Pc3

theorem stR : StR := by
  intro n ε
  obtain ⟨hcont, hinv⟩ := GlobalTheory.T.offDiagBlockNorm_mul_invariant n ε
  exact ⟨hcont, hinv, GlobalTheory.T.pseudoUnitary_offDiag_norm_sq_zero_iff_mem_maxCompact n ε, GlobalTheory.T.isCompact_pseudoUnitary_offDiag_norm_sublevel n ε⟩

end GlobalTheory.PsCo.Pc3
