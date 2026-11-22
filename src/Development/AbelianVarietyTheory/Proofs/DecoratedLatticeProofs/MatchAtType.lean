module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdentityCosetEntryProportionalColumnDatumStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiDatumAgreeColumnDatumAtTypePrimeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepDatumCompletionEqColumnTestFunctionStatement

@[expose] public section

namespace GlobalTheory.SymBridge

theorem matchAtType : MatchAtType := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s S _ _ ν hν h
  exact ⟨GlobalTheory.T.identityCoset_entry_proportional_columnDatum X Pr R Ch sel S₀ mu cst σ₀ P k ι s S ν hν h,
    GlobalTheory.T.psiDatum_agree_columnDatum_at_typePrime X Pr R Ch sel S₀ mu cst σ₀ P k ι s S ν hν h,
    GlobalTheory.T.stepDatum_completion_eq_columnTestFunction X Pr R Ch sel S₀ mu cst σ₀ P k ι s S ν hν h⟩

end GlobalTheory.SymBridge
