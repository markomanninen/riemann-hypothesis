module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDominantDiagonalConjugationContracts
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

@[expose] public section

open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_dominant_diagonal_conjugation_contracts : GlobalTheory.SatakeWeyl.Contract := by
  first | exact @GlobalTheory.SatakeWeyl.ContractProof.contract | exact GlobalTheory.SatakeWeyl.ContractProof.contract | (intros; apply GlobalTheory.SatakeWeyl.ContractProof.contract <;> assumption)
