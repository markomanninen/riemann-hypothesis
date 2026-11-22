module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalConjUnipotentRadicalIsotropic
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair

@[expose] public section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_conj_unipotentRadical_isotropic : ∀ (I : AutInst), ∀ γ ∈ I.GFset, ∀ W, I.IsIsot W → ∃ W', I.IsIsot W' ∧ ∀ m ∈ I.NA W', γ⁻¹ * m * γ ∈ I.NA W := by
  first | exact @GlobalTheory.CuspGeo.naconj | exact GlobalTheory.CuspGeo.naconj | (intros; apply GlobalTheory.CuspGeo.naconj <;> assumption)
