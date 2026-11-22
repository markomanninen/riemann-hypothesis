module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenousPDivGroupFinrankOmegaDual
public import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual :
    ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p)
      (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H),
      IsIsog q → Function.Injective (T.map q) ∧
        Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ≠ ⊤ ∧
        Module.finrank k G.omega = Module.finrank k H.omega ∧
        Module.finrank k G.dual.omega = Module.finrank k H.dual.omega :=
  @GlobalTheory.Dieu.isog_finrank_omega
