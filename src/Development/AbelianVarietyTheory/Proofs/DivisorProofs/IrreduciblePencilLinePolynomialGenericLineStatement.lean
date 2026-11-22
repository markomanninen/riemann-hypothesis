module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreduciblePencilLinePolynomialGenericLine
public import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
public import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapLine

@[expose] public section

open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_pencilLinePolynomial_generic_line : ∀ (F : Type) [Field F] (D N : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F), Irreducible f → Irreducible (GlobalTheory.PencilDisc.line (fun i j => (MvPolynomial.X (Sum.inl (i, j)) : MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F)) (fun j => MvPolynomial.X (Sum.inr (Sum.inl j))) (fun j => MvPolynomial.X (Sum.inr (Sum.inr j))) f) := by
  first | exact @GlobalTheory.PencilDisc.irreducible_line_generic | exact GlobalTheory.PencilDisc.irreducible_line_generic | (intros; apply GlobalTheory.PencilDisc.irreducible_line_generic <;> assumption)
