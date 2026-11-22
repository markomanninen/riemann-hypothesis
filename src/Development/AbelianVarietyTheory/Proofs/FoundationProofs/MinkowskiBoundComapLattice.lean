module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.SlopeE
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.HarderNarasimhan.QuotRealize
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPairingGramMatrixValuesAndDefinite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthogonalSumCoefficientLatticeIsLatticeAndDual
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualLatticeIsLatticeAndHermitianDual
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NablaDeltaOperatorLatticePreserved
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedWeylLatticeHermitianDuality
public import Formalism.LocalToGlobal.Columns.CoefModB

@[expose] public section

open NumberField
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.TestLat.Compare

section Space

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end Space

section Sum

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι C : Type} [Fintype ι] {n N : ℕ}

end Sum

section DualSpace

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} {n : ℕ}

end DualSpace

section Nabla

variable {K : Type} [Field K] [NumberField K] {ι C : Type} [Fintype ι] {n N : ℕ}


omit [NumberField K] in
theorem pairK_basis [StarRing K] (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (i j : VVIdx lam) :
    pairK lam (fun τ => (g τ : Matrix (Fin n) (Fin n) K)) (bVV K lam i) (bVV K lam j) =
      pairBK lam (bVV K lam i) (rhoK lam g (bVV K lam j)) := by
  rw [pairK_apply, pairP_eq_pairB, pairBK_apply, rhoK_coe]
  congr 2
  rw [bVV_coe]
  obtain ⟨Q, hQ⟩ := bVVfun_int K lam i
  rw [hQ, MvPolynomial.map_map]
  congr 2
  exact RingHom.ext_int _ _

def gramB (K : Type) [Field K] (lam : ι → DomWeight n) : Matrix (VVIdx lam) (VVIdx lam) K :=
  Matrix.of fun i j => pairBK lam (bVV K lam i) (bVV K lam j)

omit [NumberField K] in
theorem gramB_transpose (lam : ι → DomWeight n) : (gramB K lam)ᵀ = gramB K lam := by
  ext i j
  simp only [gramB, Matrix.transpose_apply, Matrix.of_apply, pairBK_apply]
  exact pairingBSymm_holds K ι n lam _ _

theorem hdualFr_triv {m : ℕ} (P : Matrix (Fin m) (Fin m) K) (M : Submodule (𝓞 K) (Fin m → K)) (x : Fin m → K) :
    x ∈ @hdualFr K _ m starRingOfComm P M ↔ P *ᵥ x ∈ dualFr M := by
  change (∀ y ∈ M, y ⬝ᵥ (P *ᵥ x) ∈ (1 : Submodule (𝓞 K) K)) ↔ ∀ y ∈ M, (P *ᵥ x) ⬝ᵥ y ∈ (1 : Submodule (𝓞 K) K)
  simp only [dotProduct_comm]

end Nabla

section Clauses

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] {ι C : Type} [Fintype ι] {n N : ℕ}
  (emb : ι → E →+* K) (lam : ι → DomWeight n) (R : ℝ) (J : Matrix (Fin n) (Fin n) E)
  (L : C → Submodule (𝓞 E) (Fin n → E)) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ)

end Clauses

end GlobalTheory.TestLat.Compare
