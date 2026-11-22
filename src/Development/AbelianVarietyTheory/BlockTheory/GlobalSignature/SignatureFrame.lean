module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalRingCardinality.DataCD

@[expose] public section

open MeasureTheory Matrix Finset

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SignatureFrame

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

structure SignFrame {n : ℕ} (ε : Fin n → Bool) (P Q : ℕ) where

  e : Fin P ⊕ Fin Q ≃ Fin n
  pos : ∀ i, ε (e (Sum.inl i)) = true
  neg : ∀ j, ε (e (Sum.inr j)) = false

variable {n P Q : ℕ} {ε : Fin n → Bool}

theorem SignFrame.reindex_J (F : SignFrame ε P Q) :
    Matrix.reindex F.e F.e (Formalism.UG.Jpq P Q) = Jm ε := by
  ext a b
  obtain ⟨x, rfl⟩ := F.e.surjective a
  obtain ⟨y, rfl⟩ := F.e.surjective b
  rcases x with x | x <;> rcases y with y | y <;>
    simp [Formalism.UG.Jpq, Jm, Matrix.diagonal_apply, Matrix.one_apply, F.pos, F.neg]
  split_ifs <;> simp

def SignFrame.unitsMap (F : SignFrame ε P Q) :
    GL (Fin P ⊕ Fin Q) ℂ →* (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  Units.map (Matrix.reindexAlgEquiv ℂ ℂ F.e).toMulEquiv.toMonoidHom

theorem SignFrame.inUJ_reindex (F : SignFrame ε P Q)
    (m : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    inUJ ε (Matrix.reindex F.e F.e m) ↔
      Formalism.UG.cT (starRingEnd ℂ) m * Formalism.UG.Jpq P Q * m = Formalism.UG.Jpq P Q := by
  unfold inUJ
  rw [← F.reindex_J]
  have h : Formalism.UG.cT (starRingEnd ℂ) m = mᴴ := by
    ext i j; simp [Formalism.UG.cT]
  rw [h]
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  exact (Matrix.reindex F.e F.e).injective.eq_iff (a := mᴴ * Formalism.UG.Jpq P Q * m) (b := Formalism.UG.Jpq P Q)

def SignFrame.toDiag (F : SignFrame ε P Q) (g : UpqT P Q) : UJ ε :=
  let g' : Formalism.UG.Upq P Q := g
  ⟨F.unitsMap g'.1, (F.inUJ_reindex _).2 g'.2⟩

def cdMeasure (c : CDHaar) (F : SignFrame ε P Q) : Measure (UJ ε) :=
  Measure.map F.toDiag (c.cd P Q)

def dimV {n : ℕ} (lam : Fin n → ℝ) : ℝ :=
  (∏ a : Fin n, ∏ b ∈ Ioi a, (lam a - lam b)) /
    ∏ a : Fin n, ∏ b ∈ Ioi a, (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))

end GlobalTheory.IndefiniteRowSideFullHecke.SignatureFrame
