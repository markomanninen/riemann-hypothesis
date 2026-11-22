module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocFrame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]


open Classical in
def pre (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : L := if h : ∃ x, ι x = z then h.choose else 0

theorem pre_spec (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (h : ∃ x, ι x = z) : ι (pre ι z) = z := by
  unfold pre
  rw [dite_eq_left h]
  exact h.choose_spec

def tJ (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {m n : Type} (J : Matrix m n E) : Matrix m n L :=
  fun i j => pre ι (ι 1 * inclR (F := F) (AF F) (J i j))

def gram (σL : L →+* L) (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {n : ℕ} (P : GL (Fin n) L) (J : Matrix (Fin n) (Fin n) E) :
    Matrix (Fin n) (Fin n) L :=
  (P : Matrix (Fin n) (Fin n) L)ᵀ * tJ ι J * (P : Matrix (Fin n) (Fin n) L).map σL

def xm (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {n d : ℕ} (PV : GL (Fin n) L) (PW : GL (Fin d) L) :
    Matrix (Fin d) (Fin n) L →+ Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) where
  toFun x := ((PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ).map ι
  map_zero' := by ext i j; simp
  map_add' x y := by ext i j; simp [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem xm_apply (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {n d : ℕ} (PV : GL (Fin n) L) (PW : GL (Fin d) L) (x : Matrix (Fin d) (Fin n) L) :
    xm ι PV PW x = ((PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ).map ι := rfl

end GlobalTheory.InertLocFrame

end
