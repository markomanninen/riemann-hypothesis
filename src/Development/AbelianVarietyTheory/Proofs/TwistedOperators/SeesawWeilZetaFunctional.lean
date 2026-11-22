module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicVectorsCorrespondSchrodingerThetaMapStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.DarbImageRevB

variable {D : D7}

theorem incM_mul {m : ℕ} (G H : Matrix (Fin m) (Fin m) D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D := D) (G * H) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM H :=
  Matrix.map_mul

theorem incM_one {m : ℕ} : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D := D) (1 : Matrix (Fin m) (Fin m) D.host.E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

def crd {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (hG : IsUnit G.det) (e : Fin k ≃ Fin d) :
    Matrix (Fin m) (Fin k) (AE D) ≃+ Matrix (Fin d) (Fin m) (AE D) where
  toFun u := HMul.hMul (uᵀ.submatrix e.symm id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G)
  invFun x := GlobalTheory.TripleRead.ptO G e x
  left_inv u := by
    simp only [GlobalTheory.TripleRead.ptO]
    rw [Matrix.mul_assoc, ← incM_mul, Matrix.mul_nonsing_inv _ hG, incM_one, Matrix.mul_one]
    ext i j
    simp
  right_inv x := by
    have e1 : ((GlobalTheory.TripleRead.ptO G e x)ᵀ.submatrix e.symm id) = HMul.hMul x (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G⁻¹) := by
      ext i j
      simp [GlobalTheory.TripleRead.ptO]
    simp only [e1]
    rw [Matrix.mul_assoc, ← incM_mul, Matrix.nonsing_inv_mul _ hG, incM_one, Matrix.mul_one]
  map_add' u v := by
    rw [← Matrix.add_mul]
    rfl

end GlobalTheory.DarbImageRevB

end
