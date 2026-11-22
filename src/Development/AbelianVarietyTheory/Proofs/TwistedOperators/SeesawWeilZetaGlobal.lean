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

namespace GlobalTheory.FockThetaOnto

variable {D : D7}

def crd {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (hG : IsUnit G.det) (e : Fin k ≃ Fin d) :
    Matrix (Fin m) (Fin k) (AE D) ≃+ Matrix (Fin d) (Fin m) (AE D) where
  toFun u := HMul.hMul (uᵀ.submatrix e.symm id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G)
  invFun x := GlobalTheory.TripleRead.ptO G e x
  left_inv u := by
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G⁻¹ = (1 : Matrix (Fin m) (Fin m) (AE D)) := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hG, Matrix.map_one _ (map_zero _) (map_one _)]
    unfold GlobalTheory.TripleRead.ptO
    beta_reduce
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
    ext i j
    simp
  right_inv x := by
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G = (1 : Matrix (Fin m) (Fin m) (AE D)) := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hG, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : (GlobalTheory.TripleRead.ptO G e x)ᵀ.submatrix e.symm id = HMul.hMul x (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G⁻¹) := by
      ext i j
      simp [GlobalTheory.TripleRead.ptO]
    show HMul.hMul ((GlobalTheory.TripleRead.ptO G e x)ᵀ.submatrix e.symm id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G) = x
    rw [h2, Matrix.mul_assoc, h1, Matrix.mul_one]
  map_add' u v := by
    rw [← Matrix.add_mul]
    rfl

theorem exists_darbAlg_of_mem_algF (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ)
    (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin d ≃ Fin X.rank)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (hBs : Bs.IsGood D.sp.cm.sig) (hψ : Bs.ψ = ψ)
    (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
    (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix e e)
    (hV : Vs.IsHerm D.sp.cm.sig Bs r s) (hW : Ws.IsSkew D.sp.cm.sig Bs r' s')
    (hc : ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = conj (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = ((B.cart τ).submatrix e e).map conj)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws) (hM : M.IsGood Bs.ψ) (f : WO S X → ℂ) (hf : f ∈ algF ψ θ ε A B) :
    ∃ Φ ∈ GlobalTheory.TripleAssembly.darbAlg M Bs.ψ Bs.emb, GlobalTheory.TripleRead.thO M ψ (sgn ε S).gram e Φ = f := by
  have hG : IsUnit (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from (sgn ε S).gram).det :=
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit (sgn ε S)
  have hg : (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from (sgn ε S).gram) =
      (if ε then -1 else 1 : D.host.E) • S.gram := by
    cases ε
    · simp only [Bool.false_eq_true, if_false, one_smul]; rfl
    · simp only [if_true, neg_smul, one_smul]; exact neg_gram S
  obtain ⟨Φ, hΦ, hd⟩ := (GlobalTheory.T.algebraicVectors_correspond_schrodinger_thetaMap D ψ θ hθ ε S X A B e.symm Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hc M hM
    (crd (D := D) (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from (sgn ε S).gram) hG e)
    (fun u => by rw [← hg]; rfl)).1 f hf
  refine ⟨Φ, hΦ, funext fun x => ?_⟩
  have := hd.2 ((crd (D := D) (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from (sgn ε S).gram) hG e).symm x)
  rw [AddEquiv.apply_symm_apply] at this
  exact this

end GlobalTheory.FockThetaOnto

end
