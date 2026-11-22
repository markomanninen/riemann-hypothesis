module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLow
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FmSmulLeft
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt
open scoped ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

open Classical

section forms

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
  (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter)

theorem formC_zero_l (y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hy : PBL.CV (p.T.bs j) y) : p.form j hj w 0 y = 0 := by
  have h := PBL.form_slC p j hj w 0 0 y 1 PBL.cv_zero PBL.cv_zero hy
  simp only [one_smul, add_zero, one_mul] at h
  linear_combination -h

theorem formC_zero_r (x : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hx : PBL.CV (p.T.bs j) x) : p.form j hj w x 0 = 0 := by
  have h := PBL.form_srC p j hj w x 0 0 1 hx PBL.cv_zero PBL.cv_zero
  simp only [one_smul, add_zero, map_one, one_mul] at h
  linear_combination -h

theorem formC_smul_l (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : PBL.CV (p.T.bs j) x) (hy : PBL.CV (p.T.bs j) y) : p.form j hj w (c • x) y = c * p.form j hj w x y := by
  have h := PBL.form_slC p j hj w 0 x y c PBL.cv_zero hx hy
  rwa [zero_add, formC_zero_l p j hj w y hy, zero_add] at h

theorem formC_smul_r (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : PBL.CV (p.T.bs j) x) (hy : PBL.CV (p.T.bs j) y) : p.form j hj w x (c • y) = conj c * p.form j hj w x y := by
  have h := PBL.form_srC p j hj w x 0 y c hx PBL.cv_zero hy
  rwa [zero_add, formC_zero_r p j hj w x hx, zero_add] at h

end forms

end

end Formalism.FourierDecayAlt.P.CutBP
