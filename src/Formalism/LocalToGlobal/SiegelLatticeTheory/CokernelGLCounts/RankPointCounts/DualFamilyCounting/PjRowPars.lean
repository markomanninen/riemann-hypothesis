module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowParseval
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PjFrameRow

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcReal.JX
  Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.Pf.NcReal.JX.FR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rowParseval_holds : RowParseval := by
  intro D X u x y hx hy v
  set a := rv X.B.I v (X.crd x) with ha
  set b := rv X.B.I v (X.crd y) with hb
  have hbe : ∀ c, hJ (X.B.I.ε v) (eV X v c) b = 0 := by
    intro c
    show hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.eX c))) (rv X.B.I v (X.crd y)) = 0
    rw [Formalism.L2.SG.Pf.hJ_crd, (hy c).1]; simp
  have hbf : ∀ c, hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.fY c))) b = 0 := by
    intro c
    show hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.fY c))) (rv X.B.I v (X.crd y)) = 0
    rw [Formalism.L2.SG.Pf.hJ_crd, (hy c).2]; simp
  have hdec := decomp (nX X) (ProductExactness.Tw_pos u) (fX_ee X v) (LsNc5.fr_ff X v) (LsNc5.fr_ef X v) (fX_ww X u v) (fX_ew X u v)
    (LsNc5.fr_fw X u v) (LsNc5.fr_ez X u v) (LsNc5.fr_fz X u v) (LsNc5.frame_z_z_eq_neg_t X u v) (LsNc5.fr_zw X u v) b hbe hbf
  have hab : hJ (X.B.I.ε v) a b = ∑ c, hJ (X.B.I.ε v) a (X.wfr u v c) * star (hJ (X.B.I.ε v) b (X.wfr u v c)) +
      hJ (X.B.I.ε v) a (LsNc5.zV X u v) * star (hJ (X.B.I.ε v) b (LsNc5.zV X u v)) * (-(1 / ((Tw u : ℝ) : ℂ))) := by
    conv_lhs => rw [hdec]
    rw [fr_add_r, fr_sum_r, fr_smul_r]
    congr 1
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [fr_smul_r, hJ_swap (X.B.I.ε v) (X.wfr u v c) b, star_star]
      ring
    · rw [hJ_swap (X.B.I.ε v) (LsNc5.zV X u v) b, star_star]
      ring
  rw [← Formalism.L2.SG.Pf.hJ_crd, ← ha, ← hb, hab, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hj : (Fin.castSucc j).val < D.R.k := j.isLt
    simp only [rowV, gC, dif_pos hj, if_pos hj, mul_one]
    rfl
  · have hl : ¬ (Fin.last D.R.k).val < D.R.k := by simp
    simp only [rowV, gC, dif_neg hl, if_neg hl]
    rfl

end Formalism.L2.SG.Pf.NcReal.JX.CovB
