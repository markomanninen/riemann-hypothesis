module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedTorsionClassTheoremGoodCase
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedTorsionClassTheorem_goodCase : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), admitted D HW F → Conclusion5 D → Conclusion4 D HW F := by
  first | exact @GlobalTheory.TheoremTB.tb_assembled | exact GlobalTheory.TheoremTB.tb_assembled | (intros; apply GlobalTheory.TheoremTB.tb_assembled <;> assumption)
