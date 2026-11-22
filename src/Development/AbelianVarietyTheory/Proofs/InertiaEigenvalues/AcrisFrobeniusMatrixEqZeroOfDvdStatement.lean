module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisFrobeniusMatrixEqZeroOfDvd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_frobenius_matrix_eq_zero_of_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d c : ℕ) (D₀ F F' : Matrix (Fin d) (Fin d) (Per.Acris l)), (∀ i j, ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ∣ D₀ i j) → (l : Per.Acris l) ^ c • D₀ = F * D₀.map (phiA l) * F' → D₀ = 0 := by
  first | exact @GlobalTheory.BKLim.acris_frob_eq_zero | exact GlobalTheory.BKLim.acris_frob_eq_zero | (intros; apply GlobalTheory.BKLim.acris_frob_eq_zero <;> assumption)
