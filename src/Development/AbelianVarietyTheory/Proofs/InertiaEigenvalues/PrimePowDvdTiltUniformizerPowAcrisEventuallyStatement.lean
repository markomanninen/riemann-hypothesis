module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowDvdTiltUniformizerPowAcrisEventually
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primePow_dvd_tiltUniformizer_pow_acris_eventually : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (c M : ℕ), ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → (l : Per.Acris l) ^ (c * n + M) ∣ ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ^ (l ^ n - 1) := by
  first | exact @GlobalTheory.AcrisPow.main | exact GlobalTheory.AcrisPow.main | (intros; apply GlobalTheory.AcrisPow.main <;> assumption)
