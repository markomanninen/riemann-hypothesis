module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiKernelKillingElement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRFiltrationKerThetaGeneratorFacts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiSTmul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExtFixing

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bdR_element_normalized_killing_phi_kernel : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (σ : GQ l) (L : FinExt l) [FiniteDimensional ℚ_[l] ↥L.1] (a : ℕ), ∃ e : ↥L.1 ⊗[ℚ_[l]] P.R.BdR, phiS P σ L e = 1 ∧ ∀ x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR, PhiS P σ L a x = 0 → GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) e x = 0 := by
  first | (exact @GlobalTheory.HodgeAt.exists_idem_phiS_ker) | (exact GlobalTheory.HodgeAt.exists_idem_phiS_ker) | (intros; apply GlobalTheory.HodgeAt.exists_idem_phiS_ker  <;> assumption)
