module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExponentialImageContainsLattice
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualExponential_image_contains_lattice : ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), Lev l s → ∀ e : ℕ, ∀ α : Om l, α ∈ Ks K s → ‖α‖ ≤ 1 → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar D.loc (Gj K s) e z ((l : Om l) ^ (betaE l s e) * α) := by
  first | exact @GlobalTheory.ExpImage.expStar_image | exact GlobalTheory.ExpImage.expStar_image | (intros; apply GlobalTheory.ExpImage.expStar_image <;> assumption)
