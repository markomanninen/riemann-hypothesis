module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBetaOfDiscCocycle
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDiscMaps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeFrobeniusRationalColumns

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_beta_of_disc_cocycle_alt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (κ : ↥(GK K) → Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) (φε : ↥(GK K) → Matrix (Fin d) (Fin d) (Ainf l)) (H : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → IsUnit H → (∀ m : ℕ, ∃ (k : ℕ) (Λ : Matrix (Fin d) (Fin d) bk.S), (∀ a b, bk.E ∣ (Λ - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) a b) ∧ ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → ∀ a b, bk.iS bk.E ^ m ∣ (κ g * (Λ.map bk.iS).map G - Λ.map bk.iS) a b) → (∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → G (bk.iS (frobS l bk.a bk.E)) ^ N • (H.map i * (φε g).map bk.iA) = bk.iS (frobS l bk.a bk.E) ^ N • (κ g * (H.map i).map G)) → ∀ m : ℕ, ∃ (k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), (∀ a b, bk.E ∣ (β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) a b) ∧ ∀ (g : ↥(GK K)) a b, bk.ev bk.E ^ m ∣ (φε g * (β.map bk.ev).map (Per.σA (g : GQ l)) - β.map bk.ev) a b := by
  first | (exact @GlobalTheory.BKLim.exists_beta_of_disc_cocycle) | (exact GlobalTheory.BKLim.exists_beta_of_disc_cocycle) | (intros; apply GlobalTheory.BKLim.exists_beta_of_disc_cocycle  <;> assumption)
