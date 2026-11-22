module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArchTranslatedSqrtWeightedFunGoodMirabolicTop
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WtOfLastRowOfDetPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archTranslatedSqrtWeightedFun_good_mirabolicTop : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (φ : GA E (m + 1) → ℂ),
    Continuous φ → (∀ γ g, φ (ratGL E (m + 1) γ * g) = φ g) →
    (∀ r, 0 < r → r ≤ m → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (m + 1) r m)) (fun x => φ (blkU x * g)) = 0) →
    ∀ Φ : (Fin (m + 1) → Cinf E) → ℂ, Continuous Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) →
    ∀ ψ : AddChar (Ad E) ℂ, Good ψ m (GlobalTheory.ZUnf.fT φ Φ) := by
  first | exact @GlobalTheory.ZUnf.good_fT | exact GlobalTheory.ZUnf.good_fT | (intros; apply GlobalTheory.ZUnf.good_fT <;> assumption)
