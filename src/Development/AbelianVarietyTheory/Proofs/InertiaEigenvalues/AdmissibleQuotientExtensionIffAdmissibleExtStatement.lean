module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientExtensionIffAdmissibleExt
public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientKerIffFullLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopDataOfSlotHyps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDim
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete

@[expose] public section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_quotientExtension_iff_admissible_ext : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) (jT : ZMod S.n → ℤ → ℤ),
    (∀ i a, ((S.D.Ut i).count a : ℤ) = jT i a) →
    ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (L : Lattice (O := S.O) T.ρ) (X : Type) [AddCommGroup X] [Module S.O X]
      (z : S.G → ↥L.T ⊗[S.O] X) (hz : z ∈ Z1 (twCoef (latRep L) S.Γ.χ₁ X) ⊤) (a : ℕ)
      (ha : ∀ x : X, S.Γ.lam ^ a • x = 0),
      (tableLineDegreeTwo.AdmQ (P.PD S.K) S.emb S.Γ.lam jT (tableLineDegreeTwo.resPoly S.Γ.T₀.ρ S.Γ.chi S.D.t) (tableLineDegreeTwo.actExt L X S.Γ.χ₁ z)
                         (tableLineDegreeTwo.kerExt L X S.Γ.lam a) ↔ S.admitted (Ea (latRep L) S.Γ.χ₁ ha ⟨z, hz⟩)) := by
  first | exact @GlobalTheory.AdmQuotExt.admissible_quotientExtension_iff_admissible_ext' | exact GlobalTheory.AdmQuotExt.admissible_quotientExtension_iff_admissible_ext' | (intros; apply GlobalTheory.AdmQuotExt.admissible_quotientExtension_iff_admissible_ext' <;> assumption)
