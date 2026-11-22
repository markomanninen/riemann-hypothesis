module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalInertiaIffMemPlaceInertia
public import Formalism.GaloisCohomology.LocalTateDualityK
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.MemSpanLIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.MemIntegralClosureIffMemBall
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.ExistsDen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.IsEquivAdicAbvNormAbv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.SpanLIsMaximal

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localInertia_iff_mem_placeInertia : ∀ (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p), (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
    ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p))
      (i : ↥(A.decompositionSubgroup F) ≃* (PadicAlgCl p ≃ₐ[↥K] PadicAlgCl p)),
      (∀ (g : ↥(A.decompositionSubgroup F)) (x : Ω), i g (j x) = j ((g : Ω ≃ₐ[F] Ω) x)) →
      ∀ g : ↥(A.decompositionSubgroup F), i g ∈ Formalism.GaloisCohomology.inertiaK p K ↔ (g : Ω ≃ₐ[F] Ω) ∈ Ine (F := F) A := by
  first | exact @GlobalTheory.DecInertia.inertiaK_iff_mem_Ine | exact GlobalTheory.DecInertia.inertiaK_iff_mem_Ine | (intros; apply GlobalTheory.DecInertia.inertiaK_iff_mem_Ine <;> assumption)
