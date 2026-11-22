module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientJacquetModuleSingleBlockSelf
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleTensorOfJacquetSubquotient
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSubquotient_jacquetModule_singleBlock_self : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (e : (Σ _ : Fin 1, Fin N) ≃ Fin N), IsSubquotient (piTensor fun _ : Fin 1 => π) (jac e π) := by
  first | exact @GlobalTheory.SingleBlockJac.isSubquotient_piTensor_jac | exact GlobalTheory.SingleBlockJac.isSubquotient_piTensor_jac | (intros; apply GlobalTheory.SingleBlockJac.isSubquotient_piTensor_jac <;> assumption)
