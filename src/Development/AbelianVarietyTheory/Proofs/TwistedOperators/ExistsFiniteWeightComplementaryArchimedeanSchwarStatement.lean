module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteWeightComplementaryArchimedeanSchwar
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteWeight_complementary_archimedeanSchwartz : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ R : (κ → AF F) → ℂ, R 0 ≠ 0 ∧ ∀ f : SInf F κ, Rest (evI F) (⇑f) R := by
  first | exact @GlobalTheory.ArchRest.exists_rest_arch | exact GlobalTheory.ArchRest.exists_rest_arch | (intros; apply GlobalTheory.ArchRest.exists_rest_arch <;> assumption)
