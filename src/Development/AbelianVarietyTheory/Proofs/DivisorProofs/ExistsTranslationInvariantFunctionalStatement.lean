module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantFunctional
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruh
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFormBox

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translation_invariant_functional : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (n d : ℕ), ∃ Λ : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) →ₗ[ℂ] ℂ,
    (∀ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), ∀ a, Λ (fun Y => f (Y + a)) = Λ f) ∧
      ∃ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), Λ f ≠ 0 := by
  first | exact @GlobalTheory.HaarSB.exists_invariant_form_matrix | exact GlobalTheory.HaarSB.exists_invariant_form_matrix | (intros; apply GlobalTheory.HaarSB.exists_invariant_form_matrix <;> assumption)
