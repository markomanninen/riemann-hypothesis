module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormUnramifiedFactorization
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
theorem _root_.GlobalTheory.T.local_norm_unramified_factorization : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : Pl (F := F)) (τ : E →ₐ[F] Fv F v) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) (z - 1) →
    At (evFin F v) (Algebra.norm (AF F) z - 1) ∧ evFin F v (Algebra.norm (AF F) z) = piW τ z * piW (τ.comp σ) z := by
  first | exact @GlobalTheory.NormLocSplit.norm_at_split | exact GlobalTheory.NormLocSplit.norm_at_split | (intros; apply GlobalTheory.NormLocSplit.norm_at_split <;> assumption)
