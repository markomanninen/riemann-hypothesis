module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralSiegelParabolicOfConjugateIdempote
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftVAlgebraMapMul

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralSiegelParabolic_of_conjugateIdempotent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (d : ℕ) (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ Eid : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), Eid * Eid = Eid → Eid + cA σ Eid = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) →
    Eid * cA σ Eid = 0 →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, (fun i => Eid * z i) ∈ GlobalTheory.InertSph.latAt W v) →
    ∃ s ∈ GlobalTheory.InertDbl.ParD σ W v,
      GlobalTheory.InertDbl.matD s * diagCols (Fin d) =
        diagCols (Fin d) * ((1 - (⅟2 : AF F) • Eid) • (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) ∧
      GlobalTheory.InertDbl.matD s * GlobalTheory.InertDbl.antiCols d =
        GlobalTheory.InertDbl.antiCols d * ((1 + cA σ Eid) • (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) := by
  first | exact @GlobalTheory.SplitConjPar.exists_par | exact GlobalTheory.SplitConjPar.exists_par | (intros; apply GlobalTheory.SplitConjPar.exists_par <;> assumption)
