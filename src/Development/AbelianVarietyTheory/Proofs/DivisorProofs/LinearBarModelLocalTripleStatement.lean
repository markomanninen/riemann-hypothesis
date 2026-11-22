module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarModelLocalTriple
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapNegApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_bar_model_local_triple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v)
    (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
    ∀ (f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl (incM F G.V'.J)),
      ((w : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    ∀ S : (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) → ℂ) →
        ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) → ℂ,
    (∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      S Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v)) →
    (∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      ∀ Φ' ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v), ∀ c : ℂ, S (c • Φ + Φ') = c • S Φ + S Φ') →
    (∀ u, At (evFin F v) u → ∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v u) Φ) =
        schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (actB (cA σ) w u)) (S Φ)) →
    ∃ c : ℂ, ∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      GlobalTheory.SwapSlice.sliceT ι (S Φ) = c • (GlobalTheory.SwapSlice.sliceT ι Φ ∘ GlobalTheory.SwapSlice.swapNeg) := by
  first | exact @GlobalTheory.SwapSchur.sliceT_swap_eq_smul | exact GlobalTheory.SwapSchur.sliceT_swap_eq_smul | (intros; apply GlobalTheory.SwapSchur.sliceT_swap_eq_smul <;> assumption)
