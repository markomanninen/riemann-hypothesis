module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormCompLocalWeilOperator
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupVStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergInvariantForm_comp_localWeilOperator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (m : ℕ) (C : Matrix (Fin (a + a')) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    ∀ l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l →
    ∀ g ∈ UAt σ G.V' (evFin F v),
    ∀ S : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin a' × Fin (a + a') → Fv F v) → ℂ),
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S φ ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧
        Acts (evFin F v) (om' (g, 1)) φ (S φ)) →
      GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C (l ∘ₗ S) := by
  first | exact @GlobalTheory.InertVacEquiv.heisInv_comp | exact GlobalTheory.InertVacEquiv.heisInv_comp | (intros; apply GlobalTheory.InertVacEquiv.heisInv_comp <;> assumption)
