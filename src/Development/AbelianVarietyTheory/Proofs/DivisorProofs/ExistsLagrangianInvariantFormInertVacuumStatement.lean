module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianInvariantFormInertVacuum
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lagrangian_invariantForm_inertVacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∃ (C : Matrix (Fin (a + a')) (Fin ((a + a') / 2)) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ),
      GlobalTheory.InertVacLag.IsLagrAt σ G.W v C ∧ GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l ∧ l (G.M'.vac v) ≠ 0 := by
  first | exact @GlobalTheory.InertVacLagP.exists_lagr_inv_vac | exact GlobalTheory.InertVacLagP.exists_lagr_inv_vac | (intros; apply GlobalTheory.InertVacLagP.exists_lagr_inv_vac <;> assumption)
