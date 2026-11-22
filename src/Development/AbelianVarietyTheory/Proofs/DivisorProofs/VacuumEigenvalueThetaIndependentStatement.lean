module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumEigenvalueThetaIndependent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks

@[expose] public section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_eigenvalue_theta_independent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (θ θ' : 𝓞 E), (θ : E) + σ θ = 1 → (θ' : E) + σ θ' = 1 → ∀ γ ∈ latAtV X W v,
      B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) γ γ) =
        B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ' : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) γ γ) := by
  first | exact @GlobalTheory.VacThetaIndep.vacuum_character_theta_indep | exact GlobalTheory.VacThetaIndep.vacuum_character_theta_indep | (intros; apply GlobalTheory.VacThetaIndep.vacuum_character_theta_indep <;> assumption)
