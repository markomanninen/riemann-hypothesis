module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryElementActsLocalOperatorAtPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledUnitaryElement_acts_localOperatorAtPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a'), B.IsGood σ →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a'))))
      (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J)) →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
      IsUSplitting (adeleClass F) B.ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd →
    ∀ (v : Pl (F := F)) (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))),
      At (evFin F v) (((p : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) →
    ∀ φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v), ∃ φ₁ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      Acts (evFin F v) (omd p) φ φ₁ := by
  first | exact @GlobalTheory.DblActs.dbl_acts | exact GlobalTheory.DblActs.dbl_acts | (intros; apply GlobalTheory.DblActs.dbl_acts <;> assumption)
