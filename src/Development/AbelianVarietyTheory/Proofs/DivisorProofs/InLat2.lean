module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertBigCell

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)}

def iotaW (hw : Formalism.UG.IsInertAt F E v w) : w.adicCompletion E →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) :=
  (GlobalTheory.InertLocField.liftT (E := E) v).toAddMonoidHom.comp
    (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm.toRingHom.toAddMonoidHom

def conjW (σ : E →ₐ[F] E) (hw : Formalism.UG.IsInertAt F E v w) : w.adicCompletion E →+* w.adicCompletion E :=
  (toCompl (under_eq_of_isInertAt hw)).comp
    ((sigR (Fv F v) σ).comp (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm.toRingHom)

def glueW (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι (w.adicCompletion E)) : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  (1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) • (1 : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + P.map (iotaW hw)

def InLat {K : Type} [Field K] (O : ValuationSubring K) {d : ℕ} (b : GL (Fin d) K) (u : Fin d → K) : Prop :=
  ∀ i, (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ u) i ∈ O

def InLat2 {K : Type} [Field K] (O : ValuationSubring K) {d : ℕ} (b : GL (Fin d) K) (z : Fin d ⊕ Fin d → K) : Prop :=
  InLat O b (z ∘ Sum.inl) ∧ InLat O b (z ∘ Sum.inr)

end GlobalTheory.InertBigCell
