module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefMapEmbeddingOfPositiveAtPlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrmOfPosDef
public import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction

@[expose] public section

open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.posDef_map_embedding_of_positiveAtPlace : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K), Formalism.L2.Rows.PosAt H v → (H.map v.embedding).PosDef := by
  first | exact @GlobalTheory.AmbTiePosDef.posDef_map_of_posAt | exact GlobalTheory.AmbTiePosDef.posDef_map_of_posAt | (intros; apply GlobalTheory.AmbTiePosDef.posDef_map_of_posAt <;> assumption)
