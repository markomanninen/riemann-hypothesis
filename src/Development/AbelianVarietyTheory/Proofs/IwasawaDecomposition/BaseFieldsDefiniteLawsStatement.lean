module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
public import Formalism.LocalToGlobal.Columns.BaseLemmas

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_fields_definite_laws : ∀ B : Base, B.fields.AbelianUnramifiedExtensionConditions ∧ B.fields.f = B.R.f := by
  first | exact @GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws | exact GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws | (intros; apply GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws <;> assumption)
